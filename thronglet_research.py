"""Persistent local research archive for Thronglet."""
import json
import sqlite3
from contextlib import contextmanager
import threading
import time
from pathlib import Path


class ResearchArchive:
    def __init__(self, path="thronglet_archive.sqlite3"):
        self.path = Path(path)
        self.lock = threading.RLock()
        with self.lock, self._db() as db:
            db.executescript("""
            PRAGMA journal_mode=WAL;
            CREATE TABLE IF NOT EXISTS conversations(
              id INTEGER PRIMARY KEY, cycle INTEGER, timestamp REAL,
              sender TEXT, receiver TEXT, symbol TEXT, context TEXT,
              interpretation TEXT, confidence REAL, understood INTEGER);
            CREATE INDEX IF NOT EXISTS conversations_cycle ON conversations(cycle);
            CREATE TABLE IF NOT EXISTS words(
              id INTEGER PRIMARY KEY, cycle INTEGER, timestamp REAL,
              word TEXT, organism TEXT, action TEXT, interpretation TEXT);
            CREATE INDEX IF NOT EXISTS words_name ON words(word);
            CREATE TABLE IF NOT EXISTS organisms(
              id TEXT PRIMARY KEY, first_seen INTEGER, last_seen INTEGER,
              generation INTEGER, status TEXT, profile TEXT);
            """)

    @contextmanager
    def _db(self):
        db = sqlite3.connect(str(self.path), timeout=10)
        db.row_factory = sqlite3.Row
        try:
            yield db
            db.commit()
        except Exception:
            db.rollback()
            raise
        finally:
            db.close()

    def record_conversation(self, cycle, sender, receiver, symbol, context,
                            interpretation=None, confidence=0.0, understood=False):
        with self.lock, self._db() as db:
            db.execute("INSERT INTO conversations(cycle,timestamp,sender,receiver,symbol,context,interpretation,confidence,understood) VALUES(?,?,?,?,?,?,?,?,?)",
                (cycle,time.time(),sender,receiver,symbol,json.dumps(context),interpretation,float(confidence),int(bool(understood))))

    def record_word(self, cycle, word, organism, action, interpretation=None):
        with self.lock, self._db() as db:
            db.execute("INSERT INTO words(cycle,timestamp,word,organism,action,interpretation) VALUES(?,?,?,?,?,?)",
                (cycle,time.time(),word,organism,action,interpretation))

    def sync(self, cycle, population, previous):
        active=set()
        with self.lock, self._db() as db:
            for e in population:
                active.add(e.entity_id)
                profile={"id":e.entity_id,"age":e.age,"energy":round(e.energy,2),
                    "position":[e.x,e.y],"words":dict(e.lexicon),"concepts":len(e.concepts),
                    "programs":list(e.learned_programs),"language_stats":dict(e.language_stats),
                    "program_stats":dict(e.program_stats),"context_associations":e.context_associations,
                    "memories":list(e.cultural_memory)[-20:]}
                row=db.execute("SELECT first_seen FROM organisms WHERE id=?",(e.entity_id,)).fetchone()
                first=row["first_seen"] if row else cycle
                db.execute("""INSERT INTO organisms VALUES(?,?,?,?,?,?)
                    ON CONFLICT(id) DO UPDATE SET last_seen=excluded.last_seen,status='alive',profile=excluded.profile""",
                    (e.entity_id,first,cycle,e.generation,"alive",json.dumps(profile)))
                old=previous.get(e.entity_id,{})
                current=dict(e.lexicon)
                for word in current.keys()-old.keys():
                    db.execute("INSERT INTO words(cycle,timestamp,word,organism,action) VALUES(?,?,?,?,?)",
                        (cycle,time.time(),word,e.entity_id,"adopted" if e.generation > 0 else "first-observed"))
                for word in current.keys() & old.keys():
                    if current[word] != old[word]:
                        db.execute("INSERT INTO words(cycle,timestamp,word,organism,action) VALUES(?,?,?,?,?)",
                            (cycle,time.time(),word,e.entity_id,"meaning-change"))
                previous[e.entity_id]=current
            for row in db.execute("SELECT id,profile FROM organisms WHERE status='alive'").fetchall():
                if row["id"] not in active:
                    db.execute("UPDATE organisms SET status='deceased' WHERE id=?",(row["id"],))

    def summary(self):
        with self.lock, self._db() as db:
            def count(sql): return db.execute(sql).fetchone()[0]
            total=count("SELECT COUNT(*) FROM conversations")
            understood=count("SELECT COUNT(*) FROM conversations WHERE understood=1")
            return {"conversations":total,"understood":understood,
                "success_rate":round(100*understood/total,1) if total else 0,
                "words":count("SELECT COUNT(DISTINCT word) FROM words"),
                "organisms":count("SELECT COUNT(*) FROM organisms"),
                "alive":count("SELECT COUNT(*) FROM organisms WHERE status='alive'"),
                "deceased":count("SELECT COUNT(*) FROM organisms WHERE status='deceased'"),
                "adoptions":count("SELECT COUNT(*) FROM words WHERE action='adopted'"),
                "meaning_changes":count("SELECT COUNT(*) FROM words WHERE action='meaning-change'")}

    def conversations(self,q="",limit=100):
        sql="SELECT * FROM conversations"; args=[]
        if q:
            sql+=" WHERE symbol LIKE ? OR sender LIKE ? OR receiver LIKE ? OR interpretation LIKE ? OR context LIKE ?"
            args=[f"%{q}%"]*5
        sql+=" ORDER BY id DESC LIMIT ?"; args.append(max(1,min(int(limit),500)))
        with self.lock, self._db() as db:
            return [{"id":r["id"],"cycle":r["cycle"],"sender":r["sender"],"receiver":r["receiver"],
                "symbol":r["symbol"],"context":json.loads(r["context"]),"interpretation":r["interpretation"],
                "confidence":r["confidence"],"understood":bool(r["understood"])}
                for r in db.execute(sql,args).fetchall()]

    def words(self,q="",limit=200):
        sql="SELECT word,COUNT(*) events,COUNT(DISTINCT organism) speakers,MAX(cycle) last_cycle FROM words"
        args=[]
        if q: sql+=" WHERE word LIKE ?"; args.append(f"%{q}%")
        sql+=" GROUP BY word ORDER BY speakers DESC,events DESC LIMIT ?"; args.append(max(1,min(int(limit),500)))
        with self.lock, self._db() as db:
            result=[]
            for row in db.execute(sql,args).fetchall():
                item=dict(row)
                item["history"]=[
                    {"cycle":h["cycle"],"organism":h["organism"],
                     "action":h["action"],"interpretation":h["interpretation"]}
                    for h in db.execute(
                        "SELECT cycle,organism,action,interpretation FROM words WHERE word=? ORDER BY id ASC LIMIT 100",
                        (item["word"],),
                    ).fetchall()
                ]
                result.append(item)
            return result

    def organisms(self,q="",limit=300):
        sql="SELECT * FROM organisms"; args=[]
        if q: sql+=" WHERE id LIKE ?"; args.append(f"%{q}%")
        sql+=" ORDER BY last_seen DESC LIMIT ?"; args.append(max(1,min(int(limit),500)))
        with self.lock, self._db() as db:
            return [self._profile(r) for r in db.execute(sql,args).fetchall()]

    def organism(self,oid):
        with self.lock, self._db() as db:
            row=db.execute("SELECT * FROM organisms WHERE id=?",(oid,)).fetchone()
            if not row:return None
            profile=self._profile(row)
            profile["conversations"]=self.conversations_for(db,oid)
            return profile

    def conversations_for(self,db,oid):
        return [{"cycle":r["cycle"],"sender":r["sender"],"receiver":r["receiver"],
            "symbol":r["symbol"],"context":json.loads(r["context"]),
            "interpretation":r["interpretation"],"understood":bool(r["understood"])}
            for r in db.execute("SELECT * FROM conversations WHERE sender=? OR receiver=? ORDER BY id DESC LIMIT 100",(oid,oid)).fetchall()]

    @staticmethod
    def _profile(row):
        p=json.loads(row["profile"])
        p.update({"id":row["id"],"first_seen":row["first_seen"],"last_seen":row["last_seen"],
            "generation":row["generation"],"status":row["status"]})
        return p


DASHBOARD_HTML = r"""<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Thronglet / Research</title>
<style>
:root{color-scheme:dark;--bg:#090c10;--panel:#121820;--line:#26313d;--text:#e8edf4;--muted:#8997a6;--blue:#a8c8f5;--green:#91d6b0}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--text);font:14px/1.5 -apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}main{max-width:1440px;margin:auto;padding:28px 22px}header{display:flex;justify-content:space-between;gap:20px;margin-bottom:24px}h1{font-size:24px;letter-spacing:-.04em;margin:0}h2{font-size:13px;margin:0 0 12px}.muted,.sub{color:var(--muted)}.sub{font-size:13px;margin-top:4px}.status{color:var(--green);font-size:12px}
.metrics{display:grid;grid-template-columns:repeat(6,1fr);gap:9px;margin-bottom:18px}.metric,.panel{background:var(--panel);border:1px solid var(--line);border-radius:9px}.metric{padding:13px}.label{font-size:10px;color:var(--muted);text-transform:uppercase;letter-spacing:.08em}.value{font-size:23px;font-weight:650;margin-top:3px}
.tabs{display:flex;gap:4px;border-bottom:1px solid var(--line);margin-bottom:14px;overflow:auto}.tab{background:none;border:0;border-bottom:2px solid transparent;color:var(--muted);padding:10px 13px;white-space:nowrap}.tab[aria-selected=true]{color:var(--text);border-color:var(--blue)}
.toolbar{margin:0 0 12px}.search{width:min(440px,100%);padding:9px 11px;background:var(--panel);border:1px solid var(--line);border-radius:7px;color:var(--text)}.panel{padding:15px;margin-bottom:12px;min-width:0}.split{display:grid;grid-template-columns:1.5fr 1fr;gap:12px}.list{display:grid}.item{padding:11px 0;border-bottom:1px solid var(--line)}.item:last-child{border:0}.meta{font-size:11px;color:var(--muted);margin-top:3px}.itembody{margin-top:6px;overflow-wrap:anywhere}code{font-family:ui-monospace,Menlo,monospace;color:var(--blue)}table{width:100%;border-collapse:collapse}th,td{text-align:left;padding:9px 7px;border-bottom:1px solid var(--line);font-size:12px}th{font-size:10px;color:var(--muted);text-transform:uppercase;letter-spacing:.07em}.link{background:none;border:0;color:var(--blue);padding:0}.pill{display:inline-block;background:#1b2631;border-radius:20px;padding:2px 7px;font-size:10px;color:var(--muted);margin:2px}.good{color:var(--green)}.empty{text-align:center;padding:28px;color:var(--muted)}.hidden{display:none!important}.bars{display:grid;gap:10px}.bar{display:grid;grid-template-columns:90px 1fr 30px;gap:9px;align-items:center;font-size:12px}.track{height:6px;background:#27313c;border-radius:8px}.fill{height:6px;background:#91afd8;border-radius:8px}.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:8px}.stat{background:#1a222b;border-radius:7px;padding:10px}.stat strong{display:block;font-size:18px}.stat span{font-size:10px;color:var(--muted);text-transform:uppercase}
@media(max-width:950px){.metrics{grid-template-columns:repeat(3,1fr)}.split{grid-template-columns:1fr}}@media(max-width:600px){main{padding:18px 12px}.metrics{grid-template-columns:repeat(2,1fr)}header{display:block}.status{margin-top:10px}.stats{grid-template-columns:repeat(2,1fr)}th:nth-child(n+4),td:nth-child(n+4){display:none}}
</style></head><body><main>
<header><div><h1>Thronglet <span class="muted">/ Research</span></h1><div class="sub">An observational record of an evolving artificial-life simulation.</div></div><div class="status" id="status">Connecting to local simulation</div></header>
<section class="metrics"><div class="metric"><div class="label">Conversations</div><div class="value" id="m-conversations">—</div></div><div class="metric"><div class="label">Interpretation rate</div><div class="value" id="m-success">—</div></div><div class="metric"><div class="label">Tracked words</div><div class="value" id="m-words">—</div></div><div class="metric"><div class="label">Organisms recorded</div><div class="value" id="m-organisms">—</div></div><div class="metric"><div class="label">Word adoptions</div><div class="value" id="m-adoptions">—</div></div><div class="metric"><div class="label">Deceased profiles</div><div class="value" id="m-deceased">—</div></div></section>
<nav class="tabs"><button class="tab" data-tab="overview" aria-selected="true">Overview</button><button class="tab" data-tab="conversations" aria-selected="false">Conversations</button><button class="tab" data-tab="dictionary" aria-selected="false">Living dictionary</button><button class="tab" data-tab="organisms" aria-selected="false">Organisms</button><button class="tab" data-tab="analytics" aria-selected="false">Analytics</button></nav>
<div class="toolbar"><input id="search" class="search" type="search" placeholder="Search symbols, organisms, interpretations…"></div>
<section id="overview" class="view"><div class="split"><div class="panel"><h2>Recent exchanges</h2><div id="recent" class="list"></div></div><div class="panel"><h2>Most widely shared symbols</h2><div id="topwords" class="bars"></div></div></div><div class="panel"><h2>Living population</h2><div id="population"></div></div></section>
<section id="conversations" class="view hidden"><div class="panel"><h2>Persistent conversation archive</h2><div id="allconversations" class="list"></div></div></section>
<section id="dictionary" class="view hidden"><div class="panel"><h2>Word origins and adoption</h2><div id="allwords"></div></div></section>
<section id="organisms" class="view hidden"><div class="panel"><h2>Organism registry</h2><div id="allorganisms"></div></div><div id="profile" class="panel hidden"></div></section>
<section id="analytics" class="view hidden"><div class="panel"><h2>Language and communication</h2><div id="analyticstats" class="stats"></div><p class="meta">The archive records transmitted symbols, observable context and receiver-side interpretations. It does not expose a sender’s private concept labels. An interpretation is a hypothesis, not proof of shared meaning.</p></div><div class="panel"><h2>Vocabulary distribution</h2><div id="distribution" class="bars"></div></div></section>
</main><script>
const el=id=>document.getElementById(id);let tab="overview",state=null,timer=null;
const esc=v=>String(v??"").replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const num=v=>Number(v||0).toLocaleString();
async function get(path){const r=await fetch(path,{cache:"no-store"});if(!r.ok)throw Error(r.status);return r.json()}
function empty(t){return '<div class="empty">'+esc(t)+'</div>'}
function convo(c){return '<article class="item"><strong><code>'+esc(c.symbol)+'</code> · C'+num(c.cycle)+'</strong><span class="'+(c.understood?'good':'muted')+'"> · '+(c.understood?'Interpreted':'Uncertain')+'</span><div class="meta">'+esc(c.sender)+' → '+esc(c.receiver)+' · confidence '+Math.round((c.confidence||0)*100)+'%</div><div class="itembody">'+(c.interpretation?'Receiver hypothesis: '+esc(c.interpretation):'No stable interpretation recorded')+'</div><div class="meta">Context: '+esc(JSON.stringify(c.context))+'</div></article>'}
function bars(rows){if(!rows.length)return empty('No vocabulary history yet.');const max=Math.max(1,...rows.map(x=>x.speakers||0));return rows.map(x=>'<div class="bar"><code>'+esc(x.word)+'</code><div class="track"><div class="fill" style="width:'+(100*x.speakers/max)+'%"></div></div><span>'+x.speakers+'</span></div>').join('')}
document.querySelectorAll('.tab').forEach(b=>b.onclick=()=>{tab=b.dataset.tab;document.querySelectorAll('.tab').forEach(x=>x.setAttribute('aria-selected',String(x===b)));document.querySelectorAll('.view').forEach(x=>x.classList.toggle('hidden',x.id!==tab));render()});
el('search').oninput=()=>{clearTimeout(timer);timer=setTimeout(render,180)};
async function render(){const q=encodeURIComponent(el('search').value.trim());try{
if(tab==='overview'){const [cs,ws]=await Promise.all([get('/api/research/conversations?limit=12'),get('/api/research/words?limit=10')]);el('recent').innerHTML=cs.length?cs.map(convo).join(''):empty('No exchanges recorded yet.');el('topwords').innerHTML=bars(ws);if(state)el('population').innerHTML='<table><thead><tr><th>Organism</th><th>Gen</th><th>Age</th><th>Energy</th><th>Words</th><th>Messages</th></tr></thead><tbody>'+state.entities.map(e=>'<tr><td><button class="link" data-id="'+esc(e.id)+'">'+esc(e.id)+'</button></td><td>'+e.generation+'</td><td>'+e.age+'</td><td>'+e.energy.toFixed(1)+'</td><td>'+e.words+'</td><td>'+e.messages+'</td></tr>').join('')+'</tbody></table>'}
if(tab==='conversations'){const a=await get('/api/research/conversations?limit=300&q='+q);el('allconversations').innerHTML=a.length?a.map(convo).join(''):empty('No matching conversations.')}
if(tab==='dictionary'){const a=await get('/api/research/words?limit=300&q='+q);el('allwords').innerHTML=a.length?'<table><thead><tr><th>Symbol</th><th>Speakers</th><th>Events</th><th>Last seen</th><th>Origins / changes</th></tr></thead><tbody>'+a.map(w=>'<tr><td><code>'+esc(w.word)+'</code></td><td>'+w.speakers+'</td><td>'+w.events+'</td><td>C'+w.last_cycle+'</td><td>'+w.history.map(h=>'<span class="pill">'+esc(h.action)+' · '+esc(h.organism)+'</span>').join(' ')+'</td></tr>').join('')+'</tbody></table>':empty('No matching symbols.')}
if(tab==='organisms'){const a=await get('/api/research/organisms?limit=300&q='+q);el('allorganisms').innerHTML=a.length?'<table><thead><tr><th>Organism</th><th>Status</th><th>Generation</th><th>First seen</th><th>Last seen</th><th>Vocabulary</th></tr></thead><tbody>'+a.map(o=>'<tr><td><button class="link" data-id="'+esc(o.id)+'">'+esc(o.id)+'</button></td><td>'+esc(o.status)+'</td><td>'+o.generation+'</td><td>C'+o.first_seen+'</td><td>C'+o.last_seen+'</td><td>'+Object.keys(o.words||{}).length+'</td></tr>').join('')+'</tbody></table>':empty('No profiles found.')}
if(tab==='analytics'){const [s,w]=await Promise.all([get('/api/research/summary'),get('/api/research/words?limit=15')]);el('analyticstats').innerHTML=[['Exchanges',s.conversations],['Known mappings',s.understood],['Mapping rate',s.success_rate+'%'],['Word adoptions',s.adoptions],['Meaning changes',s.meaning_changes],['Deceased',s.deceased]].map(x=>'<div class="stat"><strong>'+num(x[1])+'</strong><span>'+x[0]+'</span></div>').join('');el('distribution').innerHTML=bars(w)}
}catch(e){console.error(e);el('status').textContent='Archive unavailable'}}
document.addEventListener('click',async e=>{const b=e.target.closest('[data-id]');if(!b)return;try{const p=await get('/api/research/organism?id='+encodeURIComponent(b.dataset.id));el('profile').classList.remove('hidden');el('profile').innerHTML='<h2>'+esc(p.id)+' · '+esc(p.status)+'</h2><div class="stats"><div class="stat"><strong>'+p.age+'</strong><span>Age at last record</span></div><div class="stat"><strong>'+p.concepts+'</strong><span>Concepts</span></div><div class="stat"><strong>'+Object.keys(p.words||{}).length+'</strong><span>Words</span></div><div class="stat"><strong>'+(p.programs||[]).length+'</strong><span>Programs</span></div></div><p class="meta">First seen C'+p.first_seen+' · last seen C'+p.last_seen+' · energy '+p.energy+' · last position '+esc(JSON.stringify(p.position))+'</p><h2>Vocabulary</h2><div>'+Object.keys(p.words||{}).map(w=>'<span class="pill">'+esc(w)+'</span>').join('')+'</div><h2 style="margin-top:16px">Communication</h2><p class="meta">Sent '+num(p.language_stats?.messages_sent)+' · received '+num(p.language_stats?.messages_received)+' · known mappings '+num(p.language_stats?.successful_interpretations)+' · uncertain interpretations '+num(p.language_stats?.failed_interpretations)+'</p><h2 style="margin-top:16px">Learned programs</h2><div>'+((p.programs||[]).map(w=>'<span class="pill">'+esc(w)+'</span>').join(''))+'</div><h2 style="margin-top:16px">Recent memories</h2><div class="list">'+((p.memories||[]).slice(-12).reverse().map(x=>'<div class="item"><strong>'+esc(x.kind||'memory')+'</strong><div class="meta">Cycle '+esc(x.cycle??'—')+' · '+esc(x.word||x.value||'')+'</div></div>').join('')||empty('No memories recorded.'))+'</div><h2 style="margin-top:16px">Recent exchanges</h2>'+((p.conversations||[]).map(convo).join('')||empty('No exchanges recorded.'))}catch(e){console.error(e)}});
async function refresh(){try{state=await get('/api/state');const s=await get('/api/research/summary');el('status').textContent=state.running?'● Simulation running':'Simulation paused';el('m-conversations').textContent=num(s.conversations);el('m-success').textContent=s.success_rate+'%';el('m-words').textContent=num(s.words);el('m-organisms').textContent=num(s.organisms);el('m-adoptions').textContent=num(s.adoptions);el('m-deceased').textContent=num(s.deceased);if(tab==='overview')render()}catch(e){el('status').textContent='Waiting for local simulation'}}setInterval(refresh,1800);refresh();
</script></body></html>"""
