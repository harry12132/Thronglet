import tempfile
import unittest
from collections import deque
from types import SimpleNamespace

from thronglet_research import ResearchArchive


def organism(words=None, generation=0):
    return SimpleNamespace(
        entity_id="unit-test-organism",
        age=12,
        energy=75.0,
        x=4,
        y=9,
        generation=generation,
        lexicon=words or {},
        concepts={"local:c0": {}},
        learned_programs={"proto": []},
        language_stats={"messages_sent": 2},
        program_stats={"executions": 1},
        cultural_memory=deque([{"kind": "test"}]),
    )


class ResearchArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.archive = ResearchArchive(self.temp.name + "/archive.sqlite3")
        self.previous = {}

    def tearDown(self):
        self.temp.cleanup()

    def test_conversations_survive_reopening_archive(self):
        self.archive.record_conversation(
            8, "sender", "receiver", "mira",
            {"resource": "high"}, "resource-rich", 0.35, False,
        )
        reopened = ResearchArchive(self.temp.name + "/archive.sqlite3")
        rows = reopened.conversations("mira")
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["symbol"], "mira")
        self.assertEqual(rows[0]["interpretation"], "resource-rich")
        self.assertFalse(rows[0]["understood"])

    def test_profiles_remain_after_death(self):
        self.archive.sync(1, [organism({"mira": "local:c0"})], self.previous)
        self.archive.sync(2, [], self.previous)
        profile = self.archive.organism("unit-test-organism")
        self.assertEqual(profile["status"], "deceased")
        self.assertEqual(profile["last_seen"], 1)

    def test_word_mapping_changes_are_recorded(self):
        self.archive.sync(1, [organism({"mira": "local:c0"})], self.previous)
        self.archive.sync(2, [organism({"mira": "local:c1"})], self.previous)
        history = self.archive.words("mira")[0]["history"]
        self.assertEqual(history[-1]["action"], "meaning-change")

    def test_word_adoption_and_summary(self):
        self.archive.sync(1, [organism({"mira": "local:c0"}, generation=1)], self.previous)
        summary = self.archive.summary()
        self.assertEqual(summary["adoptions"], 1)
        self.assertEqual(summary["organisms"], 1)


if __name__ == "__main__":
    unittest.main()
