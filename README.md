# Thronglet

A Black Mirror-inspired artificial-life experiment. Digital beings evolve, invent languages, share knowledge and develop their own cultures inside a local simulation.

## Run locally

Requires Python 3.10 or newer. No third-party packages are required.

```bash
python spatial_void.py
```

Open [http://127.0.0.1:8000](http://127.0.0.1:8000) to view the research dashboard.

## Research archive

The dashboard includes live population data, a searchable conversation archive, a living dictionary, organism profiles (including deceased organisms), and language analytics.

Research records are stored locally in `thronglet_archive.sqlite3` in the directory from which the simulation is started. The archive survives simulation restarts. Keep this file if you want to preserve your experiment history.

The communication channel transmits a symbol and observable environmental context, not the sender's private concept ID or concept label. Receivers build tentative interpretations from repeated contextual evidence. The dashboard distinguishes confirmed known-word interpretations from uncertain guesses.

## Safety boundary

Organism programs execute only inside the simulation's constrained virtual machine. They cannot execute Python, access files, run shell commands, or access the network.
