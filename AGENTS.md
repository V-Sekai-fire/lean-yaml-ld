# Agent rules

The standing rules of the Chibifire Hair Cards project are in the viewer repository's `AGENTS.md` ("Every repository" and "Work flow") with their reasons in its `docs/rules.md`: https://github.com/V-Sekai-fire/interactor-hair-cards-viewer (local `/mnt/fire/3-interactor/interactor-hair-cards-viewer`). The workspace `AGENTS.md` of the manuals checkout binds too. In short: comments at most 3% of code lines; per-function branching at most 1.5 mean and 4 peak; a README is one 280-character blurb; scripts are Elixir or engine GDScript; read a LICENSE before using a model; every service has an AsyncAPI document; ENet is blocklisted; commits are authored as the owner with no agent credit and no trailing period; work lands on `dev/` branches that the viewer repository's `tools/automerge.exs` merges to main.

## This repository

- The YAML-LD reader and writer in Lean 4; the planner (`interactor-persona-frontier`) requires this repository at main once its trigger fires.
- Check: `./make.sh`.
