# DYVis

Diagrams for protocols verified with [DyLean](https://github.com/BobDyLean/dylean).
It has two parts:

- **`DYVis.Trace`** draws a run. A scenario is an ordinary `Traceful` run whose
  steps also name their actor; DYVis draws it as a Mermaid sequence diagram.
  See [`DYVis/Trace/README.md`](DYVis/Trace/README.md).
- **`DYVis.Theorem`** draws what a security theorem permits. `#traceClaim` reads
  the theorem's statement, and the viewer draws it. The drawings are covered by
  approval tests. See [`DYVis/Theorem/README.md`](DYVis/Theorem/README.md).

## Using it

```toml
[[require]]
name = "dyvis"
git = "https://github.com/julianpritzi/DyVis.git"
rev = "main"
```

DYVis requires DyLean from the `dyaeneas-main` branch of
[julianpritzi/dylean](https://github.com/julianpritzi/dylean). A project that
already requires `dylean` supplies its own copy.

## Layout

| Path | What |
|---|---|
| `DYVis/Trace/` | Trace diagrams; self-checks in `Check/` |
| `DYVis/Theorem/` | Claim extraction (`#traceClaim`); reference theorems in `Example.lean` |
| `viewer/` | The theorem viewer (`viewer.html`), and the node tools in `tests/` |
| `scripts/` | `snapshot.sh` (approval tests), `review.sh` (review server) |
| `diagrams/` | Reference claims and their approved snapshots |

## Checks

`lake build` builds the library and its self-checks. They rewrite
`DYVis/Trace/Check/Basic/*.md` and `diagrams/claims/reference.json`.
`scripts/snapshot.sh --check` then fails if an approved diagram changed. The
scripts need `node` (or `deno` or `bun`).

Agents: read [`AGENTS.md`](AGENTS.md) first.
