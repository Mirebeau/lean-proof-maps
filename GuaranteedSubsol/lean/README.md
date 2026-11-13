# GuaranteedSubsol: Lean 4 sources

Lean 4 / Mathlib formalization of the preprint

> J.-M. Mirebeau, Y. Mouheb, *A narrow band method for non-causal discretizations of anisotropic
> eikonal equations, with adaptive width, sub- and super-solution construction, and quasi-linear
> complexity* (2026), [hal-05861742](https://hal.science/hal-05861742).

All the lemmas, propositions and theorems of the paper are stated and proved, with no `sorry` and
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The statements, with links
to the paper and their dependency graph, can be browsed at
<https://mirebeau.github.io/lean-proof-maps/GuaranteedSubsol/>.

These files are a copy of a private development repository, updated together with the web page.
Do not edit them here.

## Building

1. Install Lean through `elan`: <https://lean-lang.org/install/>. The Lean version (`v4.35.0`) is
   fixed by `lean-toolchain` and downloaded automatically.
2. Get the sources and build:

   ```sh
   git clone https://github.com/Mirebeau/lean-proof-maps.git
   cd lean-proof-maps/GuaranteedSubsol/lean
   lake exe cache get    # download the compiled Mathlib (a few GB), instead of building it
   lake build
   ```

   `lake build` compiles the formalization itself: a few minutes on a recent laptop. It succeeds
   with no error and no `sorry` warning.

To check the axioms of a result, for example the complexity theorem of the ANB method
(Theorem `th:complexity` of the paper):

```sh
printf 'import LeanHJBAutoformalisation\n#print axioms GuaranteedSubsol.anbRun_complexity\n' > Check.lean
lake env lean Check.lean
```

## Contents

- `LeanHJBAutoformalisation/GuaranteedSubsol/`: definitions (`Axioms.lean`, `AxiomsExt.lean`,
  `Kruzkov.lean`, …), algorithms (`Dijkstra.lean`, `Anb.lean`, `AnbHeap.lean`, …) and proofs, in
  the namespace `GuaranteedSubsol`.
- `LeanHJBAutoformalisation/GuaranteedSubsol/Anchors/`: the statements of the paper's results, one
  per file. Each was reviewed and approved by the author, then frozen; its proof is a one-line
  reference to the proof file. `ANCHORS.md` lists them with their LaTeX labels.
- `DEFINITIONS.md`: correspondence between the definitions of the paper and the Lean ones.
- `LeanHJBAutoformalisation.lean`: the root file, importing everything.

Docstrings refer to the statements of the paper by their LaTeX labels (e.g. `th:complexity`), which
the web page translates into the printed numbers.

## AI assistance

This code was produced with AI assistance (Claude, by Anthropic, through Claude Code). The Lean
statements were proposed by the AI and reviewed and approved by the author before being frozen.
The proofs were written by AI agents and are checked by the Lean kernel.

## License

Copyright 2026 Jean-Marie Mirebeau. Released under the Apache License 2.0, see `LICENSE`.
