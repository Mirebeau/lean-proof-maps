# Lean proof maps

Public pages of the Lean 4 formalizations of papers by Jean-Marie Mirebeau and coauthors, served
by GitHub Pages at <https://mirebeau.github.io/lean-proof-maps/>. One folder per paper; each page
shows the frozen Lean statements of the paper and their dependency graph. The pages are generated
from the (private) formalization repository; do not edit them by hand.

`GuaranteedSubsol/lean/` contains the Lean sources of that formalization, a standalone Lake
project copied from the same repository together with the page; see its `README.md` for build
instructions.

`<paper>/#label=<LaTeX label>` opens the anchors of a statement of the paper, e.g.
`GuaranteedSubsol/#label=lem:max_min`.
