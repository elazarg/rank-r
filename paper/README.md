# Manuscripts

`rank-r.tex` is the focused paper and `rank-r.pdf` is its tracked typeset form.
The `derivation-*.tex` files are standalone companion notes, not omitted
sections or appendices of the main paper.

| Source | Role | Relation to the main paper | Formal status |
| --- | --- | --- | --- |
| `derivation-beta-k.tex` | Higher Choi constants of the double-skew space | Extends the local constant beyond the level-two input used in the paper | Exact for every level at least two; the level-one lower bound is checked and the matching upper bound is conjectural |
| `derivation-graph-inclusion.tex` | Free-spectrahedral and operator-system form of the graph construction | The main paper already contains the exact local constant, clique sharpness, and the one-layer/two-layer warning; the compressed inclusion and rook-graph results remain here | The basis-free finite-level inclusion is checked; choosing the displayed monic-pencil basis remains a presentation interface |
| `derivation-higher-arity.tex` | Exterior and hypergraph amplification | A genuine extension of the complete-graph estimate, not another route to the paper's $r$-positive map | The amplification theorem and double-skew specialization are checked; the explanatory spectral no-go is not separately formalized |
| `derivation-schmidt-staircase.tex` | Schmidt-number application of the protected witness | Uses the main lift and map identity but addresses a separate mixed-state problem | The lower-bound direction is checked; the exact upper direction remains conditional on the product-isotropic seed and twirl inputs |

The declaration-level boundary, including every conditional and open item, is
maintained in [`docs/FORMALIZATION.md`](../docs/FORMALIZATION.md).

## Building and cleaning

Run `latexmk` from this directory. Clean its intermediate files after each
build:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error rank-r.tex
latexmk -c rank-r.tex
```

The main PDF is tracked. Companion PDFs are local inspection artifacts and are
ignored; remove them together with their intermediates using:

```bash
latexmk -C derivation-*.tex
```
