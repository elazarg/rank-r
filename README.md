# A machine-checked rank-$r$ partial-trace inequality

A Lean 4 formalization of the main theorem of `paper/rank-r.tex`,

> **Theorem 1.1.** Let $U, V$ be finite-dimensional complex Hilbert spaces and
> let $C \in \mathcal L(U \otimes V)$ have $\operatorname{rank} C \le r$. Then
> $$\|\mathrm{Tr}_U C\|_2^2 + \|\mathrm{Tr}_V C\|_2^2 \;\le\; r\|C\|_2^2 + \tfrac1r|\mathrm{Tr}\,C|^2 .$$

together with the numerical pre-flight suite used to check the manuscript's
claims before formalizing them, and a list of concrete edits the manuscript
needs.

## What is proved, and what it rests on

```lean
theorem RankR.rank_r_partial_trace (hFGP : DoubleSkewBound U V)
    (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (hr : 0 < r) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace
```

`#print axioms RankR.rank_r_partial_trace` reports only
`propext, Classical.choice, Quot.sound`. There is no `sorry`, no `axiom`
declaration, no `native_decide` and no `set_option` anywhere in `RankR/`.

The single hypothesis `DoubleSkewBound U V` is Lemma 2.1 of the manuscript **as
its proof actually consumes it**: for every $K$ in the linear span of
$\mathfrak{so}(U) \otimes \mathfrak{so}(V)$ and every orthonormal pair $x,y$,

$$\|Kx\|^2 + \|Ky\|^2 \;\le\; \tfrac12\|K\|_2^2 .$$

It is carried as a hypothesis rather than an `axiom` precisely so that
`#print axioms` stays meaningful and the dependency is visible in the type.
`RankR/Edge.lean` is the *only* file that consumes it; everything else is
unconditional.

**Not proved here:** the manuscript's derivation of Lemma 2.1 from
Fu–Gao–Park [arXiv:2607.21367] — the zero-extension, the
$(\wedge^2U)\otimes(\wedge^2V)$ identification, the best-Schmidt-rank-2
approximation identity, and Ky Fan — nor Fu–Gao–Park itself. Replacing
`DoubleSkewBound` by FGP's literal published statement is Phase B of `PLAN.md`.

Two labelled equations of the manuscript, `eq:Phi-Pminus-TTstar` and
`eq:sos-complete-graph`, are **bypassed rather than proved**: the Bessel-duality
route in `Bessel.lean` never forms the synthesis map as a matrix, which removes
the need for both. They remain unverified as claims about the paper.

## Building

Requires [`elan`](https://github.com/leanprover/elan). Mathlib is the only
dependency.

```bash
lake exe cache get     # Mathlib oleans — do not skip, a source build takes hours
lake build RankR
```

The repository root is the Lake package; `lean-toolchain` pins
`leanprover/lean4:v4.32.0` and `lake-manifest.json` pins the exact Mathlib
revision.

## Layout

| Path | Contents |
| --- | --- |
| `RankR/` | the formalization (18 files, ~2.5k lines) |
| `PLAN.md` | roadmap, ordered by *delicacy* rather than effort; Phase A is complete |
| `MANUSCRIPT-NOTES.md` | twelve concrete edits the manuscript needs |
| `preflight.py` | 21 numerical checks of specific labelled equations |
| `paper/` | the manuscript (`rank-r.tex`, `rank-r-revised.tex`) |
| `quitting-game/` | an unrelated project: exact Z3 barrier checks for four-player quitting games |

### The formalization, bottom-up

| File | Contents |
| --- | --- |
| `Conventions` | §1 conventions, `doubleSkew`, the Fu–Gao–Park interface |
| `HS` | Hilbert–Schmidt layer, transported from `EuclideanSpace` |
| `Elementary` | rank monotonicity, the contraction identities, trace–rank bound |
| `Operator` | `qform`, factor placements, marginals |
| `Factor` | range factorization `C = ∑ᵢ|eᵢ⟩⟨dᵢ|` |
| `Main` | `qform` algebra, `HopScaled`, Theorem 1.1 given Proposition 2.2 |
| `Skew` | `skewUnit`, `Kᵀ = K` on `doubleSkew` |
| `Kraus` | `qform (A Y Aᴴ) x = qform Y (Aᴴx)`, PSD preservation |
| `Sectors` | doubled sectors, `Ppos − Pneg = 2·ρ₀ᵀ` |
| `Phi` | the `Φ₄` kernel, `eq:Phi-expansion`, `eq:Phi-rhoT` |
| `Synth` | the synthesis map, `eq:T-by-vertices`, the vertex bound |
| `Frame` | adjoint move, `eq:T-orthogonal` |
| `Edge` | the edgewise double-skew bound — the sole consumer of `hFGP` |
| `Assemble`, `Bessel`, `Restrict`, `Synthesis` | the Bessel-duality chain |
| `Theorem` | **Proposition 2.2 and Theorem 1.1** |

## Pre-flight

```bash
python3 preflight.py     # 21/21
```

Each check targets a specific labelled equation of the manuscript at small
dimensions. Two are worth singling out:

- **`Tier D3`** checks the index matching between Fu–Gao–Park as published and
  the manuscript's application of it — the step the manuscript asserts without
  exhibiting. Parts (a)–(c) are exact: $Q_-$ is a projection with commuting
  factors, its rank equals $\dim(\mathfrak{so}(d)\otimes\mathfrak{so}(d))$, and
  every $\operatorname{vec}K$ is fixed by it. Part (d) is a random-restart
  search, so it corroborates FGP's own bound rather than proving it.
- **`Prop 2.2 residual`** mirrors the Lean decomposition numerically, isolating
  exactly what the complete-graph argument must deliver.

The suite is *not* a substitute for the formalization: it runs only at
$r \le 6$, $d \le 5$, and cannot reach anything quantifying over Schmidt number.

## A note on provenance

`paper/rank-r.tex` states that its arguments were generated by GPT-5.6, that the
author did not independently derive them, and that no expert has reviewed them.
Fu–Gao–Park was posted three days before the manuscript and is itself
unreviewed. This formalization is therefore a *measuring instrument*, not a
victory lap — which is why `PLAN.md` orders the work by where a wrong step
would hide rather than by the structure of the paper.
