# A machine-checked rank-$r$ partial-trace inequality

A Lean 4 formalization of the main theorem of `paper/rank-r.tex`,

> **Theorem 1.1.** Let $U, V$ be finite-dimensional complex Hilbert spaces and
> let $C \in \mathcal L(U \otimes V)$ have $\operatorname{rank} C \le r$. Then
> $$\|\mathrm{Tr}_U C\|_2^2 + \|\mathrm{Tr}_V C\|_2^2 \;\le\; r\|C\|_2^2 + \tfrac1r|\mathrm{Tr}\,C|^2 .$$

The manuscript's abstract records that these proofs are machine-checked. That
claim is deliberately narrow, and what follows spells out its limits.

## What is proved, and what it rests on

```lean
theorem RankR.rank_r_partial_trace
    (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (hr : 0 < r) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace
```

**There are no hypotheses.** Earlier revisions carried the Fu–Gao–Park estimate
as a standing assumption; it has since been discharged. The chain is

    Autonne–Takagi  →  Lemma 2.1  →  Proposition 2.2  →  Theorem 1.1

with `Matrix.exists_takagi` in `RankR/Autonne.lean` supplying the first step.

`#print axioms RankR.rank_r_partial_trace` reports only
`propext, Classical.choice, Quot.sound`, and no declaration uses `sorry`,
`axiom`, `native_decide` or `set_option`. The axiom half of that claim is not
merely asserted: `RankR/Axioms.lean` wraps `#print axioms` in `#guard_msgs`
for each headline theorem, so the build fails if it ever stops holding.

### How the hypothesis was discharged, and whose argument it is

`RankR/Autonne.lean` proves the **Autonne–Takagi factorization** — every complex
symmetric matrix is $UDU^T$ with $U$ unitary and $D$ diagonal nonnegative
(Horn–Johnson, *Matrix Analysis*, 2nd ed., Cor. 4.4.4(c)). It is absent from
Mathlib, and is stated coordinate-free
(`LinearMap.IsConjSymmetric.exists_orthonormalBasis`) with the matrix form as a
specialization. `RankR/Takagi.lean` then derives Lemma 2.1 from it.

**The mathematics is Fu–Gao–Park's.** This is not an independent route: it is
their §2 argument — their Prop. 2.1, Lemma 2.2, Lemma 2.3 — restructured so that
Autonne–Takagi enters directly and their Theorem 2.4 is never invoked. What is
new here is the observation that their duality step and their use of
Johnston–Kribs are avoidable, plus the machine checking. Their preprint remains
the source of the argument.

**Fu–Gao–Park's Theorem 2.4 is proved too.** `RankR/Equivalence.lean` supplies
the converse of `doubleSkewBound_of_FGP`, so the double-skew bound and the
imported estimate are *equivalent*; both then follow from Autonne–Takagi, and
`fgpBound_holds` is `FGPBound` with no hypotheses.

The converse looks harder than it is. Stated as `K ∈ doubleSkew U V` — the span
of the elementary tensors — it would need `ran Qm ⊆ vec (doubleSkew U V)`, a
spanning argument dragging a linear order on `U` and `V` into the development.
Restating the bound with the fixed-point hypothesis `Qm (vec K) = vec K`
(`DoubleSkewBoundQm`) avoids that entirely: the new form is formally *stronger*,
yet no harder to prove, because `Qm (vec K) = vec K` already forces `Kᵀ = K`.

What remains a rendering rather than a transcription is that `FGPBound` is
stated in homogeneous form over `|u₁⟩⟨v₁| + |u₂⟩⟨v₂|` rather than over unit
vectors of Schmidt rank at most two. By `eq:SR-vec-rank` those are the same
statement, but that identification is a reading of the definitions, not a
theorem here.

**What this does and does not certify.** Lean checks the *deduction* — that the
conclusion follows from the hypothesis, given the formal definitions in
`RankR/Conventions.lean`. It cannot check that those formal definitions
faithfully render the manuscript's informal ones. That correspondence is a
human judgement, which is why `Conventions.lean` states each convention
explicitly (inner products conjugate-linear in the first argument;
$\mathrm{Tr}_U$ = trace *over* $U$; $\mathrm{vec}(|x\rangle\langle y|) = x \otimes \bar y$;
$\mathfrak{so}$ defined by $L^T = -L$, not $L^H = -L$) rather than leaving them
implicit. One rendering is worth singling out:
`FGPBound` quantifies over the explicit two-term form
`M = |u₁⟩⟨v₁| + |u₂⟩⟨v₂|`, which is "Schmidt rank ≤ 2 across the row:col cut"
unrolled rather than a theorem about it.

The sharpness claims around Theorem 1.1 are covered too.
`rank_r_partial_trace_exact` is the exact-rank form (`r = rank C`),
`rank_r_partial_trace_strict` says the bound is *strict* for
nonzero `C` with `rank C < r`, and `rank_eq_of_eq_rank_r_partial_trace`
is the stated consequence: equality for nonzero `C` forces `rank C = r`.

`RankR/OneSided.lean` adds the one-sided bound `‖Tr_j C‖₂² ≤ r‖C‖₂²`
(`lem:one-sided-partial-trace`), also unconditional. The manuscript proved it by
trace-norm duality; here a partial trace of a rank-one operator is a matrix
product, so Hilbert–Schmidt submultiplicativity and Cauchy–Schwarz over the range
factorization suffice, and the Schatten-1 norm appears nowhere.

`RankR/Optimal.lean` closes the other half. It builds the extremizer `projWit = P_r ⊗ |v⟩⟨w|`,
computes its rank (`rank_projWit`, exactly `r`) and its four quantities
(`‖C‖₂² = r`, `|Tr C|² = r²|⟨w,v⟩|²`, `‖Tr_U C‖₂² = r²`, `‖Tr_V C‖₂² = r|⟨w,v⟩|²`),
shows it attains equality (`projWit_bound_eq`), and derives the two optimality
statements: any bound `‖Tr_U C‖₂² + ‖Tr_V C‖₂² ≤ a‖C‖₂² + b|Tr C|²` valid at
rank `r` has `a ≥ r` (`le_coeff_hsNormSq_of_bound`), and once `a = r` is fixed,
`b ≥ 1/r` (`inv_le_coeff_trace_of_bound`).

**Not proved here:** the identification of `FGPBound` with Theorem 2.4 as stated
via an abstract Schmidt-rank predicate. `FGPBound` quantifies over the explicit
two-term form; that this is the same condition as "Schmidt rank ≤ 2" is
`eq:SR-vec-rank`, a definitional reading rather than a formalized theorem — the
development contains no definition of Schmidt rank at all. The estimate itself
*is* proved (`fgpBound_holds`). Also not proved: any of the applications in §4
or the appendices of the manuscript.

### Two sharpenings not in the manuscript

**The symmetry hypothesis is a condition on the compression, not on the operator.**
`Frame.lean` defines `IsFrameSymmetric e N` — the compression `E^*NĒ` of `N` to the
frame `E : q_i ↦ e_i` is a symmetric matrix — and `Lifting.lean`, `HigherArity.lean`
now take that in place of `Nᵀ = N`. It is what the orthogonality actually consumes:
in the fermionic notation of `HigherArity.lean`, `ε_E^*(N ⊗ I)∂_E = ι_{Alt(E^*NĒ)}`,
so the Koszul cancellation is the vanishing of the alternating part of the
compression and nothing more. Transpose symmetry is the frame-independent
strengthening, and that characterization is itself checked, in both directions:
`isFrameSymmetric_of_transpose_eq` gives one, and
`transpose_eq_of_forall_isFrameSymmetric` gives the other — quantifying over
frames recovers `Nᵀ = N`, and two-element frames already suffice. The double-skew
family supplies the hypothesis through the first of those, applied at
`skewKraus_transpose`. Theorem 1.1 is unaffected: `skewKraus` is transpose-symmetric
anyway. What changes is the class the liftings apply to, and the honesty of the
statement about which property does the work.

**Exterior amplification holds in a weighted form.** `HigherArity.lean` states
Theorems A and B for a hypergraph whose every hyperedge carries its *own* Kraus
family `A_I` and its own constant `β_I`:

    ∑_{I ∈ H} (Φ_{A_I} ⊗ id)(|η_I⟩⟨η_I|)  ⪯  Γ (I − Π),
    Γ ≥ max_J ∑_{I ∈ H, J ⊆ I} β_I,

as `qform_PhypAmp_le_of_norm` and `qform_PhypAmp_le`. The coefficient is the
weighted modulus of the incidence correspondence; the uniform theorems are the
constant-weight case, where that modulus is the largest fibre `d↑_{k-1}(H) β`, and
`qform_krausF_Phyp_le_of_weighted` derives Theorem B from the weighted form to
check the two agree. The one hypothesis the weighted route adds is `0 < β_I`,
because the weighted regrouping divides by the weight; `qform_krausF_Phyp_le`
still covers `β = 0` directly.

**Not proved:** the *support-adapted* protected space of the same generalization —
restricting the star of each `(k-2)`-face to the facets actually present in `H`,
so that `Π` has rank the number of actual hinges rather than `binom(r, k-2)`, and
`I` is replaced by the projection onto actual facets. The same Koszul cancellation
applies, but the modes change and their orthonormality has to be redone.

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
| `RankR/` | the formalization (34 files) |
| `paper/` | the manuscript |

### The formalization, bottom-up

| File | Contents |
| --- | --- |
| `Conventions` | §1 conventions, `doubleSkew`, the double-skew interface |
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
| `Frame` | `Pneg` as an edge sum, `eq:T-orthogonal` |
| `Edge` | orthonormality of the conjugated frame |
| `Choi` | `J(Φ) = ∑ₐ\|vec Aₐ⟩⟨vec Aₐ\|`, the constant `β₂`, and **Lifting I** for an arbitrary Kraus family |
| `ChoiSkew` | **`J(Λ_U ⊗ Λ_V) = 16 Qm`**, hence `β₂ = 4` in the `Phi4` scaling |
| `MapId` | `Δ` monoidal, `(Λ_U⊗Λ_V)∘τ = S_U⊗S_V`, and **the map identity** `Ψ_r = r·R_{−1/r}⊗R_{−1/r}` |
| `Bessel`, `Restrict` | Bessel duality, and its sharpening on `δ_e^⊥` |
| `Lifting` | **Lifting II** in both operator forms, for an arbitrary Kraus family and sharpened on `δ_e` for a frame-symmetric one |
| `Theorem` | Proposition 2.2 and Theorem 1.1 given the rank-two Choi bound |
| `Antisym`, `FGP`, `Extend` | the antisymmetrizer, and Theorem 1.1 from Fu–Gao–Park as published (retained, no longer on the critical path) |
| `Optimal` | the extremizer, and optimality of the coefficients `r`, `1/r` |
| `OneSided` | HS submultiplicativity, and `lem:one-sided-partial-trace` |
| `Flip` | the two partial transposes, and `⟨N, Π N⟩ = ½(‖N‖₂² − ⟨N, N^{T_U}⟩)` |
| `SymOuter` | `w wᵀ` and its pairings; the flip trace identity; two HS estimates |
| `Weights` | Ky Fan at `k = 2`, in weight form |
| `Takagi` | the Autonne–Takagi interface, Lemma 2.3, and the truncation chain |
| `Autonne` | **the Autonne–Takagi factorization itself** |
| `Equivalence` | the converse, and **Fu–Gao–Park's Theorem 2.4** |
| `Results` | joins the two halves: Theorem 1.1 with no hypotheses |
| `BlockPos` | Theorem 1.1 as the `r`-block positivity of `J(Ψ_r)` |

| `Axioms` | the axiom surface, checked by the build |

The import graph has two independent halves that meet only in `Results`: the
*reduction* (`Conventions` … `Theorem`), which is parametrized by the pair
`(Φ, β₂)` and knows nothing about where the constant comes from, and the *bound*
(`Antisym`, `Flip`, `SymOuter`, `Weights`, `Takagi`, `Autonne`, `Equivalence`),
which knows nothing about partial traces. `Extend` hangs off the reduction and
is no longer on any critical path.

Everything from `Sectors` through `Lifting` lives on a single space `W` tensored
with the ancilla: the sectors, the placement `A ↦ A ⊗ I_Q`, the synthesis map and
both operator forms of Lifting II index `W` atomically. The tensor factorization
`W = U ⊗ V` is used only by the `Φ₄` kernel of `Phi.lean` and downstream of it.

The seam between the two halves is one number. `Choi.lean` and `Lifting.lean` are
stated for an arbitrary completely positive `Φ` with transpose-symmetric Kraus
operators, and consume it only through

    ChoiTwoBound (choiOf A) β  —  ⟨z, J(Φ) z⟩ ≤ 2β‖z‖² for z of Schmidt rank ≤ 2,

so `Λ_U ⊗ Λ_V` enters exactly once, in `ChoiSkew.lean`, as
`J = 16 Qm` and hence `β = 4`.

## A note on provenance

`paper/rank-r.tex` states that its arguments were generated by GPT-5.6, that the
author did not independently derive them, and that no expert has reviewed them.
Fu–Gao–Park was posted three days before the manuscript and is itself unreviewed.
This formalization is therefore a *measuring instrument*, not a victory lap.

Discharging the standing hypothesis narrows what is being measured but does not
change that. Lean checks deductions; it does not check that
`RankR/Conventions.lean` renders the manuscript's informal definitions
faithfully, and with the hypothesis gone that definitional-fidelity question is
the *only* thing left between the formal result and the informal claim. It
deserves more scrutiny now, not less.
