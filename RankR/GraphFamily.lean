/-
The edge-Kraus family of a graph, and its rank-two Choi constant.

For a simple graph `G` on a vertex set `U`, `paper/derivation-graph-inclusion.tex`
attaches to each edge `{i, j}` the operator

    A_{ij} = (E_ij - E_ji) ⊗ (E_01 - E_10)   on   U ⊗ ℂ²,

both factors skew, so `A_{ij}ᵀ = A_{ij}`: the family carries the transpose
symmetry that `Lifting.lean` consumes.  `Φ_G(Y) = ∑_{e ∈ E} A_e Y A_e` is the
completely positive map they generate, and `lem:beta` of that manuscript is
`β₂(Φ_G) = 1` for every nonempty `G`.

Both halves are here, in the two-sided form of `Sharp.lean`.

The upper bound does not repeat the singular-value argument of the manuscript.
Each `A_e` lies in `so(U) ⊗ so(ℂ²)`, so `Qm` fixes its vectorization; since `Qm`
is self-adjoint, every pairing `⟪vec A_e, vec M⟫` may be read at `Qm (vec M)`
instead.  The `vec A_e` are orthogonal of squared norm `4`, so Bessel bounds the
Choi form by `4‖Qm (vec M)‖²`, and the double-skew estimate bounds that by
`½‖M‖₂²`.  The product is `2‖M‖₂²`, which is `β = 1`.

The lower bound is a single edge: `A_e` itself is a sum of two rank-one
operators, and it meets the bound with equality.  So the graph plays no role in
the constant --- only in which edges are present --- which is what makes `β₂`
usable as a graph-independent input to pair amplification.
-/
import RankR.Sharp

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

/-! ## Hilbert-Schmidt pairings -/

section Pairing

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `hsInner` of two elementary matrix units. -/
theorem hsInner_single (a b c d : W) :
    hsInner (Matrix.single a b (1 : ℂ)) (Matrix.single c d 1)
      = (if a = c then (1 : ℂ) else 0) * (if b = d then 1 else 0) := by
  rw [hsInner_eq_sum_vec, Fintype.sum_prod_type]
  simp only [vec_apply, Matrix.single_apply, ite_and, apply_ite (starRingEnd ℂ),
    map_one, map_zero, ite_mul, zero_mul, mul_ite, mul_zero]
  by_cases hac : a = c <;> by_cases hbd : b = d <;> simp [hac, hbd]

/-- **The elementary skew matrices are Frobenius-orthogonal**, with squared norm
`2`.  Reading it at `(a, b) = (c, d)` gives `‖skewUnit a b‖₂² = 2` for `a ≠ b`;
reading it at an unordered pair met in the opposite order gives `-2`; and any two
distinct unordered pairs give `0`. -/
theorem hsInner_skewUnit (a b c d : W) :
    hsInner (skewUnit a b) (skewUnit c d)
      = 2 * ((if a = c then (1 : ℂ) else 0) * (if b = d then 1 else 0)
          - (if a = d then (1 : ℂ) else 0) * (if b = c then 1 else 0)) := by
  simp only [skewUnit, hsInner_sub_left, hsInner_sub_right, hsInner_single]
  ring

end Pairing

/-! ## The Kronecker factorization of `hsInner` -/

section Kron

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

omit [DecidableEq U] [DecidableEq V] in
/-- `⟪A ⊗ B, C ⊗ D⟫ = ⟪A, C⟫ ⟪B, D⟫`: the Hilbert-Schmidt inner product is
multiplicative on elementary tensors. -/
theorem hsInner_kron (A C : Matrix U U ℂ) (B D : Matrix V V ℂ) :
    hsInner (A ⊗ₖ B) (C ⊗ₖ D) = hsInner A C * hsInner B D := by
  rw [hsInner, hsInner, hsInner, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.trace_kronecker]

end Kron

/-! ## The edge family -/

section EdgeFamily

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- The Kraus operator of the edge `(i, j)`.  It is the double-skew generator
`skewKraus ((i, j), (0, 1))` of `ChoiSkew.lean` read at `V = ℂ²`. -/
noncomputable def edgeKraus (p : U × U) : Matrix (U × Fin 2) (U × Fin 2) ℂ :=
  skewUnit p.1 p.2 ⊗ₖ skewUnit (0 : Fin 2) 1

omit [Fintype U] [LinearOrder U] in
theorem edgeKraus_mem_doubleSkew (p : U × U) : edgeKraus p ∈ doubleSkew U (Fin 2) :=
  kron_mem_doubleSkew (skewUnit_isSkew _ _) (skewUnit_isSkew _ _)

omit [Fintype U] [LinearOrder U] in
/-- The Kraus operators are transpose-symmetric: two skew factors make a
symmetric tensor. -/
theorem edgeKraus_transpose (p : U × U) : (edgeKraus p)ᵀ = edgeKraus p :=
  transpose_eq_self_of_mem_doubleSkew (edgeKraus_mem_doubleSkew p)

/-- The pairing of two edge operators: `4` on the diagonal and `0` off it, for
edges written with their endpoints in increasing order. -/
theorem hsInner_edgeKraus {p q : U × U} (hp : p.1 < p.2) (hq : q.1 < q.2) :
    hsInner (edgeKraus p) (edgeKraus q) = if p = q then 4 else 0 := by
  rw [edgeKraus, edgeKraus, hsInner_kron, hsInner_skewUnit, hsInner_skewUnit]
  have hJ : (if (0 : Fin 2) = 0 then (1 : ℂ) else 0) * (if (1 : Fin 2) = 1 then 1 else 0)
      - (if (0 : Fin 2) = 1 then (1 : ℂ) else 0) * (if (1 : Fin 2) = 0 then 1 else 0) = 1 := by
    norm_num
  rw [hJ]
  have hcross : ¬ (p.1 = q.2 ∧ p.2 = q.1) := by
    rintro ⟨h1, h2⟩
    exact absurd (h1 ▸ h2 ▸ hp) (asymm hq)
  by_cases hpq : p = q
  · subst hpq
    simp [ne_of_lt hp]
    norm_num
  · have hne : ¬ (p.1 = q.1 ∧ p.2 = q.2) := fun h => hpq (Prod.ext h.1 h.2)
    rw [if_neg hpq]
    by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
      by_cases h3 : p.1 = q.2 <;> by_cases h4 : p.2 = q.1 <;>
        simp_all

/-- **The Kraus family of `Φ_G`**, one operator per edge of `E`. -/
noncomputable def graphKraus (E : Finset (U × U)) :
    {p : U × U // p ∈ E} → Matrix (U × Fin 2) (U × Fin 2) ℂ :=
  fun e => edgeKraus e.val

omit [Fintype U] [LinearOrder U] in
theorem graphKraus_transpose (E : Finset (U × U)) (e : {p : U × U // p ∈ E}) :
    (graphKraus E e)ᵀ = graphKraus E e := edgeKraus_transpose e.val

omit [Fintype U] [LinearOrder U] in
theorem graphKraus_mem_doubleSkew (E : Finset (U × U)) (e : {p : U × U // p ∈ E}) :
    graphKraus E e ∈ doubleSkew U (Fin 2) := edgeKraus_mem_doubleSkew e.val

/-- **The vectorized edge family, halved, is orthonormal.**

`‖A_e‖₂² = 4` for every edge, and distinct edges are Frobenius-orthogonal: the
only way two elementary skew tensors can pair is through a shared unordered pair
of endpoints, and writing every edge with its endpoints in increasing order
leaves one representative per pair.  This is the combinatorial input to
`lem:beta`, and the only place the graph enters. -/
theorem orthonormal_graphKraus {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2) :
    Orthonormal ℂ (fun e : {p : U × U // p ∈ E} =>
      ((2 : ℂ)⁻¹ • vec (graphKraus E e) : EuclideanSpace ℂ (Idx U (Fin 2)))) := by
  rw [orthonormal_iff_ite]
  intro e f
  rw [inner_smul_left, inner_smul_right, ← hsInner_eq_inner, graphKraus, graphKraus,
    hsInner_edgeKraus (hE e.val e.property) (hE f.val f.property)]
  by_cases h : e = f
  · subst h
    rw [if_pos rfl, if_pos rfl]
    norm_num [map_ofNat]
  · have hne : e.val ≠ f.val := fun hv => h (Subtype.ext hv)
    rw [if_neg hne, if_neg h]
    ring

end EdgeFamily

/-! ## The rank-two Choi constant of `Φ_G` -/

section Beta

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- **The double antisymmetrizer satisfies the rank-two bound at `¼`**, with no
hypothesis: `choiOf skewKraus` is `16 Qm` and its constant is `4`. -/
theorem choiTwoBound_Qm : ChoiTwoBound (Qm : Matrix (Idx U V) (Idx U V) ℂ) (1 / 4) := by
  have h := choiTwoBound_holds (U := U) (V := V)
  rw [choiOf_skewKraus] at h
  have h' := choiTwoBound_smul (t := (1 / 16 : ℝ)) (by norm_num) h
  have hop : (((1 / 16 : ℝ) : ℂ) • ((16 : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ))) = Qm := by
    rw [smul_smul]
    norm_num
  have hc : (1 / 16 : ℝ) * 4 = 1 / 4 := by norm_num
  rwa [hop, hc] at h'

end Beta

section GraphBeta

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

omit [LinearOrder U] in
/-- Pairings against an edge operator may be read at `Qm v`: the edge operator is
double-skew, so `Qm` fixes it, and `Qm` is self-adjoint. -/
theorem inner_vec_edgeKraus_eq (p : U × U) (v : EuclideanSpace ℂ (Idx U (Fin 2))) :
    inner ℂ (vec (edgeKraus p)) v = inner ℂ (vec (edgeKraus p)) (mulVecE Qm v) := by
  conv_rhs => rw [inner_mulVecE_left, Qm_conjTranspose, mulVecE_Qm_vec (edgeKraus_mem_doubleSkew p)]

/-- **`β₂(Φ_G) ≤ 1`** (`lem:beta`, upper half).

Bessel against the orthonormal halved edge family bounds the Choi form by
`4‖Qm (vec M)‖²`, and `choiTwoBound_Qm` bounds that by `½‖M‖₂²`.  The graph is
invisible to the estimate: dropping edges only removes nonnegative terms. -/
theorem choiTwoBound_graphKraus {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2) :
    ChoiTwoBound (choiOf (graphKraus E)) 1 := by
  intro u₁ v₁ u₂ v₂
  set M := rankOne u₁ v₁ + rankOne u₂ v₂ with hM
  set w : EuclideanSpace ℂ (Idx U (Fin 2)) := mulVecE Qm (vec M) with hw
  have hbess := (orthonormal_graphKraus hE).sum_inner_products_le (s := Finset.univ) w
  have hterm : ∀ e : {p : U × U // p ∈ E},
      Complex.normSq (inner ℂ (vec (graphKraus E e)) (vec M))
        = 4 * ‖inner ℂ ((2 : ℂ)⁻¹ • vec (graphKraus E e)) w‖ ^ 2 := by
    intro e
    rw [graphKraus, inner_vec_edgeKraus_eq, ← hw, inner_smul_left, norm_mul, mul_pow,
      Complex.normSq_eq_norm_sq, ← graphKraus]
    simp [map_inv₀, map_ofNat]
    ring
  have hsum : ∑ e : {p : U × U // p ∈ E},
      Complex.normSq (inner ℂ (vec (graphKraus E e)) (vec M)) ≤ 4 * ‖w‖ ^ 2 := by
    rw [Finset.sum_congr rfl fun e _ => hterm e, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hbess (by norm_num)
  have hQ : ‖w‖ ^ 2 ≤ 1 / 2 * hsNormSq M := by
    rw [hw, norm_mulVecE_Qm_sq]
    have := choiTwoBound_Qm (U := U) (V := Fin 2) u₁ v₁ u₂ v₂
    rw [← hM] at this
    linarith
  rw [re_qform_choiOf]
  have hMn : (0 : ℝ) ≤ hsNormSq M := hsNormSq_nonneg _
  linarith

omit [LinearOrder U] in
/-- Pairing against the extremizer of `Sharp.lean` reads off two entries. -/
theorem hsInner_sharpWit {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix (U × V) (U × V) ℂ) (a₀ a₁ : U) (b₀ b₁ : V) :
    hsInner A (sharpWit a₀ a₁ b₀ b₁)
      = conj (A (a₁, b₁) (a₀, b₀)) - conj (A (a₁, b₀) (a₀, b₁)) := by
  rw [hsInner_eq_sum_vec, Fintype.sum_prod_type]
  simp only [vec_apply, sharpWit_apply, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The pairing of an edge operator against the extremizer at that edge's
endpoints: `2` for the edge itself, `0` for every other edge. -/
theorem hsInner_edgeKraus_sharpWit {p : U × U} (hp : p.1 < p.2) {a₀ a₁ : U} (ha : a₀ < a₁) :
    hsInner (edgeKraus p) (sharpWit a₀ a₁ (0 : Fin 2) 1) = if p = (a₀, a₁) then 2 else 0 := by
  rw [hsInner_sharpWit]
  simp only [edgeKraus, Matrix.kroneckerMap_apply, skewUnit_apply]
  have hne : ¬ (p.1 = a₁ ∧ p.2 = a₀) := by
    rintro ⟨h1, h2⟩
    exact absurd (h1 ▸ h2 ▸ hp) (asymm ha)
  by_cases hpq : p = (a₀, a₁)
  · subst hpq
    simp [ne_of_lt ha, Ne.symm (ne_of_lt ha)]
    norm_num
  · have h2 : ¬ (p.1 = a₀ ∧ p.2 = a₁) := fun h => hpq (Prod.ext h.1 h.2)
    rw [if_neg hpq]
    by_cases c1 : p.1 = a₁ <;> by_cases c2 : p.2 = a₀ <;>
      by_cases c3 : p.1 = a₀ <;> by_cases c4 : p.2 = a₁ <;>
        simp_all

/-- **`β₂(Φ_G) = 1`** (`lem:beta`).

The constants valid for the edge-Kraus family of a graph with at least one edge
are exactly the reals `≥ 1`.  The extremizer of `Sharp.lean`, read at the two
endpoints of any one edge, pairs to `2` against that edge and to `0` against
every other, so the Choi form is `4` against `hsNormSq = 2`. -/
theorem choiTwoBound_graphKraus_iff {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {a₀ a₁ : U} (hmem : (a₀, a₁) ∈ E) (β : ℝ) :
    ChoiTwoBound (choiOf (graphKraus E)) β ↔ 1 ≤ β := by
  have ha : a₀ < a₁ := hE _ hmem
  have hattain : ChoiTwoAttained (choiOf (graphKraus E)) 1 := by
    refine choiTwoAttained_of_sharpWit
      (a₀ := a₀) (a₁ := a₁) (b₀ := (0 : Fin 2)) (b₁ := 1)
      (sharpWit_ne_zero (ne_of_lt (by decide : (0 : Fin 2) < 1))) ?_
    rw [re_qform_choiOf, hsNormSq_sharpWit (ne_of_lt (by decide : (0 : Fin 2) < 1))]
    rw [Finset.sum_eq_single (⟨(a₀, a₁), hmem⟩ : {p : U × U // p ∈ E})]
    · rw [← hsInner_eq_inner, graphKraus, hsInner_edgeKraus_sharpWit (hE _ hmem) ha, if_pos rfl]
      norm_num [Complex.normSq_apply]
    · rintro ⟨q, hq⟩ _ hne
      have hq' : q ≠ (a₀, a₁) := fun h => hne (Subtype.ext h)
      rw [← hsInner_eq_inner, graphKraus, hsInner_edgeKraus_sharpWit (hE _ hq) ha, if_neg hq']
      simp
    · simp
  exact ⟨fun h => le_of_choiTwoAttained hattain h,
    fun h => choiTwoBound_mono (choiTwoBound_graphKraus hE) h⟩

end GraphBeta

end RankR
