/-
Theorem 1.1 as an `r`-block-positivity statement.

A vector of Schmidt rank at most `r` across the row:col cut of `L(U ⊗ V)` is
`vec C` for a matrix `C` of rank at most `r`, so `r`-block positivity of an
operator `M` on the doubled space is the assertion that `⟪vec C, M vec C⟫ ≥ 0`
whenever `rank C ≤ r`.  The coordinate bridge is the theorem
`pureSchmidtRank_vec`; the generic rank-`k` Choi formulation is identified with
the direct pure-Schmidt-rank formulation in `Equivalence.lean`.

The operator in question is the Choi operator of `Ψ_r`, built here from four
explicit vectors rather than through a regrouping of tensor factors: the
identity, the maximally entangled vector `Ω` whose overlap with `vec C` is
`Tr C`, and for each pair of indices on one side an indicator whose overlap with
`vec C` is an entry of the corresponding partial trace.  Its quadratic form at
`vec C` is the deficit in Theorem 1.1,

  `r‖C‖₂² + (1/r)|Tr C|² − ‖Tr_U C‖₂² − ‖Tr_V C‖₂²`,

so the two statements are interchangeable (`isBlockPositive_psiChoi` and
`rank_r_partial_trace_of_isBlockPositive`).  Combined with `MapId.lean`, which
identifies `Ψ_r` with `r·R_{−1/r} ⊗ R_{−1/r}`, this is the `a = b = 1/r` corner
of the asymmetric threshold, available without the score theorem.
-/
import RankR.Core.PartialTrace.Main

namespace RankR

open Matrix Finset ComplexConjugate

section BlockPositive

variable {W : Type*} [Fintype W]

/-- **`r`-block positivity.**  By `pureSchmidtRank_vec`, `Schmidt rank ≤ r`
across the row:col cut is exactly the displayed `Matrix.rank ≤ r` condition. -/
def IsBlockPositive (r : ℕ) (M : Matrix (W × W) (W × W) ℂ) : Prop :=
  ∀ C : Matrix W W ℂ, C.rank ≤ r → 0 ≤ (qform M (vec C)).re

end BlockPositive

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-! ## The four test vectors

Each is an indicator, so the definitions and their entries decide equalities
without summing; the overlaps below are where the sums start. -/

/-- `Ω`, the vectorization of the identity: `⟪Ω, vec C⟫ = Tr C`. -/
def omegaVec : EuclideanSpace ℂ ((U × V) × (U × V)) :=
  WithLp.toLp 2 fun X => if X.1 = X.2 then (1 : ℂ) else 0

/-- The indicator reading off the `(b, c)` entry of `Tr_U C`. -/
def gU (b c : V) : EuclideanSpace ℂ ((U × V) × (U × V)) :=
  WithLp.toLp 2 fun X => if X.1.1 = X.2.1 ∧ X.1.2 = b ∧ X.2.2 = c then (1 : ℂ) else 0

/-- The indicator reading off the `(a, a')` entry of `Tr_V C`. -/
def gV (a a' : U) : EuclideanSpace ℂ ((U × V) × (U × V)) :=
  WithLp.toLp 2 fun X => if X.1.2 = X.2.2 ∧ X.1.1 = a ∧ X.2.1 = a' then (1 : ℂ) else 0

@[simp] theorem omegaVec_apply (X : (U × V) × (U × V)) :
    omegaVec X = if X.1 = X.2 then (1 : ℂ) else 0 := rfl

@[simp] theorem gU_apply (b c : V) (X : (U × V) × (U × V)) :
    gU (U := U) b c X = if X.1.1 = X.2.1 ∧ X.1.2 = b ∧ X.2.2 = c then (1 : ℂ) else 0 := rfl

@[simp] theorem gV_apply (a a' : U) (X : (U × V) × (U × V)) :
    gV (V := V) a a' X = if X.1.2 = X.2.2 ∧ X.1.1 = a ∧ X.2.1 = a' then (1 : ℂ) else 0 := rfl

variable [Fintype U] [Fintype V]

theorem inner_omegaVec (C : Matrix (U × V) (U × V) ℂ) :
    inner ℂ (omegaVec (U := U) (V := V)) (vec C) = C.trace := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply]
  have h : ∀ y : U × V, (inner ℂ (omegaVec (U := U) (V := V) (x, y)) (vec C (x, y)) : ℂ)
      = if x = y then C x y else 0 := by
    intro y
    rw [RCLike.inner_apply', omegaVec_apply, vec_apply]
    by_cases hxy : x = y <;> simp [hxy]
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_ite_eq]
  simp

theorem inner_gU (b c : V) (C : Matrix (U × V) (U × V) ℂ) :
    inner ℂ (gU (U := U) b c) (vec C) = ptraceU C b c := by
  rw [PiLp.inner_apply, ptraceU_apply, Fintype.sum_prod_type]
  have h : ∀ x : U × V, ∑ y : U × V,
      (inner ℂ (gU (U := U) b c (x, y)) (vec C (x, y)) : ℂ)
      = if x.2 = b then C x (x.1, c) else 0 := by
    intro x
    rw [Fintype.sum_prod_type]
    have hy : ∀ a : U, ∑ v : V,
        (inner ℂ (gU (U := U) b c (x, (a, v))) (vec C (x, (a, v))) : ℂ)
        = if x.1 = a ∧ x.2 = b then C x (a, c) else 0 := by
      intro a
      have hv : ∀ v : V,
          (inner ℂ (gU (U := U) b c (x, (a, v))) (vec C (x, (a, v))) : ℂ)
          = if v = c then (if x.1 = a ∧ x.2 = b then C x (a, v) else 0) else 0 := by
        intro v
        rw [RCLike.inner_apply', gU_apply, vec_apply]
        by_cases h1 : x.1 = a <;> by_cases h2 : x.2 = b <;> by_cases h3 : v = c <;>
          simp [h1, h2, h3]
      rw [Finset.sum_congr rfl fun v _ => hv v, Finset.sum_ite_eq']
      simp
    rw [Finset.sum_congr rfl fun a _ => hy a]
    have hsplit : ∀ a : U, (if x.1 = a ∧ x.2 = b then C x (a, c) else 0)
        = if x.1 = a then (if x.2 = b then C x (a, c) else 0) else 0 := by
      intro a
      by_cases h1 : x.1 = a <;> by_cases h2 : x.2 = b <;> simp [h1, h2]
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl fun x _ => h x, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hb : ∀ v : V, (if ((a, v) : U × V).2 = b then C (a, v) (a, c) else 0)
      = if v = b then C (a, v) (a, c) else 0 := fun v => rfl
  rw [Finset.sum_congr rfl fun v _ => hb v, Finset.sum_ite_eq']
  simp

theorem inner_gV (a a' : U) (C : Matrix (U × V) (U × V) ℂ) :
    inner ℂ (gV (V := V) a a') (vec C) = ptraceV C a a' := by
  rw [PiLp.inner_apply, ptraceV_apply, Fintype.sum_prod_type]
  have h : ∀ x : U × V, ∑ y : U × V,
      (inner ℂ (gV (V := V) a a' (x, y)) (vec C (x, y)) : ℂ)
      = if x.1 = a then C x (a', x.2) else 0 := by
    intro x
    rw [Fintype.sum_prod_type]
    have hy : ∀ u : U, ∑ v : V,
        (inner ℂ (gV (V := V) a a' (x, (u, v))) (vec C (x, (u, v))) : ℂ)
        = if x.1 = a ∧ u = a' then C x (u, x.2) else 0 := by
      intro u
      have hv : ∀ v : V,
          (inner ℂ (gV (V := V) a a' (x, (u, v))) (vec C (x, (u, v))) : ℂ)
          = if v = x.2 then (if x.1 = a ∧ u = a' then C x (u, v) else 0) else 0 := by
        intro v
        rw [RCLike.inner_apply', gV_apply, vec_apply]
        by_cases h3 : v = x.2
        · subst h3
          by_cases h1 : x.1 = a <;> by_cases h2 : u = a' <;> simp [h1, h2]
        · have h3' : ¬ x.2 = v := fun h => h3 h.symm
          simp [h3, h3']
      rw [Finset.sum_congr rfl fun v _ => hv v, Finset.sum_ite_eq']
      simp
    rw [Finset.sum_congr rfl fun u _ => hy u]
    have hsplit : ∀ u : U, (if x.1 = a ∧ u = a' then C x (u, x.2) else 0)
        = if u = a' then (if x.1 = a then C x (u, x.2) else 0) else 0 := by
      intro u
      by_cases h1 : x.1 = a <;> by_cases h2 : u = a' <;> simp [h1, h2]
    rw [Finset.sum_congr rfl fun u _ => hsplit u, Finset.sum_ite_eq']
    simp
  rw [Finset.sum_congr rfl fun x _ => h x, Fintype.sum_prod_type]
  have hu : ∀ u : U,
      ∑ v : V, (if ((u, v) : U × V).1 = a then C (u, v) (a', ((u, v) : U × V).2) else 0)
      = if u = a then ∑ v : V, C (u, v) (a', v) else 0 := by
    intro u
    by_cases hua : u = a <;> simp [hua]
  rw [Finset.sum_congr rfl fun u _ => hu u, Finset.sum_ite_eq']
  simp

/-! ## The Choi operator of `Ψ_r` -/

/-- `J(Ψ_r)`, assembled from the identity, `|Ω⟩⟨Ω|`, and the two families of
marginal indicators. -/
noncomputable def psiChoi (r : ℕ) :
    Matrix ((U × V) × (U × V)) ((U × V) × (U × V)) ℂ :=
  (r : ℂ) • (1 : Matrix ((U × V) × (U × V)) ((U × V) × (U × V)) ℂ)
    + ((1 / r : ℝ) : ℂ) • rankOne (omegaVec (U := U) (V := V)) omegaVec
    - ∑ p : V × V, rankOne (gU (U := U) p.1 p.2) (gU p.1 p.2)
    - ∑ p : U × U, rankOne (gV (V := V) p.1 p.2) (gV p.1 p.2)

/-- **The quadratic form of `J(Ψ_r)` is the deficit in Theorem 1.1.** -/
theorem re_qform_psiChoi (r : ℕ) (C : Matrix (U × V) (U × V) ℂ) :
    (qform (psiChoi (U := U) (V := V) r) (vec C)).re
      = r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace
        - hsNormSq (ptraceU C) - hsNormSq (ptraceV C) := by
  have hU : (qform (∑ p : V × V, rankOne (gU (U := U) p.1 p.2) (gU p.1 p.2))
      (vec C)).re = hsNormSq (ptraceU C) := by
    rw [qform_sum, Complex.re_sum, hsNormSq, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
      rw [qform_rankOne, Complex.ofReal_re, inner_gU]
  have hV : (qform (∑ p : U × U, rankOne (gV (V := V) p.1 p.2) (gV p.1 p.2))
      (vec C)).re = hsNormSq (ptraceV C) := by
    rw [qform_sum, Complex.re_sum, hsNormSq, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => by
      rw [qform_rankOne, Complex.ofReal_re, inner_gV]
  rw [psiChoi, qform_sub, qform_sub, qform_add, qform_smul, qform_smul, qform_one,
    qform_rankOne, inner_omegaVec, Complex.sub_re, Complex.sub_re, Complex.add_re, hU, hV,
    Complex.mul_re, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [hsNormSq_eq_norm_sq C]

/-- **Theorem 1.1 is the `r`-block positivity of `J(Ψ_r)`**, unconditionally. -/
theorem isBlockPositive_psiChoi (r : ℕ) :
    IsBlockPositive r (psiChoi (U := U) (V := V) r) := by
  intro C hrank
  rw [re_qform_psiChoi]
  linarith [rank_r_partial_trace C r hrank]

/-- The converse reading: block positivity at `r` returns the bound. -/
theorem rank_r_partial_trace_of_isBlockPositive (r : ℕ)
    (h : IsBlockPositive r (psiChoi (U := U) (V := V) r))
    (C : Matrix (U × V) (U × V) ℂ) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace := by
  have := h C hrank
  rw [re_qform_psiChoi] at this
  linarith

end RankR
