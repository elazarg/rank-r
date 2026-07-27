/-
The `U ⊗ V ⊗ Q` operator layer.

The manuscript's caveat -- "operators are placed on their labeled tensor
factors, regardless of whether those factors are adjacent in the displayed
tensor ordering" -- is exactly the informality Lean will not accept.  Rather
than fight `kroneckerMap` plus reindexing equivalences, we define the two
placements entrywise: `placeUQ A` is `A ⊗ I_V` and `placeVQ B` is `I_U ⊗ B`,
each already living on `(U × V) × Q`.  Entrywise definitions are what the
contraction computations actually consume.
-/
import RankR.Elementary

namespace RankR

open Matrix Finset ComplexConjugate

section QForm

variable {W : Type*} [Fintype W]

/-- The quadratic form `⟪x, A x⟫`, written out so that no `toEuclideanLin`
instance juggling (and no `DecidableEq`) is needed. -/
def qform (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) : ℂ :=
  ∑ p, ∑ q, conj (x p) * A p q * x q

/-- `⟪x, |y⟩⟨y| x⟫ = |⟪y, x⟫|²`. -/
theorem qform_rankOne (y x : EuclideanSpace ℂ W) :
    qform (rankOne y y) x = ((Complex.normSq (inner ℂ y x) : ℝ) : ℂ) := by
  have h : qform (rankOne y y) x
      = (∑ p, conj (x p) * y p) * (∑ q, conj (y q) * x q) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      simp [rankOne]; ring
  rw [h]
  have h1 : (∑ q, conj (y q) * x q) = inner ℂ y x := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun q _ => (RCLike.inner_apply' (y q) (x q)).symm
  have h2 : (∑ p, conj (x p) * y p) = conj (inner ℂ y x) := by
    rw [PiLp.inner_apply, map_sum]
    exact Finset.sum_congr rfl fun p _ => by
      rw [RCLike.inner_apply', map_mul, Complex.conj_conj]; ring
  rw [h1, h2, Complex.normSq_eq_conj_mul_self]

end QForm

section Trace

variable {W : Type*} [Fintype W] {s : ℕ}

/-- `⟪δ_e, δ_d⟫ = conj (Tr C)`, the unnormalized form of `eq:contraction-trace`.
The manuscript's `ψ` is `δ_e / √s`, so this carries all of its content without
introducing the square root. -/
theorem inner_delta_delta (e d : Fin s → EuclideanSpace ℂ W) :
    inner ℂ (delta e) (delta d) = conj ((rankFactor e d).trace) := by
  rw [contraction_trace, PiLp.inner_apply, map_sum, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.inner_apply, map_sum]
  exact Finset.sum_congr rfl fun p _ => by
    simp [RCLike.inner_apply']; ring

/-- **`eq:contraction-trace` in operator form**: `⟪δ, ρ₀ δ⟫ = |Tr C|²`, where
`ρ₀ = |δ_e⟩⟨δ_e|` is the unnormalized `s · ρ`. -/
theorem qform_rho_delta (e d : Fin s → EuclideanSpace ℂ W) :
    qform (rankOne (delta e) (delta e)) (delta d)
      = ((Complex.normSq ((rankFactor e d).trace) : ℝ) : ℂ) := by
  rw [qform_rankOne, inner_delta_delta, Complex.normSq_conj]

end Trace

section Place

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  {s : ℕ}

/-- `A ⊗ I_V`, for `A` on `U × Q`, placed on `(U × V) × Q`. -/
def placeUQ (A : Matrix (U × Fin s) (U × Fin s) ℂ) :
    Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ :=
  Matrix.of fun x y => if x.1.2 = y.1.2 then A (x.1.1, x.2) (y.1.1, y.2) else 0

/-- `I_U ⊗ B`, for `B` on `V × Q`, placed on `(U × V) × Q`. -/
def placeVQ (B : Matrix (V × Fin s) (V × Fin s) ℂ) :
    Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ :=
  Matrix.of fun x y => if x.1.1 = y.1.1 then B (x.1.2, x.2) (y.1.2, y.2) else 0

/-- `ρ_UQ = Tr_V ρ`. -/
def margUQ (R : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ) :
    Matrix (U × Fin s) (U × Fin s) ℂ :=
  Matrix.of fun x y => ∑ b, R ((x.1, b), x.2) ((y.1, b), y.2)

/-- `ρ_VQ = Tr_U ρ`. -/
def margVQ (R : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ) :
    Matrix (V × Fin s) (V × Fin s) ℂ :=
  Matrix.of fun x y => ∑ a, R ((a, x.1), x.2) ((a, y.1), y.2)

/-- Expansion of the `U`-marginal quadratic form.  The `if b = b'` of `placeUQ`
collapses the `b'` sum; what is left is a six-fold sum in the order `qform`
produces it. -/
theorem qform_placeUQ_expand (y x : EuclideanSpace ℂ ((U × V) × Fin s)) :
    qform (placeUQ (margUQ (rankOne y y))) x
      = ∑ a, ∑ b, ∑ i, ∑ a', ∑ i', ∑ c,
          conj (x ((a, b), i)) * y ((a, c), i) *
            (conj (y ((a', c), i')) * x ((a', b), i')) := by
  simp only [qform, placeUQ, margUQ, rankOne, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_ite_eq Finset.univ b]
  simp only [Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **`eq:contraction-U` in operator form**: `⟪δ, (ρ_UQ ⊗ I_V) δ⟫ = ‖Tr_U C‖₂²`,
with `ρ₀ = |δ_e⟩⟨δ_e|` the unnormalized `s · ρ`. -/
theorem qform_margUQ (e d : Fin s → EuclideanSpace ℂ (U × V)) :
    qform (placeUQ (margUQ (rankOne (delta e) (delta e)))) (delta d)
      = ((hsNormSq (ptraceU (rankFactor e d)) : ℝ) : ℂ) := by
  have hL : qform (placeUQ (margUQ (rankOne (delta e) (delta e)))) (delta d)
      = ∑ i, ∑ i', ∑ a, ∑ a',
          (∑ c, e i (a, c) * conj (e i' (a', c))) *
          (∑ b, conj (d i (a, b)) * d i' (a', b)) := by
    rw [qform_placeUQ_expand, sum6_perm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by
      simp only [delta_apply]; ring
  rw [hL, hsNormSq_ptraceU_rankFactor, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

/-- Expansion of the `V`-marginal quadratic form; here the `if a = a'` of
`placeVQ` collapses the `a'` sum. -/
theorem qform_placeVQ_expand (y x : EuclideanSpace ℂ ((U × V) × Fin s)) :
    qform (placeVQ (margVQ (rankOne y y))) x
      = ∑ a, ∑ b, ∑ i, ∑ b', ∑ i', ∑ c,
          conj (x ((a, b), i)) * y ((c, b), i) *
            (conj (y ((c, b'), i')) * x ((a, b'), i')) := by
  simp only [qform, placeVQ, margVQ, rankOne, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_ite_eq Finset.univ a]
  simp only [Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **`eq:contraction-V` in operator form**. -/
theorem qform_margVQ (e d : Fin s → EuclideanSpace ℂ (U × V)) :
    qform (placeVQ (margVQ (rankOne (delta e) (delta e)))) (delta d)
      = ((hsNormSq (ptraceV (rankFactor e d)) : ℝ) : ℂ) := by
  have hL : qform (placeVQ (margVQ (rankOne (delta e) (delta e)))) (delta d)
      = ∑ i, ∑ i', ∑ b, ∑ b',
          (∑ c, e i (c, b) * conj (e i' (c, b'))) *
          (∑ a, conj (d i (a, b)) * d i' (a, b')) := by
    rw [qform_placeVQ_expand, sum6_perm']
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by
      simp only [delta_apply]; ring
  rw [hL, hsNormSq_ptraceV_rankFactor, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

end Place

end RankR
