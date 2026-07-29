/-
Placement of a matrix on the first factor of a product.

For an operator `A` on `W`, `placeT A` is `A ⊗ I_T` on `W × T`.  The
definition is accompanied by its linearity, contraction, and conjugation
formulas.
-/
import RankR.Library.Conventions

namespace RankR

open Matrix Finset ComplexConjugate

section MatrixProducts

variable {W : Type*} [Fintype W]

/-- Entrywise form of the conjugation `Y ↦ A Y Aᴴ`. -/
theorem mul_mul_conjTranspose_apply (A Y : Matrix W W ℂ) (x y : W) :
    (A * Y * Aᴴ) x y = ∑ u, ∑ v, A x u * Y u v * conj (A y v) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Finset.sum_mul]
  exact Finset.sum_comm

end MatrixProducts

section PlaceT

variable {W T : Type*} [DecidableEq T]

/-- `A ⊗ I_T`, for `A` on `W`, placed on `W × T`. -/
def placeT (A : Matrix W W ℂ) : Matrix (W × T) (W × T) ℂ :=
  Matrix.of fun x y => if x.2 = y.2 then A x.1 y.1 else 0

@[simp] theorem placeT_apply (A : Matrix W W ℂ) (x y : W × T) :
    placeT A x y = if x.2 = y.2 then A x.1 y.1 else 0 := rfl

/-- Placing an operator on the second factor commutes with finite sums. -/
theorem placeT_sum {ι : Type*} [Fintype ι] (A : ι → Matrix W W ℂ) :
    placeT (T := T) (∑ i, A i) = ∑ i, placeT (T := T) (A i) := by
  ext x y
  simp only [placeT_apply, Matrix.sum_apply]
  split_ifs
  · rfl
  · exact Finset.sum_const_zero.symm

/-- Placing an operator on the second factor commutes with scalar multiplication. -/
theorem placeT_smul (c : ℂ) (A : Matrix W W ℂ) :
    placeT (T := T) (c • A) = c • placeT (T := T) A := by
  ext x y
  simp only [placeT_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_zero]

variable [Fintype W] [Fintype T]

/-- Contracting `placeT N` on the left collapses the second-factor sum. -/
theorem sum_placeT_left (N : Matrix W W ℂ) (x : W × T) (F : W × T → ℂ) :
    ∑ u, placeT N x u * F u = ∑ q : W, N x.1 q * F (q, x.2) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [placeT_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Contracting `placeT N` on the right collapses the second-factor sum. -/
theorem sum_placeT_right (N : Matrix W W ℂ) (y : W × T) (F : W × T → ℂ) :
    ∑ v, F v * conj (placeT N y v) = ∑ q' : W, F (q', y.2) * conj (N y.1 q') := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [placeT_apply, apply_ite conj, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- Entries of `placeT N · Y · (placeT N)ᴴ`. -/
theorem placeT_conj_apply (N : Matrix W W ℂ) (Y : Matrix (W × T) (W × T) ℂ)
    (x y : W × T) :
    (placeT (T := T) N * Y * (placeT (T := T) N)ᴴ) x y
      = ∑ q : W, ∑ q' : W, N x.1 q * Y (q, x.2) (q', y.2) * conj (N y.1 q') := by
  have h : ∀ u : W × T, ∑ v, placeT N x u * Y u v * conj (placeT N y v)
      = placeT N x u * ∑ q' : W, Y u (q', y.2) * conj (N y.1 q') := by
    intro u
    have h2 := sum_placeT_right N y (fun v => Y u v)
    calc ∑ v, placeT N x u * Y u v * conj (placeT N y v)
        = placeT N x u * ∑ v, Y u v * conj (placeT N y v) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ = placeT N x u * ∑ q' : W, Y u (q', y.2) * conj (N y.1 q') := by rw [h2]
  calc (placeT (T := T) N * Y * (placeT (T := T) N)ᴴ) x y
      = ∑ u, ∑ v, placeT N x u * Y u v * conj (placeT N y v) :=
        mul_mul_conjTranspose_apply _ _ _ _
    _ = ∑ u, placeT N x u * ∑ q' : W, Y u (q', y.2) * conj (N y.1 q') :=
        Finset.sum_congr rfl fun u _ => h u
    _ = ∑ q : W, N x.1 q * ∑ q' : W, Y (q, x.2) (q', y.2) * conj (N y.1 q') :=
        sum_placeT_left N x _
    _ = ∑ q : W, ∑ q' : W, N x.1 q * Y (q, x.2) (q', y.2) * conj (N y.1 q') :=
        Finset.sum_congr rfl fun q _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q' _ => by ring

end PlaceT

end RankR
