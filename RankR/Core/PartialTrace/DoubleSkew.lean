/-
The contraction identity connecting the double-skew Kraus map to the
partial-trace operator.
-/
import RankR.Core.DoubleSkew.Map
import RankR.Core.PartialTrace.FromOperator

namespace RankR

open Matrix Finset ComplexConjugate

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

/-- The value of `Phi4` on the partially transposed rank-one operator built from
an orthonormal frame. -/
theorem Phi4_ptransposeUV_rankOne (e : Fin s → EuclideanSpace ℂ (U × V))
    (he : Orthonormal ℂ e) :
    Phi4 (ptransposeUV (rankOne (delta e) (delta e)))
      = (4 : ℂ) • ((1 : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ)
          - placeUQ (margUQ (rankOne (delta e) (delta e)))
          - placeVQ (margVQ (rankOne (delta e) (delta e)))
          + rankOne (delta e) (delta e)) := by
  have horth : ∀ i i' : Fin s,
      ∑ q : U × V, e i q * conj (e i' q) = if i = i' then (1 : ℂ) else 0 := by
    intro i i'
    calc ∑ q : U × V, e i q * conj (e i' q) = inner ℂ (e i') (e i) := by
          rw [PiLp.inner_apply]
          exact Finset.sum_congr rfl fun q _ => by rw [RCLike.inner_apply']; ring
      _ = if i' = i then 1 else 0 := orthonormal_iff_ite.mp he i' i
      _ = if i = i' then 1 else 0 := by simp [eq_comm]
  ext x y
  rw [Phi4_apply]
  simp only [ptransposeUV_apply, rankOne, Matrix.of_apply, delta_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, placeUQ, placeVQ,
    margUQ, margVQ, Prod.mk.eta]
  rw [horth x.2 y.2]
  have hone : (if x = y then (1 : ℂ) else 0)
      = if x.1.1 = y.1.1 ∧ x.1.2 = y.1.2 then (if x.2 = y.2 then (1 : ℂ) else 0) else 0 := by
    by_cases h1 : x.1.1 = y.1.1 <;> by_cases h2 : x.1.2 = y.1.2 <;>
      by_cases h3 : x.2 = y.2 <;> simp [Prod.ext_iff, h1, h2, h3]
  rw [hone]
  ring

/-- The scaled partial-trace operator rewritten in terms of `Phi4`. -/
theorem HopScaled_eq (e : Fin s → EuclideanSpace ℂ (U × V)) (he : Orthonormal ℂ e) :
    (4 : ℂ) • HopScaled e
      = ((4 * s * (s - 1) : ℂ)) • (1 : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ)
        - ((4 * (s - 1) : ℂ)) • rankOne (delta e) (delta e)
        + (s : ℂ) • Phi4 (ptransposeUV (rankOne (delta e) (delta e))) := by
  rw [Phi4_ptransposeUV_rankOne e he, HopScaled]
  ext p q
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply]
  ring

end RankR
