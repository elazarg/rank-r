/-
Rank factorizations of elementary skew and double-skew operators.
-/
import RankR.Core.DoubleSkew.Choi

namespace RankR

open Matrix ComplexConjugate
open scoped Kronecker

section SkewRank

variable {W : Type*} [DecidableEq W]

/-- The two-column factor carrying the range of an elementary skew matrix. -/
noncomputable def skewUnitLeft (a b : W) : Matrix W (Fin 2) ℂ :=
  Matrix.of fun p i => ![eBasis a p, -(eBasis b p)] i

/-- The two-row factor carrying the covectors of an elementary skew matrix. -/
noncomputable def skewUnitRight (a b : W) : Matrix (Fin 2) W ℂ :=
  Matrix.of fun i q => ![conj (eBasis b q), conj (eBasis a q)] i

/-- Every elementary skew matrix factors through a two-dimensional space. -/
theorem skewUnit_eq_mul (a b : W) :
    skewUnit a b = skewUnitLeft a b * skewUnitRight a b := by
  by_cases hab : a = b
  · subst b
    ext p q
    simp only [skewUnit, skewUnitLeft, skewUnitRight, Matrix.mul_apply,
      Matrix.single_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, eBasis_apply,
      apply_ite (starRingEnd ℂ), map_one, map_zero]
    by_cases hqa : q = a <;> by_cases hpa : p = a <;> simp [hqa, hpa]
  · ext p q
    simp only [skewUnit, skewUnitLeft, skewUnitRight, Matrix.mul_apply,
      Matrix.single_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, eBasis_apply,
      apply_ite (starRingEnd ℂ), map_one, map_zero]
    by_cases hpa : p = a <;> by_cases hqb : q = b <;> by_cases hpb : p = b <;>
      by_cases hqa : q = a <;> simp_all [eq_comm]

end SkewRank

section DoubleSkewRank

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- Every scalar multiple of an elementary double-skew Kraus operator has rank
at most four. -/
theorem rank_smul_skewKraus_le_four (c : ℂ) (f : KIdx U V) :
    (c • skewKraus f).rank ≤ 4 := by
  rw [skewKraus, skewUnit_eq_mul, skewUnit_eq_mul, Matrix.mul_kronecker_mul,
    ← Matrix.smul_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.reduceMul] using
      Matrix.rank_le_card_width
        (c • (skewUnitLeft f.1.1 f.1.2 ⊗ₖ skewUnitLeft f.2.1 f.2.2)))

end DoubleSkewRank

end RankR
