/-
The one-factor reduction pencil and its Choi matrix: the rank--trace
inequality as block positivity, and the completely-positive parameter range.
-/
import RankR.Library.Matrix.Rank
import RankR.Library.Quantum.BlockPositive
import RankR.Library.Quantum.ChoiMap
import RankR.Library.Quantum.MaximallyEntangled
import Mathlib.Analysis.Matrix.Order

namespace RankR

open Matrix Finset
open scoped ComplexOrder

/-- The one-factor reduction pencil `R_{-a}(X) = Tr(X)I - aX`. -/
noncomputable def reductionMap {T : Type*} [Fintype T] [DecidableEq T]
    (a : ℝ) (X : Matrix T T ℂ) : Matrix T T ℂ :=
  X.trace • 1 - (a : ℂ) • X

/-- The Choi matrix `I - a|Ω⟩⟨Ω|` of the reduction pencil
`R_{-a}(X) = Tr(X)I - aX`. -/
noncomputable def reductionChoi {T : Type*} [DecidableEq T] (a : ℝ) :
    Matrix (T × T) (T × T) ℂ :=
  1 - (a : ℂ) • singleOmegaChoi

theorem mapChoi_reductionMap {T : Type*} [Fintype T] [DecidableEq T] (a : ℝ) :
    mapChoi (reductionMap (T := T) a) = reductionChoi (T := T) a := by
  ext p q
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  by_cases hkl : k = l
  · subst l
    simp [mapChoi, reductionMap, Matrix.trace_single_eq_same, reductionChoi,
      singleOmegaChoi, rankOne, Matrix.one_apply, Matrix.single_apply, eq_comm]
    split_ifs <;> simp_all
  · simp [mapChoi, reductionMap, Matrix.trace_single_eq_of_ne k l (1 : ℂ) hkl,
      reductionChoi, singleOmegaChoi, rankOne, Matrix.one_apply,
      Matrix.single_apply, hkl, eq_comm]
    split_ifs <;> simp_all

theorem qform_reductionChoi {T : Type*} [Fintype T] [DecidableEq T]
    (a : ℝ) (C : Matrix T T ℂ) :
    qform (reductionChoi (T := T) a) (vec C)
      = ((hsNormSq C - a * Complex.normSq C.trace : ℝ) : ℂ) := by
  rw [reductionChoi, qform_sub, qform_smul, qform_one, singleOmegaChoi,
    qform_rankOne, inner_singleOmegaVec, hsNormSq_eq_norm_sq]
  norm_cast

/-- The reduction witness `I - |Ω⟩⟨Ω|/r` is `r`-block-positive.

This is the one-factor rank--trace inequality in witness form. -/
theorem reductionChoi_inv_isBlockPositive {T : Type*} [Fintype T]
    [DecidableEq T] {r : ℕ} (hr : 0 < r) :
    IsBlockPositive r (reductionChoi (T := T) (1 / (r : ℝ))) := by
  intro C hCrank
  rw [qform_reductionChoi, Complex.ofReal_re, sub_nonneg]
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have htrace :
      Complex.normSq C.trace ≤ (r : ℝ) * hsNormSq C :=
    (normSq_trace_le_rank C).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hCrank)
        (hsNormSq_nonneg C))
  rw [one_div_mul_eq_div, div_le_iff₀ hrR]
  nlinarith

theorem reductionChoi_isHermitian {T : Type*} [DecidableEq T] (a : ℝ) :
    (reductionChoi (T := T) a).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [reductionChoi, singleOmegaChoi, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    rankOne_conjTranspose]

/-- The reduction-pencil Choi matrix is positive semidefinite in its
completely-positive range `0 ≤ a ≤ 1 / dim(T)`. -/
theorem reductionChoi_posSemidef {T : Type*} [Fintype T] [DecidableEq T]
    {a : ℝ} (ha0 : 0 ≤ a) (hT : 0 < Fintype.card T)
    (ha : a ≤ 1 / (Fintype.card T : ℝ)) :
    (reductionChoi (T := T) a).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (reductionChoi_isHermitian a) ?_
  intro x
  let C : Matrix T T ℂ := Matrix.of fun i j => x (i, j)
  have hvec : vec C = WithLp.toLp 2 x := rfl
  have htrace_rank := normSq_trace_le_rank C
  have hrank : (C.rank : ℝ) ≤ Fintype.card T := by
    exact_mod_cast Matrix.rank_le_card_width C
  have hnorm := hsNormSq_nonneg C
  have htrace :
      Complex.normSq C.trace ≤ (Fintype.card T : ℝ) * hsNormSq C :=
    htrace_rank.trans (mul_le_mul_of_nonneg_right hrank hnorm)
  have hcard : (0 : ℝ) < Fintype.card T := by exact_mod_cast hT
  have hacard : a * (Fintype.card T : ℝ) ≤ 1 :=
    (le_div_iff₀ hcard).mp ha
  have hatrace := mul_le_mul_of_nonneg_left htrace ha0
  have hacard_norm := mul_le_mul_of_nonneg_right hacard hnorm
  have hreal : 0 ≤ hsNormSq C - a * Complex.normSq C.trace := by
    rw [sub_nonneg]
    calc
      a * Complex.normSq C.trace
          ≤ a * ((Fintype.card T : ℝ) * hsNormSq C) := hatrace
      _ = (a * (Fintype.card T : ℝ)) * hsNormSq C := by ring
      _ ≤ 1 * hsNormSq C := hacard_norm
      _ = hsNormSq C := one_mul _
  have hdot :
      star x ⬝ᵥ (reductionChoi (T := T) a *ᵥ x)
        = qform (reductionChoi (T := T) a) (WithLp.toLp 2 x) := by
    simp [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [hdot, ← hvec, qform_reductionChoi]
  exact (RCLike.ofReal_nonneg (K := ℂ)).mpr hreal

end RankR
