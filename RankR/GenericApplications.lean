/-
Generic finite-coordinate consequences of block positivity.

The main development usually uses the square bipartition `W : W`.  The
positive-map semidefinite cut in `app:generic` has an arbitrary ancilla, so this
file first gives the same pure-state decomposition definition for an `A : B`
bipartition.  It then proves directly that a Choi operator which is
`r`-block-positive maps every such Schmidt-number-`r` positive operator to a
positive semidefinite matrix, even when the ancilla has more than `r`
coordinates.
-/
import RankR.TraceSeparation
import RankR.MapPos

namespace RankR

open Matrix Finset ComplexConjugate
open scoped ComplexOrder MatrixOrder

/-! ## Schmidt number across a rectangular bipartition -/

section SchmidtNumberBetween

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Mixed-state Schmidt number at most `r` across the coordinate bipartition
`A : B`.  The coefficient matrix of each pure vector is rectangular. -/
def SchmidtNumberLEBetween (r : ℕ)
    (ρ : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ n : ℕ, ∃ C : Fin n → Matrix A B ℂ,
    (∀ i, (C i).rank ≤ r) ∧
      ρ = ∑ i, rankOne (vec (C i)) (vec (C i))

/-- The square-bipartition definition used by the trace-separation
development is the corresponding instance of `SchmidtNumberLEBetween`. -/
theorem schmidtNumberLEBetween_self_iff {r : ℕ}
    {ρ : Matrix (B × B) (B × B) ℂ} :
    SchmidtNumberLEBetween (A := B) (B := B) r ρ ↔ SchmidtNumberLE r ρ :=
  Iff.rfl

end SchmidtNumberBetween

/-! ## Extending an `r`-positive map to arbitrary Schmidt-rank-`r` inputs -/

section PositiveMapCut

variable {A W : Type*} [Fintype A] [Fintype W]
  [DecidableEq A] [DecidableEq W]

/-- Contracting a vectorized rank-at-most-`r` coefficient matrix against an
arbitrary output vector still produces a Choi test matrix of rank at most
`r`.  The proof factors the coefficient matrix through `Fin r`; this avoids
any restriction on the size of the ambient ancilla `A`. -/
theorem rank_choiContraction_vec_le {r : ℕ} (C : Matrix A W ℂ)
    (hrank : C.rank ≤ r) (y : EuclideanSpace ℂ (A × W)) :
    (choiContraction (vec C) y).rank ≤ r := by
  have hcard : C.rank ≤ Fintype.card (Fin r) := by
    simpa using hrank
  obtain ⟨X, Y, hXY⟩ :=
    (rank_le_card_iff_exists_mul (A := Fin r) C).mp hcard
  let Z : Matrix W A ℂ := Matrix.of fun o a => y (a, o)
  have hfac :
      choiContraction (vec C) y =
        (Z * X.map (starRingEnd ℂ)) * Y.map (starRingEnd ℂ) := by
    rw [← hXY]
    ext o i
    simp only [choiContraction, Matrix.of_apply, vec_apply, Matrix.mul_apply,
      Matrix.map_apply, map_sum, map_mul, Z]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
  rw [hfac]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using Matrix.rank_le_card_width
    (Z * X.map (starRingEnd ℂ))

/-- An `r`-block-positive Choi operator sends a pure input of Schmidt rank at
most `r` to a positive semidefinite output, for an ancilla of arbitrary finite
dimension. -/
theorem mapAmplification_mapOfChoi_rankOne_vec_posSemidef
    {r : ℕ} {M : Matrix (W × W) (W × W) ℂ}
    (hM : M.IsHermitian) (hblock : IsBlockPositive r M)
    (C : Matrix A W ℂ) (hrank : C.rank ≤ r) :
    (mapAmplification (A := A) (mapOfChoi M)
      (rankOne (vec C) (vec C))).PosSemidef := by
  have hxHerm : (rankOne (vec C) (vec C)).IsHermitian := by
    simpa [Matrix.IsHermitian] using rankOne_conjTranspose (vec C) (vec C)
  have houtHerm :=
    mapAmplification_mapOfChoi_isHermitian (A := A) hM hxHerm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg houtHerm ?_
  intro y
  rw [show star y ⬝ᵥ
      (mapAmplification (A := A) (mapOfChoi M)
        (rankOne (vec C) (vec C)) *ᵥ y) =
      qform (mapAmplification (A := A) (mapOfChoi M)
        (rankOne (vec C) (vec C))) (WithLp.toLp 2 y) by
      simp [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]]
  apply Complex.nonneg_iff.mpr
  constructor
  · rw [qform_mapAmplification_mapOfChoi_rankOne]
    exact hblock (choiContraction (vec C) (WithLp.toLp 2 y))
      (rank_choiContraction_vec_le C hrank (WithLp.toLp 2 y))
  · have him := houtHerm.im_star_dotProduct_mulVec_self y
    rw [show star y ⬝ᵥ
        (mapAmplification (A := A) (mapOfChoi M)
          (rankOne (vec C) (vec C)) *ᵥ y) =
        qform (mapAmplification (A := A) (mapOfChoi M)
          (rankOne (vec C) (vec C))) (WithLp.toLp 2 y) by
        simp [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]] at him
    exact him.symm

/-- A block-positive Choi operator gives the positive-map semidefinite cut on
every positive operator of Schmidt number at most `r`, with no bound on the
ambient ancilla dimension. -/
theorem mapAmplification_posSemidef_of_schmidtNumberLEBetween
    {r : ℕ} {M : Matrix (W × W) (W × W) ℂ}
    (hM : M.IsHermitian) (hblock : IsBlockPositive r M)
    {ρ : Matrix (A × W) (A × W) ℂ}
    (hρ : SchmidtNumberLEBetween r ρ) :
    (mapAmplification (A := A) (mapOfChoi M) ρ).PosSemidef := by
  obtain ⟨n, C, hCrank, rfl⟩ := hρ
  change
    (mapAmplificationLinear (A := A) (mapOfChoiLinear M)
      (∑ i, rankOne (vec (C i)) (vec (C i)))).PosSemidef
  rw [map_sum]
  exact (Finset.sum_nonneg fun i _ =>
    (mapAmplification_mapOfChoi_rankOne_vec_posSemidef
      hM hblock (C i) (hCrank i)).nonneg).posSemidef

end PositiveMapCut

/-! ## The reduction-product semidefinite cut -/

section ReductionCut

variable {A T : Type*} [Fintype A] [Fintype T]
  [DecidableEq A] [DecidableEq T]

/-- The asymmetric positive-map cut from `cor:positive-map-cut`, in finite
coordinates and for an arbitrary finite ancilla. -/
theorem productReduction_schmidtNumberLE_cut
    {r : ℕ} (hr : 0 < r) (hTtwo : 2 ≤ Fintype.card T)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hab : max a b ≤ 1 / (min r (Fintype.card T) : ℝ))
    {ρ : Matrix (A × (T × T)) (A × (T × T)) ℂ}
    (hρ : SchmidtNumberLEBetween r ρ) :
    (mapAmplification (A := A)
      (productReductionMapLinear (U := T) (V := T) a b) ρ).PosSemidef := by
  have hblock :
      IsBlockPositive r
        (productReductionChoi (U := T) (V := T) a b) :=
    (isBlockPositive_productReductionChoi_iff_max_le_inv_min
      hr hTtwo ha0 hb0).2 hab
  change
    (mapAmplification (A := A)
      (mapOfChoi (productReductionChoi (U := T) (V := T) a b)) ρ).PosSemidef
  exact mapAmplification_posSemidef_of_schmidtNumberLEBetween
    (productReductionChoi_isHermitian a b) hblock hρ

/-- The symmetric specialization
`Λ_r = R_{-1/min(r,d)} ⊗ R_{-1/min(r,d)}`. -/
theorem productReduction_self_schmidtNumberLE_cut
    {r : ℕ} (hr : 0 < r) (hTtwo : 2 ≤ Fintype.card T)
    {ρ : Matrix (A × (T × T)) (A × (T × T)) ℂ}
    (hρ : SchmidtNumberLEBetween r ρ) :
    let s := min r (Fintype.card T)
    (mapAmplification (A := A)
      (productReductionMapLinear (U := T) (V := T)
        (1 / (s : ℝ)) (1 / (s : ℝ))) ρ).PosSemidef := by
  dsimp only
  have hTpos : 0 < Fintype.card T := by omega
  have hspos : 0 < min r (Fintype.card T) := lt_min hr hTpos
  apply productReduction_schmidtNumberLE_cut hr hTtwo
  · positivity
  · positivity
  · simp
  · exact hρ

end ReductionCut

end RankR
