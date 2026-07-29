/-
Positive-map formulations of the product reduction application.
-/
import RankR.Applications.Reduction.Main
import RankR.Library.Quantum.PositiveMaps

namespace RankR

open Matrix Finset

section ProductReductionMaps

variable {U V : Type*} [Fintype U] [Fintype V]
  [DecidableEq U] [DecidableEq V]

/-- Coordinate tensor product of two matrix maps. -/
noncomputable def tensorMatrixMap
    (Φ : Matrix U U ℂ → Matrix U U ℂ)
    (Ψ : Matrix V V ℂ → Matrix V V ℂ)
    (X : Matrix (U × V) (U × V) ℂ) :
    Matrix (U × V) (U × V) ℂ :=
  Matrix.of fun uv pq =>
    ∑ i : U × V, ∑ j : U × V,
      X i j * Φ (Matrix.single i.1 j.1 1) uv.1 pq.1
        * Ψ (Matrix.single i.2 j.2 1) uv.2 pq.2

/-- Reconstructing a map from a regrouped product Choi matrix gives the
coordinate tensor product of the maps. -/
theorem mapOfChoi_regroupChoi_mapChoi
    (Φ : Matrix U U ℂ → Matrix U U ℂ)
    (Ψ : Matrix V V ℂ → Matrix V V ℂ)
    (X : Matrix (U × V) (U × V) ℂ) :
    mapOfChoi (regroupChoi (mapChoi Φ) (mapChoi Ψ)) X
      = tensorMatrixMap Φ Ψ X := by
  ext ⟨u, v⟩ ⟨p, q⟩
  simp [mapOfChoi, tensorMatrixMap, regroupChoi, choiRegroupEquiv,
    mapChoi, Fintype.sum_prod_type]
  simp only [mul_assoc]

/-- The tensor product of two reduction pencils as a linear matrix map. -/
noncomputable def productReductionMapLinear (a b : ℝ) :
    Matrix (U × V) (U × V) ℂ →ₗ[ℂ] Matrix (U × V) (U × V) ℂ :=
  mapOfChoiLinear (productReductionChoi (U := U) (V := V) a b)

theorem productReductionMapLinear_apply (a b : ℝ)
    (X : Matrix (U × V) (U × V) ℂ) :
    productReductionMapLinear (U := U) (V := V) a b X
      = tensorMatrixMap (reductionMap (T := U) a)
          (reductionMap (T := V) b) X := by
  rw [productReductionMapLinear, productReductionChoi_eq_regroup_mapChoi]
  change mapOfChoi
    (regroupChoi (mapChoi (reductionMap (T := U) a))
      (mapChoi (reductionMap (T := V) b))) X
      = tensorMatrixMap (reductionMap (T := U) a)
          (reductionMap (T := V) b) X
  exact mapOfChoi_regroupChoi_mapChoi _ _ _

theorem mapChoi_productReductionMapLinear (a b : ℝ) :
    mapChoi (productReductionMapLinear (U := U) (V := V) a b)
      = productReductionChoi (U := U) (V := V) a b :=
  mapChoi_mapOfChoi _

/-- The asymmetric map-positivity threshold in the rank-constrained range. -/
theorem isMapRPositive_productReductionMapLinear_iff_max_le_inv
    {r : ℕ} (hr : 0 < r)
    (hU : r ≤ Fintype.card U) (hV : r ≤ Fintype.card V)
    (hUtwo : 2 ≤ Fintype.card U) (hVtwo : 2 ≤ Fintype.card V)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    IsMapRPositive r (productReductionMapLinear (U := U) (V := V) a b)
      ↔ max a b ≤ 1 / (r : ℝ) := by
  rw [productReductionMapLinear,
    isMapRPositive_mapOfChoi_iff_isBlockPositive
      (productReductionChoi_isHermitian a b)]
  exact isBlockPositive_productReductionChoi_iff_max_le_inv
    hr hU hV hUtwo hVtwo ha0 hb0

/-- The asymmetric map-positivity classification in equal local dimensions. -/
theorem isMapRPositive_productReductionMapLinear_iff_max_le_inv_min
    {T : Type*} [Fintype T] [DecidableEq T] {r : ℕ}
    (hr : 0 < r) (hTtwo : 2 ≤ Fintype.card T)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    IsMapRPositive r (productReductionMapLinear (U := T) (V := T) a b)
      ↔ max a b ≤ 1 / (min r (Fintype.card T) : ℝ) := by
  rw [productReductionMapLinear,
    isMapRPositive_mapOfChoi_iff_isBlockPositive
      (productReductionChoi_isHermitian a b)]
  exact isBlockPositive_productReductionChoi_iff_max_le_inv_min
    hr hTtwo ha0 hb0

/-- The symmetric tensor-square map classification at every positive rank. -/
theorem isMapRPositive_productReductionMapLinear_self_iff_le_inv_min
    {T : Type*} [Fintype T] [DecidableEq T] {r : ℕ}
    (hr : 0 < r) (hTtwo : 2 ≤ Fintype.card T)
    {t : ℝ} (ht0 : 0 ≤ t) :
    IsMapRPositive r (productReductionMapLinear (U := T) (V := T) t t)
      ↔ t ≤ 1 / (min r (Fintype.card T) : ℝ) := by
  simpa using
    (isMapRPositive_productReductionMapLinear_iff_max_le_inv_min
      (T := T) hr hTtwo ht0 ht0)

end ProductReductionMaps

end RankR
