/-
The finite-coordinate Choi--Jamiołkowski interface.

This file keeps the map notion independent of block positivity: an `r`-positive
map is defined by positivity of its actual `Fin r` ampliation.  The bridge to
`IsBlockPositive` is proved from a finite-matrix rank factorization and a
positive-semidefinite square decomposition.
-/
import RankR.Applications

namespace RankR

open Matrix Finset ComplexConjugate
open scoped ComplexOrder MatrixOrder

section ChoiMap

variable {I O A : Type*} [Fintype I] [Fintype O] [Fintype A]
  [DecidableEq I] [DecidableEq O] [DecidableEq A]

/-- The coordinate map reconstructed from a Choi matrix. -/
noncomputable def mapOfChoi
    (M : Matrix (O × I) (O × I) ℂ) (X : Matrix I I ℂ) : Matrix O O ℂ :=
  Matrix.of fun o p => ∑ i, ∑ j, X i j * M (o, i) (p, j)

theorem mapChoi_mapOfChoi (M : Matrix (O × I) (O × I) ℂ) :
    mapChoi (mapOfChoi M) = M := by
  ext ⟨o, i⟩ ⟨p, j⟩
  simp only [mapChoi, mapOfChoi, Matrix.of_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      have hjk : j ≠ k := Ne.symm hkj
      simp [hjk]
    · simp
  · intro k _ hki
    have hik : i ≠ k := Ne.symm hki
    simp [hik]
  · simp

theorem mapOfChoi_add (M : Matrix (O × I) (O × I) ℂ)
    (X Y : Matrix I I ℂ) :
    mapOfChoi M (X + Y) = mapOfChoi M X + mapOfChoi M Y := by
  ext o p
  simp only [mapOfChoi, Matrix.of_apply, Matrix.add_apply, add_mul,
    Finset.sum_add_distrib]

theorem mapOfChoi_smul (M : Matrix (O × I) (O × I) ℂ)
    (c : ℂ) (X : Matrix I I ℂ) :
    mapOfChoi M (c • X) = c • mapOfChoi M X := by
  ext o p
  simp only [mapOfChoi, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

/-- The map reconstructed from a Choi matrix, bundled as a complex-linear map. -/
noncomputable def mapOfChoiLinear
    (M : Matrix (O × I) (O × I) ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun := mapOfChoi M
  map_add' := mapOfChoi_add M
  map_smul' := mapOfChoi_smul M

theorem mapOfChoi_conjTranspose
    {M : Matrix (O × I) (O × I) ℂ} (hM : M.IsHermitian)
    (X : Matrix I I ℂ) :
    mapOfChoi M Xᴴ = (mapOfChoi M X)ᴴ := by
  ext o p
  simp only [mapOfChoi, Matrix.of_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => ?_
  rw [← hM.apply (o, i) (p, j)]
  simp [RCLike.star_def]

/-- The coordinate ampliation `id_A ⊗ Φ`, written as a matrix of blocks. -/
noncomputable def mapAmplification
    (Φ : Matrix I I ℂ → Matrix O O ℂ)
    (X : Matrix (A × I) (A × I) ℂ) :
    Matrix (A × O) (A × O) ℂ :=
  Matrix.of fun ao bp =>
    Φ (Matrix.of fun i j => X (ao.1, i) (bp.1, j)) ao.2 bp.2

/-- The ampliation of a linear matrix map, bundled as a linear map in its
matrix input. -/
noncomputable def mapAmplificationLinear
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    Matrix (A × I) (A × I) ℂ →ₗ[ℂ] Matrix (A × O) (A × O) ℂ where
  toFun := mapAmplification (A := A) Φ
  map_add' := by
    intro X Y
    ext ao bp
    simp only [mapAmplification, Matrix.of_apply, Matrix.add_apply]
    have hblock :
        Matrix.of (fun i j => X (ao.1, i) (bp.1, j) + Y (ao.1, i) (bp.1, j))
          = Matrix.of (fun i j => X (ao.1, i) (bp.1, j))
            + Matrix.of (fun i j => Y (ao.1, i) (bp.1, j)) := by
      ext i j
      rfl
    rw [hblock, map_add, Matrix.add_apply]
  map_smul' := by
    intro c X
    ext ao bp
    simp only [mapAmplification, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    have hblock :
        Matrix.of (fun i j => c * X (ao.1, i) (bp.1, j))
          = c • Matrix.of (fun i j => X (ao.1, i) (bp.1, j)) := by
      ext i j
      rfl
    rw [hblock, map_smul, Matrix.smul_apply, smul_eq_mul]
    simp

/-- Positivity of the actual `Fin r` ampliation of a coordinate matrix map. -/
def IsMapRPositive (r : ℕ)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  ∀ X : Matrix (Fin r × I) (Fin r × I) ℂ, X.PosSemidef →
    (mapAmplification (A := Fin r) Φ X).PosSemidef

theorem mapAmplification_mapOfChoi_isHermitian
    {M : Matrix (O × I) (O × I) ℂ} (hM : M.IsHermitian)
    {X : Matrix (A × I) (A × I) ℂ} (hX : X.IsHermitian) :
    (mapAmplification (A := A) (mapOfChoi M) X).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext ⟨a, o⟩ ⟨b, p⟩
  let B : Matrix I I ℂ := Matrix.of fun i j => X (a, i) (b, j)
  have hblock :
      Matrix.of (fun i j => X (b, i) (a, j)) = Bᴴ := by
    ext i j
    exact (hX.apply (b, i) (a, j)).symm
  simp only [Matrix.conjTranspose_apply, mapAmplification, Matrix.of_apply,
    RCLike.star_def]
  rw [hblock, mapOfChoi_conjTranspose hM]
  simp [B, Matrix.conjTranspose_apply, RCLike.star_def]

/-- Contract an ampliation input vector and an output test vector to the
matrix tested against the Choi operator. -/
noncomputable def choiContraction
    (x : A × I → ℂ) (y : A × O → ℂ) : Matrix O I ℂ :=
  Matrix.of fun o i => ∑ a, y (a, o) * conj (x (a, i))

theorem rank_choiContraction_le_card
    (x : A × I → ℂ) (y : A × O → ℂ) :
    (choiContraction x y).rank ≤ Fintype.card A := by
  let Y : Matrix O A ℂ := Matrix.of fun o a => y (a, o)
  let X : Matrix A I ℂ := Matrix.of fun a i => conj (x (a, i))
  have hmul : choiContraction x y = Y * X := by
    ext o i
    simp [choiContraction, Y, X, Matrix.mul_apply]
  rw [hmul]
  exact (Matrix.rank_mul_le_left Y X).trans (Matrix.rank_le_card_width Y)

private theorem sum6_choi_perm
    {A O I M : Type*} [Fintype A] [Fintype O] [Fintype I]
    [AddCommMonoid M] (F : A → O → A → O → I → I → M) :
    (∑ a, ∑ o, ∑ b, ∑ p, ∑ i, ∑ j, F a o b p i j)
      = ∑ o, ∑ i, ∑ p, ∑ j, ∑ b, ∑ a, F a o b p i j := by
  have hL :
      (∑ a, ∑ o, ∑ b, ∑ p, ∑ i, ∑ j, F a o b p i j)
        = ∑ z : A × O × A × O × I × I,
            F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  have hR :
      (∑ o, ∑ i, ∑ p, ∑ j, ∑ b, ∑ a, F a o b p i j)
        = ∑ z : O × I × O × I × A × A,
            F z.2.2.2.2.2 z.1 z.2.2.2.2.1 z.2.2.1 z.2.1 z.2.2.2.1 := by
    simp only [Fintype.sum_prod_type]
  rw [hL, hR]
  exact Fintype.sum_equiv
    { toFun := fun z : A × O × A × O × I × I =>
        (z.2.1, z.2.2.2.2.1, z.2.2.2.1, z.2.2.2.2.2, z.2.2.1, z.1)
      invFun := fun z : O × I × O × I × A × A =>
        (z.2.2.2.2.2, z.1, z.2.2.2.2.1, z.2.2.1, z.2.1, z.2.2.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun _ => rfl)

/-- A rank-one ampliation test is exactly the Choi quadratic form of the
contracted matrix. -/
theorem qform_mapAmplification_mapOfChoi_rankOne
    (M : Matrix (O × I) (O × I) ℂ)
    (x : EuclideanSpace ℂ (A × I)) (y : EuclideanSpace ℂ (A × O)) :
    qform (mapAmplification (A := A) (mapOfChoi M) (rankOne x x)) y
      = qform M (vec (choiContraction x y)) := by
  simp only [qform, mapAmplification, mapOfChoi, Matrix.of_apply, rankOne,
    vec_apply, choiContraction, map_sum, map_mul, Complex.conj_conj,
    Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
  ring_nf
  rw [sum6_choi_perm (fun a o b p i j =>
    conj (y (a, o)) * x (a, i) * conj (x (b, j)) * M (o, i) (p, j) * y (b, p))]
  refine Finset.sum_congr rfl fun o _ =>
    Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun p _ =>
        Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun a _ => ?_
  ring

/-- A positive-semidefinite square is a sum of rank-one matrices formed from
the conjugates of its rows. -/
theorem sum_rankOne_conjRow_eq_conjTranspose_mul
    (B : Matrix (A × I) (A × I) ℂ) :
    (∑ k : A × I,
        rankOne
          (WithLp.toLp 2 fun p => conj (B k p))
          (WithLp.toLp 2 fun p => conj (B k p)))
      = Bᴴ * B := by
  ext p q
  simp [rankOne, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def]

private theorem dotProduct_mulVec_eq_qform
    {W : Type*} [Fintype W] (M : Matrix W W ℂ) (x : W → ℂ) :
    star x ⬝ᵥ (M *ᵥ x) = qform M (WithLp.toLp 2 x) := by
  simp [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- Block positivity makes every rank-one positive input remain positive under
the corresponding ampliation. -/
theorem mapAmplification_mapOfChoi_rankOne_posSemidef
    {W : Type*} [Fintype W] [DecidableEq W]
    {M : Matrix (W × W) (W × W) ℂ} (hM : M.IsHermitian)
    (hblock : IsBlockPositive (Fintype.card A) M)
    (x : EuclideanSpace ℂ (A × W)) :
    (mapAmplification (A := A) (mapOfChoi M) (rankOne x x)).PosSemidef := by
  have hxHerm : (rankOne x x).IsHermitian := by
    simpa [Matrix.IsHermitian] using rankOne_conjTranspose x x
  have houtHerm :=
    mapAmplification_mapOfChoi_isHermitian (A := A) hM hxHerm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg houtHerm ?_
  intro y
  rw [dotProduct_mulVec_eq_qform]
  apply Complex.nonneg_iff.mpr
  constructor
  · rw [qform_mapAmplification_mapOfChoi_rankOne]
    exact hblock (choiContraction x (WithLp.toLp 2 y))
      (rank_choiContraction_le_card x (WithLp.toLp 2 y))
  · have him := houtHerm.im_star_dotProduct_mulVec_self y
    rw [dotProduct_mulVec_eq_qform] at him
    exact him.symm

/-- The Choi block-positivity condition implies positivity of the full
ampliation, not only of pure inputs. -/
theorem isMapRPositive_mapOfChoi_of_isBlockPositive
    {W : Type*} [Fintype W] [DecidableEq W]
    {r : ℕ} {M : Matrix (W × W) (W × W) ℂ} (hM : M.IsHermitian)
    (hblock : IsBlockPositive r M) :
    IsMapRPositive r (mapOfChoiLinear M) := by
  intro X hX
  obtain ⟨B, hB⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  have hB' : X = Bᴴ * B := by
    simpa [star_eq_conjTranspose] using hB
  rw [hB', ← sum_rankOne_conjRow_eq_conjTranspose_mul]
  change
    (mapAmplificationLinear (A := Fin r) (mapOfChoiLinear M)
      (∑ k : Fin r × W,
        rankOne
          (WithLp.toLp 2 fun p => conj (B k p))
          (WithLp.toLp 2 fun p => conj (B k p)))).PosSemidef
  rw [map_sum]
  exact (Finset.sum_nonneg fun k _ =>
    (mapAmplification_mapOfChoi_rankOne_posSemidef
      hM (by simpa using hblock)
      (WithLp.toLp 2 fun p => conj (B k p))).nonneg).posSemidef

/-- Positivity of the ampliation implies Choi block positivity, using the
rank factorization through the ancilla. -/
theorem isBlockPositive_of_isMapRPositive_mapOfChoi
    {W : Type*} [Fintype W] [DecidableEq W]
    {r : ℕ} {M : Matrix (W × W) (W × W) ℂ}
    (hmap : IsMapRPositive r (mapOfChoiLinear M)) :
    IsBlockPositive r M := by
  intro C hrank
  have hcard : C.rank ≤ Fintype.card (Fin r) := by simpa using hrank
  obtain ⟨Y, X, hYX⟩ :=
    (rank_le_card_iff_exists_mul (A := Fin r) C).mp hcard
  let x : EuclideanSpace ℂ (Fin r × W) :=
    WithLp.toLp 2 fun p => conj (X p.1 p.2)
  let y : EuclideanSpace ℂ (Fin r × W) :=
    WithLp.toLp 2 fun p => Y p.2 p.1
  have hcontract : choiContraction x y = C := by
    rw [← hYX]
    ext o i
    simp [choiContraction, x, y, Matrix.mul_apply]
  have hxpos : (rankOne x x).PosSemidef := by
    have hrankOne :
        rankOne x x =
          Matrix.vecMulVec (x : Fin r × W → ℂ) (star (x : Fin r × W → ℂ)) := by
      ext p q
      simp [rankOne, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def]
    rw [hrankOne]
    exact Matrix.posSemidef_vecMulVec_self_star (x : Fin r × W → ℂ)
  have hout := hmap (rankOne x x) hxpos
  have hq := hout.dotProduct_mulVec_nonneg (y : Fin r × W → ℂ)
  rw [dotProduct_mulVec_eq_qform] at hq
  change 0 ≤ qform
    (mapAmplification (A := Fin r) (mapOfChoi M) (rankOne x x)) y at hq
  rw [qform_mapAmplification_mapOfChoi_rankOne, hcontract] at hq
  exact (Complex.nonneg_iff.mp hq).1

/-- Finite-dimensional Choi--Jamiołkowski equivalence for the coordinate
notions used in the development. -/
theorem isMapRPositive_mapOfChoi_iff_isBlockPositive
    {W : Type*} [Fintype W] [DecidableEq W]
    {r : ℕ} {M : Matrix (W × W) (W × W) ℂ} (hM : M.IsHermitian) :
    IsMapRPositive r (mapOfChoiLinear M) ↔ IsBlockPositive r M :=
  ⟨isBlockPositive_of_isMapRPositive_mapOfChoi,
    isMapRPositive_mapOfChoi_of_isBlockPositive hM⟩

end ChoiMap

section ProductReductionMaps

variable {U V : Type*} [Fintype U] [Fintype V]
  [DecidableEq U] [DecidableEq V]

/-- Coordinate tensor product of two matrix maps, defined by its action on
matrix units and extended linearly. -/
noncomputable def tensorMatrixMap
    (Φ : Matrix U U ℂ → Matrix U U ℂ)
    (Ψ : Matrix V V ℂ → Matrix V V ℂ)
    (X : Matrix (U × V) (U × V) ℂ) :
    Matrix (U × V) (U × V) ℂ :=
  Matrix.of fun uv pq =>
    ∑ i : U × V, ∑ j : U × V,
      X i j * Φ (Matrix.single i.1 j.1 1) uv.1 pq.1
        * Ψ (Matrix.single i.2 j.2 1) uv.2 pq.2

/-- Reconstructing a map from the regrouped tensor of two Choi matrices gives
the coordinate tensor product of the maps. -/
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

/-- The tensor product of the two reduction pencils, as a linear coordinate
matrix map. -/
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

/-- The asymmetric map-positivity classification at every positive rank in
equal local dimensions. -/
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
