/-
Finite operator algebra for the state family and boundary decomposition in
`paper/derivation-schmidt-staircase.tex`.

The matrices are kept in the paper's `A₁B₁A₂B₂` register order.  This file
proves the normalized isotropic white-noise identity, protected and unprotected
witness expectations, the isotropic marginal formula and its one-sided
Schmidt-number obstruction, the global witness obstruction across the stated
Schmidt cut, and the exact boundary operator equality.  It does not assert that
the algebraic product-isotropic space is the range of a Haar twirl, or that the
twirl preserves Schmidt number.
-/
import RankR.Isotropic
import RankR.Staircase

namespace RankR

open Matrix ComplexConjugate
open scoped ComplexOrder Kronecker MatrixOrder

section

variable {U V : Type*} [Fintype U] [Fintype V]
  [DecidableEq U] [DecidableEq V]

/-- Regroup an operator from register order `A₁B₁A₂B₂` to the bipartite
Schmidt-cut order `(A₁A₂):(B₁B₂)`. -/
noncomputable def regroupProductOperator
    (M : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    Matrix ((U × V) × (U × V)) ((U × V) × (U × V)) ℂ :=
  Matrix.reindex (choiRegroupEquiv (U := U) (V := V))
    (choiRegroupEquiv (U := U) (V := V)) M

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
theorem regroupProductOperator_smul
    (c : ℂ)
    (M : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    regroupProductOperator (c • M) = c • regroupProductOperator M := by
  rfl

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
theorem regroupProductOperator_add
    (M N : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    regroupProductOperator (M + N) =
      regroupProductOperator M + regroupProductOperator N := by
  rfl

omit [Fintype U] [Fintype V] in
theorem regroupProductOperator_one :
    regroupProductOperator
        (1 : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) =
      (1 : Matrix ((U × V) × (U × V)) ((U × V) × (U × V)) ℂ) := by
  ext p q
  simp [regroupProductOperator, Matrix.reindex_apply, Matrix.one_apply]

theorem regroupProductOperator_mul
    (M N : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    regroupProductOperator (M * N) =
      regroupProductOperator M * regroupProductOperator N := by
  change
    (Matrix.reindexAlgEquiv ℂ ℂ
      (choiRegroupEquiv (U := U) (V := V))) (M * N) =
      (Matrix.reindexAlgEquiv ℂ ℂ
        (choiRegroupEquiv (U := U) (V := V))) M *
      (Matrix.reindexAlgEquiv ℂ ℂ
        (choiRegroupEquiv (U := U) (V := V))) N
  exact map_mul _ M N

omit [DecidableEq U] [DecidableEq V] in
theorem trace_regroupProductOperator
    (M : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    (regroupProductOperator M).trace = M.trace := by
  simp only [regroupProductOperator, Matrix.trace, Matrix.diag_apply,
    Matrix.reindex_apply]
  simpa using
    (Equiv.sum_comp
      (choiRegroupEquiv (U := U) (V := V))
      (fun q => M
        ((choiRegroupEquiv (U := U) (V := V)).symm q)
        ((choiRegroupEquiv (U := U) (V := V)).symm q))).symm

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
theorem regroupProductOperator_isHermitian
    {M : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ}
    (hM : M.IsHermitian) :
    (regroupProductOperator M).IsHermitian := by
  rw [Matrix.IsHermitian, regroupProductOperator,
    Matrix.conjTranspose_reindex, hM.eq]

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
theorem regroupProductOperator_posSemidef
    {M : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ}
    (hM : M.PosSemidef) :
    (regroupProductOperator M).PosSemidef := by
  rw [regroupProductOperator, Matrix.reindex_apply]
  exact hM.submatrix _

theorem trace_mul_regroupProductOperator
    (M N : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    (regroupProductOperator M * regroupProductOperator N).trace =
      (M * N).trace := by
  rw [← regroupProductOperator_mul, trace_regroupProductOperator]

/-- The product-isotropic seed
`Iso_m(s/m) ⊗ Iso_n(0)`. -/
noncomputable def staircaseSeedState (s : ℝ) :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  biIsotropicState (s / Fintype.card U) 0

/-- The product-isotropic rendering of maximally mixed noise. -/
noncomputable def staircaseWhiteNoiseState :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  biIsotropicState
    (1 / (Fintype.card U : ℝ) ^ 2)
    (1 / (Fintype.card V : ℝ) ^ 2)

/-- The noisy staircase family
`ρ_p = p τ_s + (1-p) I/(mn)^2`. -/
noncomputable def staircaseState (s p : ℝ) :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  (p : ℂ) • staircaseSeedState s
    + ((1 - p : ℝ) : ℂ) • staircaseWhiteNoiseState

/-- The noisy staircase state in the register order of its Schmidt cut. -/
noncomputable def staircaseStateAcrossCut (s p : ℝ) :
    Matrix ((U × V) × (U × V)) ((U × V) × (U × V)) ℂ :=
  regroupProductOperator (staircaseState s p)

/-- Every point below a nonzero mixing parameter `q` is the affine
combination of the point at `q` and white noise with coefficient `p/q`. -/
theorem staircaseState_eq_threshold_whiteNoise_mix
    (s p q : ℝ) (hq : q ≠ 0) :
    staircaseState (U := U) (V := V) s p =
      ((p / q : ℝ) : ℂ) • staircaseState s q
        + ((1 - p / q : ℝ) : ℂ) • staircaseWhiteNoiseState := by
  ext x y
  simp only [staircaseState, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  field_simp [hqC]
  ring

/-- The two-term candidate in the boundary decomposition. -/
noncomputable def staircaseBoundaryState (k α : ℝ) :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  ((1 - α : ℝ) : ℂ) •
      biIsotropicState (k / Fintype.card U) 0
    + (α : ℂ) •
      biIsotropicState
        (1 / (Fintype.card U : ℝ) ^ 2)
        (k / Fintype.card V)

/-- The boundary decomposition in the register order of the Schmidt cut. -/
noncomputable def staircaseBoundaryStateAcrossCut (k α : ℝ) :
    Matrix ((U × V) × (U × V)) ((U × V) × (U × V)) ℂ :=
  regroupProductOperator (staircaseBoundaryState k α)

/-- One factor of the lifted witness, written with the normalized maximally
entangled projection. -/
noncomputable def staircaseWitnessFactor (T : Type*) [Fintype T]
    [DecidableEq T] (k : ℝ) :
    Matrix (T × T) (T × T) ℂ :=
  1 - (((Fintype.card T : ℝ) / k : ℝ) : ℂ) •
    omegaProjection (T := T)

/-- The lifted witness `W_k` in `A₁B₁A₂B₂` register order. -/
noncomputable def staircaseWitness (k : ℝ) :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  (k : ℂ) •
    (staircaseWitnessFactor U k ⊗ₖ staircaseWitnessFactor V k)

/-- The lifted witness in the register order of the Schmidt cut. -/
noncomputable def staircaseWitnessAcrossCut (k : ℝ) :
    Matrix ((U × V) × (U × V)) ((U × V) × (U × V)) ℂ :=
  regroupProductOperator (staircaseWitness k)

/-- The maximally entangled rank-one term on the two product factors, in the
paper's `A₁B₁A₂B₂` register order. -/
noncomputable def staircaseOmegaProduct :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  singleOmegaChoi (T := U) ⊗ₖ singleOmegaChoi (T := V)

/-- The witness obtained when the protected `-id/k` correction is omitted. -/
noncomputable def staircaseUnprotectedWitness (k : ℝ) :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  staircaseWitness k
    + (((k - 1) / k : ℝ) : ℂ) • staircaseOmegaProduct

theorem staircaseWitnessFactor_isHermitian
    {T : Type*} [Fintype T] [DecidableEq T] (k : ℝ) :
    (staircaseWitnessFactor T k).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [staircaseWitnessFactor, omegaProjection, singleOmegaChoi,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    rankOne_conjTranspose]

/-- In positive dimension, the normalized witness factor is the ordinary
reduction Choi matrix at parameter `1/k`. -/
theorem staircaseWitnessFactor_eq_reductionChoi
    {T : Type*} [Fintype T] [DecidableEq T]
    (hT : 0 < Fintype.card T) (k : ℝ) :
    staircaseWitnessFactor T k =
      reductionChoi (T := T) (1 / k) := by
  rw [staircaseWitnessFactor, reductionChoi, omegaProjection, smul_smul]
  congr 1
  norm_cast
  have hd : (Fintype.card T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hT)
  field_simp

theorem staircaseWitness_isHermitian (k : ℝ) :
    (staircaseWitness (U := U) (V := V) k).IsHermitian := by
  have hkr :
      (staircaseWitnessFactor U k ⊗ₖ
        staircaseWitnessFactor V k).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker,
      (staircaseWitnessFactor_isHermitian k).eq,
      (staircaseWitnessFactor_isHermitian k).eq]
  exact hkr.smul (Complex.conj_ofReal k)

theorem staircaseWitnessAcrossCut_isHermitian (k : ℝ) :
    (staircaseWitnessAcrossCut (U := U) (V := V) k).IsHermitian :=
  regroupProductOperator_isHermitian (staircaseWitness_isHermitian k)

/-- After regrouping to the Schmidt cut, the staircase witness is `k` times
the product of two reduction Choi matrices. -/
theorem staircaseWitnessAcrossCut_eq_productReductionChoi
    (hU : 0 < Fintype.card U) (hV : 0 < Fintype.card V) (k : ℝ) :
    staircaseWitnessAcrossCut (U := U) (V := V) k =
      (k : ℂ) •
        productReductionChoi (U := U) (V := V) (1 / k) (1 / k) := by
  rw [staircaseWitnessAcrossCut, staircaseWitness,
    regroupProductOperator_smul, productReductionChoi]
  change
    (k : ℂ) •
        regroupProductOperator
          (staircaseWitnessFactor U k ⊗ₖ
            staircaseWitnessFactor V k) =
      (k : ℂ) •
        regroupProductOperator
          (reductionChoi (T := U) (1 / k) ⊗ₖ
            reductionChoi (T := V) (1 / k))
  rw [staircaseWitnessFactor_eq_reductionChoi hU,
    staircaseWitnessFactor_eq_reductionChoi hV]

/-- The lifted witness is block-positive at its integer level across the
paper's Schmidt cut. -/
theorem staircaseWitnessAcrossCut_isBlockPositive
    {k : ℕ} (hk : 0 < k)
    (hU : k ≤ Fintype.card U) (hV : k ≤ Fintype.card V)
    (hUtwo : 2 ≤ Fintype.card U) (hVtwo : 2 ≤ Fintype.card V) :
    IsBlockPositive k
      (staircaseWitnessAcrossCut (U := U) (V := V) (k : ℝ)) := by
  rw [staircaseWitnessAcrossCut_eq_productReductionChoi
    (by omega) (by omega)]
  have hproduct :
      IsBlockPositive k
        (productReductionChoi (U := U) (V := V)
          (1 / (k : ℝ)) (1 / (k : ℝ))) := by
    apply
      (isBlockPositive_productReductionChoi_iff_max_le_inv
        hk hU hV hUtwo hVtwo (by positivity) (by positivity)).mpr
    simp
  intro C hCrank
  rw [qform_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) (hproduct C hCrank)

omit [Fintype U] [Fintype V] in
theorem staircaseOmegaProduct_isHermitian :
    (staircaseOmegaProduct (U := U) (V := V)).IsHermitian := by
  rw [Matrix.IsHermitian, staircaseOmegaProduct,
    Matrix.conjTranspose_kronecker]
  simp [singleOmegaChoi, rankOne_conjTranspose]

theorem staircaseUnprotectedWitness_isHermitian (k : ℝ) :
    (staircaseUnprotectedWitness (U := U) (V := V) k).IsHermitian := by
  exact Matrix.IsHermitian.add (staircaseWitness_isHermitian k)
    (staircaseOmegaProduct_isHermitian.smul (Complex.conj_ofReal _))

theorem hsInner_staircaseWitnessFactor_isotropicState
    {T : Type*} [Fintype T] [DecidableEq T]
    (hT : 2 ≤ Fintype.card T) (k F : ℝ) :
    hsInner (staircaseWitnessFactor T k) (isotropicState F) =
      ((1 - (Fintype.card T : ℝ) * F / k : ℝ) : ℂ) := by
  rw [staircaseWitnessFactor, hsInner_sub_left, hsInner_one_left,
    trace_isotropicState hT F, hsInner_smul_left,
    hsInner_omegaProjection_isotropicState hT]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

/-- The operator-level trace formula `eq:trace`. -/
theorem hsInner_staircaseWitness_biIsotropicState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (k F G : ℝ) :
    hsInner (staircaseWitness (U := U) (V := V) k)
        (biIsotropicState F G) =
      ((k * (1 - (Fintype.card U : ℝ) * F / k) *
        (1 - (Fintype.card V : ℝ) * G / k) : ℝ) : ℂ) := by
  rw [staircaseWitness, biIsotropicState, hsInner_smul_left,
    hsInner_kron,
    hsInner_staircaseWitnessFactor_isotropicState hU,
    hsInner_staircaseWitnessFactor_isotropicState hV]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

theorem trace_mul_staircaseWitness_biIsotropicState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (k F G : ℝ) :
    (staircaseWitness (U := U) (V := V) k *
        biIsotropicState F G).trace =
      ((k * (1 - (Fintype.card U : ℝ) * F / k) *
        (1 - (Fintype.card V : ℝ) * G / k) : ℝ) : ℂ) := by
  rw [← hsInner_staircaseWitness_biIsotropicState hU hV]
  simp only [hsInner, (staircaseWitness_isHermitian k).eq]

theorem hsInner_staircaseOmegaProduct_biIsotropicState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (F G : ℝ) :
    hsInner staircaseOmegaProduct
        (biIsotropicState (U := U) (V := V) F G) =
      (((Fintype.card U : ℝ) * F *
        ((Fintype.card V : ℝ) * G) : ℝ) : ℂ) := by
  rw [staircaseOmegaProduct, biIsotropicState, hsInner_kron,
    hsInner_singleOmegaChoi_isotropicState hU,
    hsInner_singleOmegaChoi_isotropicState hV]
  push_cast
  rfl

theorem trace_mul_staircaseUnprotectedWitness_biIsotropicState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (k F G : ℝ) :
    (staircaseUnprotectedWitness (U := U) (V := V) k *
        biIsotropicState F G).trace =
      ((k * (1 - (Fintype.card U : ℝ) * F / k) *
          (1 - (Fintype.card V : ℝ) * G / k)
        + (k - 1) / k *
          ((Fintype.card U : ℝ) * F *
            ((Fintype.card V : ℝ) * G)) : ℝ) : ℂ) := by
  rw [← (staircaseUnprotectedWitness_isHermitian k).eq]
  change
    hsInner (staircaseUnprotectedWitness (U := U) (V := V) k)
      (biIsotropicState F G) = _
  rw [staircaseUnprotectedWitness, hsInner_add_left, hsInner_smul_left,
    hsInner_staircaseWitness_biIsotropicState hU hV,
    hsInner_staircaseOmegaProduct_biIsotropicState hU hV]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

theorem hsInner_staircaseWitness_seed
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {k : ℝ} (hk : 1 ≤ k) (s : ℝ) :
    hsInner (staircaseWitness (U := U) (V := V) k)
        (staircaseSeedState s) = ((k - s : ℝ) : ℂ) := by
  rw [staircaseSeedState,
    hsInner_staircaseWitness_biIsotropicState hU hV]
  have hUc : (Fintype.card U : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card U ≠ 0 by omega)
  have hk0 : k ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hk)
  push_cast
  field_simp
  ring

theorem hsInner_staircaseWitness_whiteNoise
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {k : ℝ} (hk : 1 ≤ k) :
    hsInner (staircaseWitness (U := U) (V := V) k)
        staircaseWhiteNoiseState =
      (staircaseGamma (Fintype.card U) (Fintype.card V) k : ℂ) := by
  rw [staircaseWhiteNoiseState,
    hsInner_staircaseWitness_biIsotropicState hU hV]
  have hUc : (Fintype.card U : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card U ≠ 0 by omega)
  have hVc : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card V ≠ 0 by omega)
  have hk0 : k ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hk)
  rw [staircaseGamma]
  push_cast
  field_simp

/-- The exact affine expectation `eq:trace-rho`. -/
theorem hsInner_staircaseWitness_staircaseState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {k : ℝ} (hk : 1 ≤ k) (s p : ℝ) :
    hsInner (staircaseWitness (U := U) (V := V) k)
        (staircaseState s p) =
      (((1 - p) * staircaseGamma (Fintype.card U) (Fintype.card V) k
        - p * (s - k) : ℝ) : ℂ) := by
  rw [staircaseState, hsInner_add_right,
    hsInner_smul_right, hsInner_smul_right,
    hsInner_staircaseWitness_seed hU hV hk,
    hsInner_staircaseWitness_whiteNoise hU hV hk]
  push_cast
  ring

theorem trace_mul_staircaseWitness_staircaseState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {k : ℝ} (hk : 1 ≤ k) (s p : ℝ) :
    (staircaseWitness (U := U) (V := V) k *
        staircaseState s p).trace =
      (((1 - p) * staircaseGamma (Fintype.card U) (Fintype.card V) k
        - p * (s - k) : ℝ) : ℂ) := by
  rw [← hsInner_staircaseWitness_staircaseState hU hV hk]
  simp only [hsInner, (staircaseWitness_isHermitian k).eq]

/-- The operator expectation is negative exactly beyond the displayed
staircase threshold. -/
theorem trace_mul_staircaseWitness_staircaseState_neg_iff
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {s k p : ℝ} (hk : 1 ≤ k) (hks : k < s) :
    ((staircaseWitness (U := U) (V := V) k *
        staircaseState s p).trace).re < 0 ↔
      staircaseP (Fintype.card U) (Fintype.card V) s k < p := by
  have hm : (2 : ℝ) ≤ Fintype.card U := by exact_mod_cast hU
  have hn : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  rw [trace_mul_staircaseWitness_staircaseState hU hV hk,
    Complex.ofReal_re,
    staircaseP_eq_gamma_ratio hm hn hk hks]
  simpa [sub_eq_add_neg, add_assoc] using
    (affine_threshold_iff
      (p := p)
      (staircaseGamma_pos hm hn hk hks) (sub_pos.mpr hks))

/-- The exact negative-expectation threshold is unchanged after regrouping
the witness and state to the paper's Schmidt cut. -/
theorem trace_mul_staircaseWitnessAcrossCut_staircaseStateAcrossCut_neg_iff
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {s k p : ℝ} (hk : 1 ≤ k) (hks : k < s) :
    ((staircaseWitnessAcrossCut (U := U) (V := V) k *
        staircaseStateAcrossCut s p).trace).re < 0 ↔
      staircaseP (Fintype.card U) (Fintype.card V) s k < p := by
  rw [staircaseWitnessAcrossCut, staircaseStateAcrossCut,
    trace_mul_regroupProductOperator]
  exact trace_mul_staircaseWitness_staircaseState_neg_iff
    hU hV hk hks

/-- Above `p_k`, the noisy staircase state has Schmidt number greater than
`k` across `(A₁A₂):(B₁B₂)`.

This is the fully mixed-state lower-bound direction of the staircase theorem;
it uses no twirling or seed-decomposition claim. -/
theorem not_schmidtNumberLE_staircaseStateAcrossCut_of_threshold_lt
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {k : ℕ} (hk : 0 < k)
    (hkU : k ≤ Fintype.card U) (hkV : k ≤ Fintype.card V)
    {s p : ℝ} (hks : (k : ℝ) < s)
    (hp :
      staircaseP (Fintype.card U) (Fintype.card V) s k < p) :
    ¬ SchmidtNumberLE k
      (staircaseStateAcrossCut (U := U) (V := V) s p) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hneg :
      ((staircaseWitnessAcrossCut (U := U) (V := V) (k : ℝ) *
          staircaseStateAcrossCut s p).trace).re < 0 :=
    (trace_mul_staircaseWitnessAcrossCut_staircaseStateAcrossCut_neg_iff
      hU hV hkR hks).mpr hp
  intro hSN
  have hnonneg :=
    trace_mul_nonneg_of_schmidtNumberLE
      (staircaseWitnessAcrossCut_isHermitian (U := U) (V := V) (k : ℝ))
      (staircaseWitnessAcrossCut_isBlockPositive hk hkU hkV hU hV)
      hSN
  exact (not_lt_of_ge hnonneg) hneg

theorem trace_mul_staircaseUnprotectedWitness_seed
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {k : ℝ} (hk : 1 ≤ k) (s : ℝ) :
    (staircaseUnprotectedWitness (U := U) (V := V) k *
        staircaseSeedState s).trace = ((k - s : ℝ) : ℂ) := by
  rw [staircaseSeedState,
    trace_mul_staircaseUnprotectedWitness_biIsotropicState hU hV]
  have hUc : (Fintype.card U : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card U ≠ 0 by omega)
  have hk0 : k ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hk)
  push_cast
  field_simp
  ring

theorem trace_mul_staircaseUnprotectedWitness_whiteNoise
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {k : ℝ} (hk : 1 ≤ k) :
    (staircaseUnprotectedWitness (U := U) (V := V) k *
        staircaseWhiteNoiseState).trace =
      (staircaseGammaUnprotected
        (Fintype.card U) (Fintype.card V) k : ℂ) := by
  rw [staircaseWhiteNoiseState,
    trace_mul_staircaseUnprotectedWitness_biIsotropicState hU hV,
    staircaseGammaUnprotected, staircaseGamma]
  have hUc : (Fintype.card U : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card U ≠ 0 by omega)
  have hVc : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card V ≠ 0 by omega)
  have hk0 : k ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hk)
  push_cast
  field_simp

theorem trace_mul_staircaseUnprotectedWitness_staircaseState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {k : ℝ} (hk : 1 ≤ k) (s p : ℝ) :
    (staircaseUnprotectedWitness (U := U) (V := V) k *
        staircaseState s p).trace =
      (((1 - p) *
          staircaseGammaUnprotected
            (Fintype.card U) (Fintype.card V) k
        - p * (s - k) : ℝ) : ℂ) := by
  rw [staircaseState, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul,
    trace_mul_staircaseUnprotectedWitness_seed hU hV hk,
    trace_mul_staircaseUnprotectedWitness_whiteNoise hU hV hk]
  push_cast
  ring

theorem trace_mul_staircaseUnprotectedWitness_staircaseState_neg_iff
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {s k p : ℝ} (hk : 1 ≤ k) (hks : k < s) :
    ((staircaseUnprotectedWitness (U := U) (V := V) k *
        staircaseState s p).trace).re < 0 ↔
      staircasePUnprotected
        (Fintype.card U) (Fintype.card V) s k < p := by
  have hm : (2 : ℝ) ≤ Fintype.card U := by exact_mod_cast hU
  have hn : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hγ := staircaseGamma_pos hm hn hk hks
  have hγun :
      0 < staircaseGammaUnprotected
        (Fintype.card U) (Fintype.card V) k := by
    rw [staircaseGammaUnprotected]
    have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
    have hmpos : (0 : ℝ) < Fintype.card U := by linarith
    have hnpos : (0 : ℝ) < Fintype.card V := by linarith
    have hextra : 0 ≤ (k - 1) /
        (k * (Fintype.card U : ℝ) * Fintype.card V) := by positivity
    linarith
  rw [trace_mul_staircaseUnprotectedWitness_staircaseState hU hV hk,
    Complex.ofReal_re, staircasePUnprotected]
  simpa [sub_eq_add_neg, add_assoc] using
    (affine_threshold_iff
      (p := p) hγun (sub_pos.mpr hks))

theorem staircaseWhiteNoiseState_eq
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V) :
    staircaseWhiteNoiseState (U := U) (V := V) =
      (((((Fintype.card U : ℝ) * Fintype.card V) ^ 2)⁻¹ : ℝ) : ℂ) •
        (1 : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) := by
  rw [staircaseWhiteNoiseState, biIsotropicState,
    isotropicState_whiteNoise hU, isotropicState_whiteNoise hV,
    Matrix.smul_kronecker, Matrix.kronecker_smul,
    Matrix.one_kronecker_one, smul_smul]
  congr 1
  norm_cast
  have hUc : (Fintype.card U : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card U ≠ 0 by omega)
  have hVc : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card V ≠ 0 by omega)
  field_simp
  push_cast
  ring

/-- White noise is separable across the stated Schmidt cut, expressed as
Schmidt number at most one. -/
theorem schmidtNumberLE_one_regroupProductOperator_staircaseWhiteNoiseState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V) :
    SchmidtNumberLE 1
      (regroupProductOperator
        (staircaseWhiteNoiseState (U := U) (V := V))) := by
  rw [staircaseWhiteNoiseState_eq hU hV,
    regroupProductOperator_smul, regroupProductOperator_one]
  exact schmidtNumberLE_one.nonneg_smul (by positivity)

theorem staircaseSeedState_normalized_posSemidef
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {s : ℝ} (hs0 : 0 ≤ s) (hsU : s ≤ Fintype.card U) :
    (staircaseSeedState (U := U) (V := V) s).PosSemidef ∧
      (staircaseSeedState (U := U) (V := V) s).trace = 1 := by
  have hUc : (0 : ℝ) < Fintype.card U := by exact_mod_cast (by omega : 0 < Fintype.card U)
  simpa only [staircaseSeedState] using
    (biIsotropicState_normalized_posSemidef hU hV
      (div_nonneg hs0 hUc.le) ((div_le_one hUc).mpr hsU)
      (by norm_num) (by norm_num))

theorem staircaseWhiteNoiseState_normalized_posSemidef
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V) :
    (staircaseWhiteNoiseState (U := U) (V := V)).PosSemidef ∧
      (staircaseWhiteNoiseState (U := U) (V := V)).trace = 1 := by
  have hUr : (2 : ℝ) ≤ Fintype.card U := by exact_mod_cast hU
  have hVr : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hU2 : (1 : ℝ) ≤ (Fintype.card U : ℝ) ^ 2 := by nlinarith
  have hV2 : (1 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by nlinarith
  have hU2pos : (0 : ℝ) < (Fintype.card U : ℝ) ^ 2 := by positivity
  have hV2pos : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by positivity
  simpa only [staircaseWhiteNoiseState] using
    (biIsotropicState_normalized_posSemidef hU hV
      (by positivity) ((div_le_one hU2pos).mpr hU2)
      (by positivity) ((div_le_one hV2pos).mpr hV2))

theorem staircaseState_normalized_posSemidef
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {s p : ℝ} (hs0 : 0 ≤ s) (hsU : s ≤ Fintype.card U)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (staircaseState (U := U) (V := V) s p).PosSemidef ∧
      (staircaseState (U := U) (V := V) s p).trace = 1 := by
  obtain ⟨hseed, -⟩ :=
    staircaseSeedState_normalized_posSemidef hU hV hs0 hsU
  obtain ⟨hnoise, -⟩ :=
    staircaseWhiteNoiseState_normalized_posSemidef hU hV
  constructor
  · rw [staircaseState]
    apply Matrix.PosSemidef.add
    · exact hseed.smul ((RCLike.ofReal_nonneg (K := ℂ)).mpr hp0)
    · exact hnoise.smul
        ((RCLike.ofReal_nonneg (K := ℂ)).mpr (sub_nonneg.mpr hp1))
  · rw [staircaseState, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, staircaseSeedState, staircaseWhiteNoiseState,
      trace_biIsotropicState hU hV, trace_biIsotropicState hU hV]
    norm_num

/-- In the register order of the Schmidt cut, the admissible noisy family is
still a density matrix. -/
theorem staircaseStateAcrossCut_isDensityMatrix
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {s p : ℝ} (hs0 : 0 ≤ s) (hsU : s ≤ Fintype.card U)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsDensityMatrix
      (staircaseStateAcrossCut (U := U) (V := V) s p) := by
  obtain ⟨hpos, htrace⟩ :=
    staircaseState_normalized_posSemidef hU hV hs0 hsU hp0 hp1
  constructor
  · exact regroupProductOperator_posSemidef hpos
  · rw [staircaseStateAcrossCut, trace_regroupProductOperator, htrace]

/-- Tracing out the second product factor leaves the isotropic marginal used
in the marginal-threshold comparison. -/
theorem ptraceV_staircaseState
    (hV : 2 ≤ Fintype.card V) (s p : ℝ) :
    ptraceV (staircaseState (U := U) (V := V) s p) =
      isotropicState (T := U)
        (p * (s / Fintype.card U)
          + (1 - p) / (Fintype.card U : ℝ) ^ 2) := by
  rw [staircaseState, ptraceV_add, ptraceV_smul, ptraceV_smul,
    staircaseSeedState, staircaseWhiteNoiseState,
    ptraceV_biIsotropicState hV, ptraceV_biIsotropicState hV]
  rw [isotropicState_affine (T := U)]
  congr 1
  ring

/-- Above the marginal threshold, the first isotropic marginal cannot have
Schmidt number at most `k`.

This is the certified (detector-soundness) direction of the paper's exact
marginal crossing.  The converse still requires the missing explicit
Schmidt-rank decomposition of isotropic states. -/
theorem not_schmidtNumberLE_ptraceV_staircaseState_of_marginal_lt
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {k : ℕ} (hk : 0 < k) {s p : ℝ} (hks : (k : ℝ) < s)
    (hp :
      staircasePMarginal (Fintype.card U) s k < p) :
    ¬ SchmidtNumberLE k
      (ptraceV (staircaseState (U := U) (V := V) s p)) := by
  rw [ptraceV_staircaseState hV]
  exact not_schmidtNumberLE_isotropicState_of_ratio_lt hU hk
    ((staircasePMarginal_lt_iff_fidelity_gt
      (m := (Fintype.card U : ℝ)) (s := s) (k := (k : ℝ)) (p := p)
      (by exact_mod_cast hU) (by exact_mod_cast hk) hks).mp hp)

/-- The other marginal of the noisy family. -/
theorem ptraceU_staircaseState
    (hU : 2 ≤ Fintype.card U) (s p : ℝ) :
    ptraceU (staircaseState (U := U) (V := V) s p) =
      isotropicState (T := V)
        ((1 - p) / (Fintype.card V : ℝ) ^ 2) := by
  rw [staircaseState, ptraceU_add, ptraceU_smul, ptraceU_smul,
    staircaseSeedState, staircaseWhiteNoiseState,
    ptraceU_biIsotropicState hU, ptraceU_biIsotropicState hU]
  rw [isotropicState_affine (T := V)]
  congr 1
  ring

theorem memBiIsotropicSpace_staircaseState (s p : ℝ) :
    MemBiIsotropicSpace (staircaseState (U := U) (V := V) s p) := by
  apply MemBiIsotropicSpace.add
  · exact (memBiIsotropicSpace_biIsotropicState _ _).real_smul p
  · exact (memBiIsotropicSpace_biIsotropicState _ _).real_smul (1 - p)

theorem memBiIsotropicSpace_staircaseBoundaryState (k α : ℝ) :
    MemBiIsotropicSpace
      (staircaseBoundaryState (U := U) (V := V) k α) := by
  apply MemBiIsotropicSpace.add
  · exact (memBiIsotropicSpace_biIsotropicState _ _).real_smul (1 - α)
  · exact (memBiIsotropicSpace_biIsotropicState _ _).real_smul α

theorem trace_staircaseState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (s p : ℝ) :
    (staircaseState (U := U) (V := V) s p).trace = 1 := by
  rw [staircaseState, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, staircaseSeedState, staircaseWhiteNoiseState,
    trace_biIsotropicState hU hV, trace_biIsotropicState hU hV]
  norm_num

theorem trace_staircaseBoundaryState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (k α : ℝ) :
    (staircaseBoundaryState (U := U) (V := V) k α).trace = 1 := by
  rw [staircaseBoundaryState, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, trace_biIsotropicState hU hV,
    trace_biIsotropicState hU hV]
  norm_num

theorem staircaseBoundaryState_normalized_posSemidef
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {k α : ℝ} (hk0 : 0 ≤ k)
    (hkU : k ≤ Fintype.card U) (hkV : k ≤ Fintype.card V)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (staircaseBoundaryState (U := U) (V := V) k α).PosSemidef ∧
      (staircaseBoundaryState (U := U) (V := V) k α).trace = 1 := by
  have hUr : (2 : ℝ) ≤ Fintype.card U := by exact_mod_cast hU
  have hUpos : (0 : ℝ) < Fintype.card U := by linarith
  have hVpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hU2 : (1 : ℝ) ≤ (Fintype.card U : ℝ) ^ 2 := by nlinarith
  have hU2pos : (0 : ℝ) < (Fintype.card U : ℝ) ^ 2 := by positivity
  have hfirst :
      (biIsotropicState (U := U) (V := V)
        (k / Fintype.card U) 0).PosSemidef :=
    (biIsotropicState_normalized_posSemidef hU hV
      (div_nonneg hk0 hUpos.le) ((div_le_one hUpos).mpr hkU)
      (by norm_num) (by norm_num)).1
  have hsecond :
      (biIsotropicState (U := U) (V := V)
        (1 / (Fintype.card U : ℝ) ^ 2)
        (k / Fintype.card V)).PosSemidef :=
    (biIsotropicState_normalized_posSemidef hU hV
      (by positivity) ((div_le_one hU2pos).mpr hU2)
      (div_nonneg hk0 hVpos.le) ((div_le_one hVpos).mpr hkV)).1
  constructor
  · rw [staircaseBoundaryState]
    apply Matrix.PosSemidef.add
    · exact hfirst.smul
        ((RCLike.ofReal_nonneg (K := ℂ)).mpr (sub_nonneg.mpr hα1))
    · exact hsecond.smul ((RCLike.ofReal_nonneg (K := ℂ)).mpr hα0)
  · exact trace_staircaseBoundaryState hU hV k α

theorem biIsotropicMomentU_staircaseState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (s p : ℝ) :
    biIsotropicMomentU (staircaseState (U := U) (V := V) s p) =
      p * (s / Fintype.card U)
        + (1 - p) / (Fintype.card U : ℝ) ^ 2 := by
  rw [staircaseState, biIsotropicMomentU_add,
    biIsotropicMomentU_real_smul, biIsotropicMomentU_real_smul,
    staircaseSeedState, staircaseWhiteNoiseState,
    biIsotropicMomentU_state hU hV, biIsotropicMomentU_state hU hV]
  ring

theorem biIsotropicMomentV_staircaseState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (s p : ℝ) :
    biIsotropicMomentV (staircaseState (U := U) (V := V) s p) =
      (1 - p) / (Fintype.card V : ℝ) ^ 2 := by
  rw [staircaseState, biIsotropicMomentV_add,
    biIsotropicMomentV_real_smul, biIsotropicMomentV_real_smul,
    staircaseSeedState, staircaseWhiteNoiseState,
    biIsotropicMomentV_state hU hV, biIsotropicMomentV_state hU hV]
  ring

theorem biIsotropicMomentUV_staircaseState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (s p : ℝ) :
    biIsotropicMomentUV (staircaseState (U := U) (V := V) s p) =
      (1 - p) /
        ((Fintype.card U : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 2) := by
  rw [staircaseState, biIsotropicMomentUV_add,
    biIsotropicMomentUV_real_smul, biIsotropicMomentUV_real_smul,
    staircaseSeedState, staircaseWhiteNoiseState,
    biIsotropicMomentUV_state hU hV, biIsotropicMomentUV_state hU hV]
  ring

theorem biIsotropicMomentU_staircaseBoundaryState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (k α : ℝ) :
    biIsotropicMomentU
        (staircaseBoundaryState (U := U) (V := V) k α) =
      (1 - α) * (k / Fintype.card U)
        + α / (Fintype.card U : ℝ) ^ 2 := by
  rw [staircaseBoundaryState, biIsotropicMomentU_add,
    biIsotropicMomentU_real_smul, biIsotropicMomentU_real_smul,
    biIsotropicMomentU_state hU hV, biIsotropicMomentU_state hU hV]
  ring

theorem biIsotropicMomentV_staircaseBoundaryState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (k α : ℝ) :
    biIsotropicMomentV
        (staircaseBoundaryState (U := U) (V := V) k α) =
      α * (k / Fintype.card V) := by
  rw [staircaseBoundaryState, biIsotropicMomentV_add,
    biIsotropicMomentV_real_smul, biIsotropicMomentV_real_smul,
    biIsotropicMomentV_state hU hV, biIsotropicMomentV_state hU hV]
  ring

theorem biIsotropicMomentUV_staircaseBoundaryState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (k α : ℝ) :
    biIsotropicMomentUV
        (staircaseBoundaryState (U := U) (V := V) k α) =
      α * (k / ((Fintype.card U : ℝ) ^ 2 * Fintype.card V)) := by
  rw [staircaseBoundaryState, biIsotropicMomentUV_add,
    biIsotropicMomentUV_real_smul, biIsotropicMomentUV_real_smul,
    biIsotropicMomentUV_state hU hV, biIsotropicMomentUV_state hU hV]
  ring

/-- The exact matrix identity `eq:decomp`, separated from the still-open
Schmidt-number assertions about its two summands. -/
theorem staircase_boundary_operator_identity
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {s k : ℝ} (hk : 1 ≤ k) (hks : k < s) :
    let m := (Fintype.card U : ℝ)
    let n := (Fintype.card V : ℝ)
    staircaseState (U := U) (V := V) s (staircaseP m n s k) =
      staircaseBoundaryState (U := U) (V := V) k
        (staircaseAlpha m n s k) := by
  dsimp
  have hm : (2 : ℝ) ≤ Fintype.card U := by exact_mod_cast hU
  have hn : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  obtain ⟨hUmoment, hVmoment, hUVmoment⟩ :=
    staircase_boundary_moments hm hn hk hks
  apply eq_of_memBiIsotropicSpace_of_trace_moments hU hV
  · exact memBiIsotropicSpace_staircaseState _ _
  · exact memBiIsotropicSpace_staircaseBoundaryState _ _
  · rw [trace_staircaseState hU hV,
      trace_staircaseBoundaryState hU hV]
  · rw [biIsotropicMomentU_staircaseState hU hV,
      biIsotropicMomentU_staircaseBoundaryState hU hV]
    exact hUmoment
  · rw [biIsotropicMomentV_staircaseState hU hV,
      biIsotropicMomentV_staircaseBoundaryState hU hV]
    exact hVmoment
  · rw [biIsotropicMomentUV_staircaseState hU hV,
      biIsotropicMomentUV_staircaseBoundaryState hU hV]
    exact hUVmoment

/-- The boundary identity gives the Schmidt-number upper bound once its two
product-isotropic seed obligations are supplied.

This theorem isolates all remaining semantic content of the boundary step in
the two hypotheses; the convex-cone argument and the register regrouping are
fully explicit. -/
theorem schmidtNumberLE_staircaseStateAcrossCut_at_threshold_of_seeds
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {s : ℝ} {k : ℕ} (hk : 0 < k) (hks : (k : ℝ) < s)
    (hseedU :
      SchmidtNumberLE k
        (regroupProductOperator
          (biIsotropicState (U := U) (V := V)
            ((k : ℝ) / Fintype.card U) 0)))
    (hseedV :
      SchmidtNumberLE k
        (regroupProductOperator
          (biIsotropicState (U := U) (V := V)
            (1 / (Fintype.card U : ℝ) ^ 2)
            ((k : ℝ) / Fintype.card V)))) :
    SchmidtNumberLE k
      (staircaseStateAcrossCut (U := U) (V := V) s
        (staircaseP (Fintype.card U) (Fintype.card V) s k)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : (2 : ℝ) ≤ Fintype.card U := by exact_mod_cast hU
  have hn : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hα :=
    staircaseAlpha_mem_Ioo hm hn hkR hks
  rw [staircaseStateAcrossCut,
    staircase_boundary_operator_identity hU hV hkR hks,
    staircaseBoundaryState, regroupProductOperator_add,
    regroupProductOperator_smul, regroupProductOperator_smul]
  exact
    (hseedU.nonneg_smul (sub_nonneg.mpr hα.2.le)).add
      (hseedV.nonneg_smul hα.1.le)

/-- The entire upper-bound side `0 ≤ p ≤ p_k` follows from the two boundary
seed obligations.

White noise is handled by its explicit computational-basis decomposition.
Thus all affine and cone bookkeeping in the staircase upper bound is checked;
only the two displayed product-seed inputs remain semantic obligations. -/
theorem schmidtNumberLE_staircaseStateAcrossCut_of_le_threshold_of_seeds
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {s : ℝ} {k : ℕ} (hk : 0 < k) (hks : (k : ℝ) < s)
    (hseedU :
      SchmidtNumberLE k
        (regroupProductOperator
          (biIsotropicState (U := U) (V := V)
            ((k : ℝ) / Fintype.card U) 0)))
    (hseedV :
      SchmidtNumberLE k
        (regroupProductOperator
          (biIsotropicState (U := U) (V := V)
            (1 / (Fintype.card U : ℝ) ^ 2)
            ((k : ℝ) / Fintype.card V))))
    {p : ℝ} (hp0 : 0 ≤ p)
    (hp :
      p ≤ staircaseP (Fintype.card U) (Fintype.card V) s k) :
    SchmidtNumberLE k
      (staircaseStateAcrossCut (U := U) (V := V) s p) := by
  let q := staircaseP
    (Fintype.card U : ℝ) (Fintype.card V : ℝ) s (k : ℝ)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : (2 : ℝ) ≤ Fintype.card U := by exact_mod_cast hU
  have hn : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hq : 0 < q :=
    (staircaseP_mem_Ioo hm hn hkR hks).1
  have hboundary :
      SchmidtNumberLE k
        (staircaseStateAcrossCut (U := U) (V := V) s q) := by
    exact
      schmidtNumberLE_staircaseStateAcrossCut_at_threshold_of_seeds
        hU hV hk hks hseedU hseedV
  have hwhite :
      SchmidtNumberLE k
        (regroupProductOperator
          (staircaseWhiteNoiseState (U := U) (V := V))) :=
    (schmidtNumberLE_one_regroupProductOperator_staircaseWhiteNoiseState
      hU hV).mono (by omega)
  rw [staircaseStateAcrossCut,
    staircaseState_eq_threshold_whiteNoise_mix s p q (ne_of_gt hq),
    regroupProductOperator_add, regroupProductOperator_smul,
    regroupProductOperator_smul]
  exact
    (hboundary.nonneg_smul (div_nonneg hp0 hq.le)).add
      (hwhite.nonneg_smul
        (sub_nonneg.mpr ((div_le_one hq).mpr hp)))

/-- At an admissible threshold, the left-hand state in the boundary identity
is normalized and positive semidefinite. -/
theorem staircaseState_at_threshold_normalized_posSemidef
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {s k : ℝ} (hs0 : 0 ≤ s) (hsU : s ≤ Fintype.card U)
    (hk : 1 ≤ k) (hks : k < s) :
    let p := staircaseP (Fintype.card U) (Fintype.card V) s k
    (staircaseState (U := U) (V := V) s p).PosSemidef ∧
      (staircaseState (U := U) (V := V) s p).trace = 1 := by
  dsimp
  have hm : (2 : ℝ) ≤ Fintype.card U := by exact_mod_cast hU
  have hn : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hp := staircaseP_mem_Ioo hm hn hk hks
  exact staircaseState_normalized_posSemidef hU hV hs0 hsU hp.1.le hp.2.le

/-- At an admissible threshold, the right-hand convex combination in the
boundary identity is normalized and positive semidefinite.  This is a state
claim, not the still-open Schmidt-number bound. -/
theorem staircaseBoundaryState_at_threshold_normalized_posSemidef
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {s k : ℝ} (hk : 1 ≤ k) (hks : k < s)
    (hkU : k ≤ Fintype.card U) (hkV : k ≤ Fintype.card V) :
    let α := staircaseAlpha (Fintype.card U) (Fintype.card V) s k
    (staircaseBoundaryState (U := U) (V := V) k α).PosSemidef ∧
      (staircaseBoundaryState (U := U) (V := V) k α).trace = 1 := by
  dsimp
  have hm : (2 : ℝ) ≤ Fintype.card U := by exact_mod_cast hU
  have hn : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hα := staircaseAlpha_mem_Ioo hm hn hk hks
  exact staircaseBoundaryState_normalized_posSemidef hU hV
    (by linarith) hkU hkV hα.1.le hα.2.le

end

end RankR
