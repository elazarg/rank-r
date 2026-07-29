/-
Finite operator algebra for the state family and boundary decomposition in
`paper/derivation-schmidt-staircase.tex`.

The matrices are kept in the paper's `A₁B₁A₂B₂` register order.  This file
proves the normalized isotropic white-noise identity and the exact boundary
operator equality.  It does not assert that the algebraic product-isotropic
space is the range of a Haar twirl, or that the twirl preserves Schmidt number.
-/
import RankR.Isotropic
import RankR.Staircase

namespace RankR

open Matrix ComplexConjugate
open scoped ComplexOrder Kronecker MatrixOrder

section

variable {U V : Type*} [Fintype U] [Fintype V]
  [DecidableEq U] [DecidableEq V]

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

/-- The two-term candidate in the boundary decomposition. -/
noncomputable def staircaseBoundaryState (k α : ℝ) :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  ((1 - α : ℝ) : ℂ) •
      biIsotropicState (k / Fintype.card U) 0
    + (α : ℂ) •
      biIsotropicState
        (1 / (Fintype.card U : ℝ) ^ 2)
        (k / Fintype.card V)

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

theorem staircaseWitnessFactor_isHermitian
    {T : Type*} [Fintype T] [DecidableEq T] (k : ℝ) :
    (staircaseWitnessFactor T k).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [staircaseWitnessFactor, omegaProjection, singleOmegaChoi,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    rankOne_conjTranspose]

theorem staircaseWitness_isHermitian (k : ℝ) :
    (staircaseWitness (U := U) (V := V) k).IsHermitian := by
  have hkr :
      (staircaseWitnessFactor U k ⊗ₖ
        staircaseWitnessFactor V k).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker,
      (staircaseWitnessFactor_isHermitian k).eq,
      (staircaseWitnessFactor_isHermitian k).eq]
  apply hkr.smul
  change conj (k : ℂ) = (k : ℂ)
  exact Complex.conj_ofReal k

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
    · apply hseed.smul
      exact (RCLike.ofReal_nonneg (K := ℂ)).mpr hp0
    · apply hnoise.smul
      exact (RCLike.ofReal_nonneg (K := ℂ)).mpr (sub_nonneg.mpr hp1)
  · rw [staircaseState, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, staircaseSeedState, staircaseWhiteNoiseState,
      trace_biIsotropicState hU hV, trace_biIsotropicState hU hV]
    norm_num

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
    · apply hfirst.smul
      exact (RCLike.ofReal_nonneg (K := ℂ)).mpr (sub_nonneg.mpr hα1)
    · apply hsecond.smul
      exact (RCLike.ofReal_nonneg (K := ℂ)).mpr hα0
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
