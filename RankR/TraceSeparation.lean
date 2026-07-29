/-
Mixed-state and Hermitian-duality infrastructure for the quantitative
trace-distance application.

A positive operator has Schmidt number at most `r` precisely when it is a
finite sum of unnormalized pure states whose coefficient matrices have rank at
most `r`.  Encoding the nonnegative scalar weights into those coefficient
matrices avoids a redundant probability-vector layer.
-/
import RankR.Applications
import Mathlib.Analysis.Matrix.Spectrum

namespace RankR

open Matrix Finset ComplexConjugate
open scoped ComplexOrder

section MixedStates

variable {W : Type*} [Fintype W]

/-- A finite-coordinate density matrix. -/
def IsDensityMatrix (ρ : Matrix (W × W) (W × W) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- Mixed-state Schmidt number at most `r`, in the same vectorization
coordinates as `IsBlockPositive`.

The vectors need not be normalized: their squared norms absorb the
nonnegative ensemble weights. -/
def SchmidtNumberLE (r : ℕ) (ρ : Matrix (W × W) (W × W) ℂ) : Prop :=
  ∃ n : ℕ, ∃ C : Fin n → Matrix W W ℂ,
    (∀ i, (C i).rank ≤ r) ∧
      ρ = ∑ i, rankOne (vec (C i)) (vec (C i))

/-- Enlarging the allowed Schmidt rank enlarges the cone. -/
theorem SchmidtNumberLE.mono {r s : ℕ} {ρ : Matrix (W × W) (W × W) ℂ}
    (hρ : SchmidtNumberLE r ρ) (hrs : r ≤ s) :
    SchmidtNumberLE s ρ := by
  obtain ⟨n, C, hCrank, hCsum⟩ := hρ
  exact ⟨n, C, fun i => (hCrank i).trans hrs, hCsum⟩

/-- The Schmidt-number-at-most-`r` cone is closed under addition. -/
theorem SchmidtNumberLE.add {r : ℕ}
    {ρ σ : Matrix (W × W) (W × W) ℂ}
    (hρ : SchmidtNumberLE r ρ) (hσ : SchmidtNumberLE r σ) :
    SchmidtNumberLE r (ρ + σ) := by
  obtain ⟨n, C, hCrank, hCsum⟩ := hρ
  obtain ⟨m, D, hDrank, hDsum⟩ := hσ
  refine ⟨n + m, Fin.append C D, ?_, ?_⟩
  · intro i
    exact Fin.addCases
      (fun j => by simpa using hCrank j)
      (fun j => by simpa using hDrank j) i
  · rw [hCsum, hDsum, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

/-- The Schmidt-number-at-most-`r` cone is closed under multiplication by a
nonnegative real scalar. -/
theorem SchmidtNumberLE.nonneg_smul {r : ℕ}
    {ρ : Matrix (W × W) (W × W) ℂ}
    [DecidableEq W]
    (hρ : SchmidtNumberLE r ρ) {t : ℝ} (ht : 0 ≤ t) :
    SchmidtNumberLE r ((t : ℂ) • ρ) := by
  obtain ⟨n, C, hCrank, hCsum⟩ := hρ
  let D : Fin n → Matrix W W ℂ :=
    fun i => (Real.sqrt t : ℂ) • C i
  refine ⟨n, D, ?_, ?_⟩
  · intro i
    by_cases ht0 : t = 0
    · subst t
      simp [D]
    · have hsqrt : (Real.sqrt t : ℂ) ≠ 0 := by
        exact_mod_cast Real.sqrt_ne_zero'.mpr
          (lt_of_le_of_ne ht (Ne.symm ht0))
      change (((Real.sqrt t : ℂ) • C i).rank ≤ r)
      rw [rank_smul_eq_of_ne_zero _ hsqrt]
      exact hCrank i
  · rw [hCsum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      ext p q
      simp only [D, vec_smul, PiLp.smul_apply, smul_eq_mul, rankOne,
        Matrix.smul_apply, Matrix.of_apply, map_mul, Complex.conj_ofReal]
      have hsqrt :
          ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) = (t : ℂ) := by
        norm_cast
        simpa [pow_two] using Real.sq_sqrt ht
      rw [← hsqrt]
      ring

/-- The identity on a square bipartite coordinate space has Schmidt number at
most one: its computational-basis decomposition consists of product
projectors. -/
theorem schmidtNumberLE_one
    [DecidableEq W] :
    SchmidtNumberLE 1
      (1 : Matrix (W × W) (W × W) ℂ) := by
  let e : Fin (Fintype.card (W × W)) ≃ W × W :=
    (Fintype.equivFin (W × W)).symm
  let C : Fin (Fintype.card (W × W)) → Matrix W W ℂ :=
    fun a => Matrix.single (e a).1 (e a).2 1
  refine ⟨Fintype.card (W × W), C, ?_, ?_⟩
  · intro a
    let u : W → ℂ := fun i => if i = (e a).1 then 1 else 0
    let v : W → ℂ := fun j => if j = (e a).2 then 1 else 0
    have hsingle : C a = Matrix.vecMulVec u v := by
      ext i j
      simp only [C, u, v, Matrix.single_apply, Matrix.vecMulVec_apply]
      by_cases hi : i = (e a).1 <;> by_cases hj : j = (e a).2 <;>
        simp [hi, hj, eq_comm]
    rw [hsingle]
    exact Matrix.rank_vecMulVec_le u v
  · ext p q
    simp only [Matrix.one_apply, Matrix.sum_apply]
    change (if p = q then 1 else 0) =
      ∑ a, rankOne (vec (C a)) (vec (C a)) p q
    rw [show
      (∑ a, rankOne (vec (C a)) (vec (C a)) p q) =
        ∑ z : W × W,
          rankOne
            (vec (Matrix.single z.1 z.2 (1 : ℂ)))
            (vec (Matrix.single z.1 z.2 (1 : ℂ))) p q by
      simpa only [C] using
        (Equiv.sum_comp e
          (fun z : W × W =>
            rankOne
              (vec (Matrix.single z.1 z.2 (1 : ℂ)))
              (vec (Matrix.single z.1 z.2 (1 : ℂ))) p q))]
    simp only [rankOne, vec_apply, Matrix.single_apply]
    simp_rw [← Prod.ext_iff]
    by_cases hpq : p = q <;> simp [hpq, eq_comm]

/-- Pairing an operator with a rank-one projector gives its real quadratic
form. -/
theorem re_hsInner_rankOne {X : Type*} [Fintype X] (M : Matrix X X ℂ)
    (x : EuclideanSpace ℂ X) :
    (hsInner M (rankOne x x)).re = (qform M x).re := by
  have h :
      hsInner M (rankOne x x) = conj (inner ℂ x (mulVecE M x)) := by
    simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def, rankOne, Matrix.of_apply,
      PiLp.inner_apply, RCLike.inner_apply', mulVecE_apply, map_sum, map_mul,
      Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [h, qform_eq_inner]
  exact Complex.conj_re _

/-- Block positivity extends from pure vectors to every positive operator of
Schmidt number at most `r`. -/
theorem re_hsInner_nonneg_of_schmidtNumberLE {r : ℕ}
    {M ρ : Matrix (W × W) (W × W) ℂ}
    (hM : IsBlockPositive r M) (hρ : SchmidtNumberLE r ρ) :
    0 ≤ (hsInner M ρ).re := by
  obtain ⟨n, C, hCrank, rfl⟩ := hρ
  rw [hsInner_sum_right, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [re_hsInner_rankOne]
    exact hM (C i) (hCrank i)

/-- The expectation of a Hermitian witness is its Hilbert--Schmidt pairing. -/
theorem trace_mul_eq_hsInner_of_isHermitian
    {M ρ : Matrix (W × W) (W × W) ℂ} (hM : M.IsHermitian) :
    (M * ρ).trace = hsInner M ρ := by
  rw [hsInner, hM.eq]

/-- A block-positive Hermitian witness has nonnegative expectation on every
state of Schmidt number at most `r`. -/
theorem trace_mul_nonneg_of_schmidtNumberLE {r : ℕ}
    {M ρ : Matrix (W × W) (W × W) ℂ}
    (hHerm : M.IsHermitian) (hM : IsBlockPositive r M)
    (hρ : SchmidtNumberLE r ρ) :
    0 ≤ ((M * ρ).trace).re := by
  rw [trace_mul_eq_hsInner_of_isHermitian hHerm]
  exact re_hsInner_nonneg_of_schmidtNumberLE hM hρ

end MixedStates

section HermitianTraceNorm

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The Schatten-`1` norm of a Hermitian matrix, rendered as the sum of the
absolute values of its real eigenvalues. -/
noncomputable def hermitianTraceNorm (D : Matrix I I ℂ) (hD : D.IsHermitian) : ℝ :=
  ∑ i, |hD.eigenvalues i|

theorem hermitianTraceNorm_nonneg (D : Matrix I I ℂ) (hD : D.IsHermitian) :
    0 ≤ hermitianTraceNorm D hD :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Spectral decomposition into unnormalized rank-one projectors. -/
theorem isHermitian_eq_sum_eigen_rankOne (D : Matrix I I ℂ) (hD : D.IsHermitian) :
    D = ∑ i, (hD.eigenvalues i : ℂ) •
      rankOne (hD.eigenvectorBasis i) (hD.eigenvectorBasis i) := by
  calc
    D = (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hD.eigenvectorUnitary)
        (Matrix.diagonal (RCLike.ofReal ∘ hD.eigenvalues)) := hD.spectral_theorem
    _ = ∑ i, (hD.eigenvalues i : ℂ) •
        rankOne (hD.eigenvectorBasis i) (hD.eigenvectorBasis i) := by
      ext p q
      simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.of_apply, mul_ite,
        mul_zero, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, rankOne, Matrix.IsHermitian.eigenvectorUnitary_apply]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [Complex.coe_algebraMap, Function.comp_apply,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          RCLike.star_def]
        ring

/-- Expand a Hilbert--Schmidt pairing along the Hermitian spectral
decomposition of its second argument. -/
theorem re_hsInner_eq_sum_eigen_qform (H D : Matrix I I ℂ) (hD : D.IsHermitian) :
    (hsInner H D).re
      = ∑ i, hD.eigenvalues i * (qform H (hD.eigenvectorBasis i)).re := by
  calc
    (hsInner H D).re
        = (hsInner H (∑ i, (hD.eigenvalues i : ℂ) •
            rankOne (hD.eigenvectorBasis i) (hD.eigenvectorBasis i))).re := by
              rw [← isHermitian_eq_sum_eigen_rankOne D hD]
    _ = ∑ i, hD.eigenvalues i * (qform H (hD.eigenvectorBasis i)).re := by
      rw [hsInner_sum_right, Complex.re_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [hsInner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, re_hsInner_rankOne]

/-- Hölder duality for a Hermitian second argument, stated using exactly the
quadratic-form bound needed by the witness application. -/
theorem abs_re_hsInner_le_hermitianTraceNorm
    (H D : Matrix I I ℂ) (hD : D.IsHermitian) {L : ℝ}
    (hH : ∀ x : EuclideanSpace ℂ I, ‖x‖ = 1 → |(qform H x).re| ≤ L) :
    |(hsInner H D).re| ≤ L * hermitianTraceNorm D hD := by
  rw [re_hsInner_eq_sum_eigen_qform H D hD, hermitianTraceNorm]
  calc
    |∑ i, hD.eigenvalues i * (qform H (hD.eigenvectorBasis i)).re|
        ≤ ∑ i, |hD.eigenvalues i * (qform H (hD.eigenvectorBasis i)).re| := by
          simpa using Finset.abs_sum_le_sum_abs
            (fun i => hD.eigenvalues i * (qform H (hD.eigenvectorBasis i)).re)
            Finset.univ
    _ = ∑ i, |hD.eigenvalues i| *
          |(qform H (hD.eigenvectorBasis i)).re| := by
          exact Finset.sum_congr rfl fun i _ => abs_mul _ _
    _ ≤ ∑ i, |hD.eigenvalues i| * L := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left
              (hH (hD.eigenvectorBasis i)
                (hD.eigenvectorBasis.orthonormal.norm_eq_one i))
              (abs_nonneg _)
    _ = L * ∑ i, |hD.eigenvalues i| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring

end HermitianTraceNorm

section WitnessSeparation

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A centered Hermitian witness separates a detected state from every
Schmidt-number-`r` state by its Hermitian trace norm.  This is the
finite-coordinate content of the Hölder-duality step in
`cor:two-copy-trace-distance`. -/
theorem witness_separation_hermitianTraceNorm
    {r : ℕ} {Z ρ σ : Matrix (W × W) (W × W) ℂ}
    (hZ : Z.IsHermitian) (hBlock : IsBlockPositive r Z)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hSN : SchmidtNumberLE r σ)
    {ε c L : ℝ} (hdetect : ((Z * ρ).trace).re = -ε)
    (hcenter : ∀ x : EuclideanSpace ℂ (W × W), ‖x‖ = 1 →
      |(qform (Z - (c : ℂ) • 1) x).re| ≤ L) :
    ε ≤ L * hermitianTraceNorm (σ - ρ) (hσ.1.isHermitian.sub hρ.1.isHermitian) := by
  let D := σ - ρ
  have hD : D.IsHermitian := hσ.1.isHermitian.sub hρ.1.isHermitian
  have htraceD : D.trace = 0 := by
    dsimp only [D]
    rw [Matrix.trace_sub, hσ.2, hρ.2, sub_self]
  have hZρ : (hsInner Z ρ).re = -ε := by
    rw [← trace_mul_eq_hsInner_of_isHermitian hZ]
    exact hdetect
  have hZσ : 0 ≤ (hsInner Z σ).re :=
    re_hsInner_nonneg_of_schmidtNumberLE hBlock hSN
  have hgap : ε ≤ (hsInner Z D).re := by
    dsimp only [D]
    rw [hsInner_sub_right, Complex.sub_re]
    linarith
  have hscalar : hsInner ((c : ℂ) • (1 : Matrix (W × W) (W × W) ℂ)) D = 0 := by
    rw [hsInner_smul_left]
    simp only [Complex.conj_ofReal, hsInner, Matrix.conjTranspose_one, Matrix.one_mul, htraceD,
      mul_zero]
  have hcenterEq :
      (hsInner (Z - (c : ℂ) • (1 : Matrix (W × W) (W × W) ℂ)) D).re
        = (hsInner Z D).re := by
    rw [hsInner_sub_left, hscalar, sub_zero]
  have hholder := abs_re_hsInner_le_hermitianTraceNorm
    (Z - (c : ℂ) • (1 : Matrix (W × W) (W × W) ℂ)) D hD hcenter
  rw [hcenterEq] at hholder
  exact hgap.trans ((le_abs_self _).trans hholder)

/-- The preceding separation bound in the spectral-diameter normalization of
the manuscript. -/
theorem two_mul_div_le_hermitianTraceNorm_of_witness
    {r : ℕ} {Z ρ σ : Matrix (W × W) (W × W) ℂ}
    (hZ : Z.IsHermitian) (hBlock : IsBlockPositive r Z)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hSN : SchmidtNumberLE r σ)
    {ε c Δ : ℝ} (hΔ : 0 < Δ) (hdetect : ((Z * ρ).trace).re = -ε)
    (hcenter : ∀ x : EuclideanSpace ℂ (W × W), ‖x‖ = 1 →
      |(qform (Z - (c : ℂ) • 1) x).re| ≤ Δ / 2) :
    2 * ε / Δ
      ≤ hermitianTraceNorm (σ - ρ) (hσ.1.isHermitian.sub hρ.1.isHermitian) := by
  have h := witness_separation_hermitianTraceNorm
    hZ hBlock hρ hσ hSN hdetect hcenter
  rw [div_le_iff₀ hΔ]
  nlinarith

end WitnessSeparation

section TwoCopySpectrum

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The normalized projector onto the one-factor maximally entangled
direction. -/
noncomputable def omegaProjection :
    Matrix (T × T) (T × T) ℂ :=
  ((1 / (Fintype.card T : ℝ) : ℝ) : ℂ) • singleOmegaChoi

/-- The orthogonal complement of the maximally entangled direction. -/
noncomputable def omegaComplement :
    Matrix (T × T) (T × T) ℂ :=
  1 - omegaProjection (T := T)

/-- The negative eigenvalue magnitude `d/r - 1` of the one-factor reduction
Choi matrix at parameter `1/r`. -/
noncomputable def traceSeparationGamma (r : ℕ) : ℝ :=
  (Fintype.card T : ℝ) / r - 1

/-- The spectral diameter used in `cor:two-copy-trace-distance`. -/
noncomputable def traceSeparationDelta (r : ℕ) : ℝ :=
  traceSeparationGamma (T := T) r
    + max 1 ((traceSeparationGamma (T := T) r) ^ 2)

theorem omegaComplement_add_projection :
    omegaComplement (T := T) + omegaProjection (T := T) = 1 := by
  rw [omegaComplement, sub_add_cancel]

theorem singleOmegaChoi_posSemidef :
    (singleOmegaChoi (T := T)).PosSemidef := by
  have h :
      singleOmegaChoi (T := T) =
        Matrix.vecMulVec (singleOmegaVec (T := T) : T × T → ℂ)
          (star (singleOmegaVec (T := T) : T × T → ℂ)) := by
    ext p q
    simp [singleOmegaChoi, rankOne, Matrix.vecMulVec_apply, Pi.star_apply,
      RCLike.star_def]
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem omegaProjection_posSemidef (hT : 0 < Fintype.card T) :
    (omegaProjection (T := T)).PosSemidef := by
  exact singleOmegaChoi_posSemidef.smul
    ((RCLike.ofReal_nonneg (K := ℂ)).mpr
      (one_div_nonneg.mpr (by exact_mod_cast hT.le)))

theorem omegaComplement_eq_reductionChoi :
    omegaComplement (T := T)
      = reductionChoi (T := T) (1 / (Fintype.card T : ℝ)) := by
  rfl

theorem omegaComplement_posSemidef (hT : 0 < Fintype.card T) :
    (omegaComplement (T := T)).PosSemidef := by
  rw [omegaComplement_eq_reductionChoi]
  exact reductionChoi_posSemidef (one_div_nonneg.mpr (by exact_mod_cast hT.le))
    hT le_rfl

omit [DecidableEq T] in
/-- Regrouping a Kronecker product preserves positive semidefiniteness. -/
theorem regroupChoi_posSemidef
    {A : Matrix (T × T) (T × T) ℂ} {B : Matrix (T × T) (T × T) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (regroupChoi A B).PosSemidef := by
  rw [regroupChoi, Matrix.reindex_apply]
  exact hA.kronecker hB |>.submatrix _

omit [Fintype T] [DecidableEq T] in
theorem regroupChoi_add_left
    (A A' : Matrix (T × T) (T × T) ℂ) (B : Matrix (T × T) (T × T) ℂ) :
    regroupChoi (A + A') B = regroupChoi A B + regroupChoi A' B := by
  ext X Y
  simp only [regroupChoi, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.add_apply]
  ring

omit [Fintype T] [DecidableEq T] in
theorem regroupChoi_add_right
    (A : Matrix (T × T) (T × T) ℂ) (B B' : Matrix (T × T) (T × T) ℂ) :
    regroupChoi A (B + B') = regroupChoi A B + regroupChoi A B' := by
  ext X Y
  simp only [regroupChoi, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.add_apply]
  ring

/-- Read positive semidefiniteness in the quadratic-form convention of the
development. -/
theorem qform_re_nonneg_of_posSemidef
    {X : Type*} [Fintype X] {A : Matrix X X ℂ} (hA : A.PosSemidef)
    (x : EuclideanSpace ℂ X) :
    0 ≤ (qform A x).re := by
  have hq : 0 ≤ qform A x := by
    have h := hA.dotProduct_mulVec_nonneg (x : X → ℂ)
    simpa [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using h
  exact (Complex.nonneg_iff.mp hq).1

/-- The one-factor reduction Choi matrix decomposes into its two spectral
projectors with eigenvalues `1` and `-γ`. -/
theorem reductionChoi_inv_eq_complement_sub_gamma
    {r : ℕ} (hr : 0 < r) (hT : 0 < Fintype.card T) :
    reductionChoi (T := T) (1 / (r : ℝ))
      = omegaComplement (T := T)
        - ((traceSeparationGamma (T := T) r : ℝ) : ℂ) •
          omegaProjection (T := T) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hdR : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  ext p q
  simp only [reductionChoi, omegaComplement, omegaProjection, traceSeparationGamma,
    Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hpq : p = q <;> simp [hpq]
  all_goals (field_simp [hrR, hdR] ; ring)

/-- The four mutually orthogonal sector projectors in the tensor square of
the one-factor decomposition. -/
noncomputable def twoCopySectorCC :
    Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ :=
  regroupChoi (omegaComplement (T := T)) (omegaComplement (T := T))

noncomputable def twoCopySectorCP :
    Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ :=
  regroupChoi (omegaComplement (T := T)) (omegaProjection (T := T))

noncomputable def twoCopySectorPC :
    Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ :=
  regroupChoi (omegaProjection (T := T)) (omegaComplement (T := T))

noncomputable def twoCopySectorPP :
    Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ :=
  regroupChoi (omegaProjection (T := T)) (omegaProjection (T := T))

theorem twoCopySectorCC_posSemidef (hT : 0 < Fintype.card T) :
    (twoCopySectorCC (T := T)).PosSemidef :=
  regroupChoi_posSemidef (omegaComplement_posSemidef hT)
    (omegaComplement_posSemidef hT)

theorem twoCopySectorCP_posSemidef (hT : 0 < Fintype.card T) :
    (twoCopySectorCP (T := T)).PosSemidef :=
  regroupChoi_posSemidef (omegaComplement_posSemidef hT)
    (omegaProjection_posSemidef hT)

theorem twoCopySectorPC_posSemidef (hT : 0 < Fintype.card T) :
    (twoCopySectorPC (T := T)).PosSemidef :=
  regroupChoi_posSemidef (omegaProjection_posSemidef hT)
    (omegaComplement_posSemidef hT)

theorem twoCopySectorPP_posSemidef (hT : 0 < Fintype.card T) :
    (twoCopySectorPP (T := T)).PosSemidef :=
  regroupChoi_posSemidef (omegaProjection_posSemidef hT)
    (omegaProjection_posSemidef hT)

theorem twoCopySectors_sum :
    twoCopySectorCC (T := T) + twoCopySectorCP (T := T)
        + twoCopySectorPC (T := T) + twoCopySectorPP (T := T) = 1 := by
  rw [show twoCopySectorCC (T := T) + twoCopySectorCP (T := T)
        + twoCopySectorPC (T := T) + twoCopySectorPP (T := T)
      = (twoCopySectorCC (T := T) + twoCopySectorCP (T := T))
        + (twoCopySectorPC (T := T) + twoCopySectorPP (T := T)) by abel]
  simp only [twoCopySectorCC, twoCopySectorCP, twoCopySectorPC, twoCopySectorPP,
    ← regroupChoi_add_right, ← regroupChoi_add_left,
    omegaComplement_add_projection, regroupChoi_one_one]

/-- Spectral-sector decomposition of the two-copy witness. -/
theorem productReductionChoi_inv_eq_twoCopySectors
    {r : ℕ} (hr : 0 < r) (hT : 0 < Fintype.card T) :
    productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ))
      = twoCopySectorCC (T := T)
        - ((traceSeparationGamma (T := T) r : ℝ) : ℂ) •
            (twoCopySectorCP (T := T) + twoCopySectorPC (T := T))
        + (((traceSeparationGamma (T := T) r) ^ 2 : ℝ) : ℂ) •
            twoCopySectorPP (T := T) := by
  rw [productReductionChoi, reductionChoi_inv_eq_complement_sub_gamma hr hT,
    regroupChoi_sub_left, regroupChoi_sub_right, regroupChoi_sub_right,
    regroupChoi_smul_left, regroupChoi_smul_right, regroupChoi_smul_right,
    regroupChoi_smul_left]
  simp only [twoCopySectorCC, twoCopySectorCP, twoCopySectorPC, twoCopySectorPP]
  module

/-- The four sector quadratic forms resolve the squared norm. -/
theorem re_qform_twoCopySectors_sum
    (x : EuclideanSpace ℂ ((T × T) × (T × T))) :
    (qform (twoCopySectorCC (T := T)) x).re
        + (qform (twoCopySectorCP (T := T)) x).re
        + (qform (twoCopySectorPC (T := T)) x).re
        + (qform (twoCopySectorPP (T := T)) x).re
      = ‖x‖ ^ 2 := by
  have h := congrArg
    (fun A : Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ =>
      (qform A x).re) (twoCopySectors_sum (T := T))
  simpa only [qform_add, Complex.add_re, qform_one, Complex.ofReal_re] using h

/-- The tensor-square witness quadratic form in its four spectral sectors. -/
theorem re_qform_productReductionChoi_inv
    {r : ℕ} (hr : 0 < r) (hT : 0 < Fintype.card T)
    (x : EuclideanSpace ℂ ((T × T) × (T × T))) :
    (qform
      (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ))) x).re
      = (qform (twoCopySectorCC (T := T)) x).re
        - traceSeparationGamma (T := T) r *
            ((qform (twoCopySectorCP (T := T)) x).re
              + (qform (twoCopySectorPC (T := T)) x).re)
        + (traceSeparationGamma (T := T) r) ^ 2 *
            (qform (twoCopySectorPP (T := T)) x).re := by
  rw [productReductionChoi_inv_eq_twoCopySectors hr hT, qform_add, qform_sub,
    qform_smul, qform_smul, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [qform_add, Complex.add_re]

/-- The lower and upper spectral bounds of the two-copy witness. -/
theorem re_qform_productReductionChoi_inv_mem
    {r : ℕ} (hr : 0 < r) (hrT : r < Fintype.card T)
    (x : EuclideanSpace ℂ ((T × T) × (T × T))) (hx : ‖x‖ = 1) :
    -traceSeparationGamma (T := T) r
        ≤ (qform
          (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ)))
          x).re
      ∧
      (qform
          (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ)))
          x).re
        ≤ max 1 ((traceSeparationGamma (T := T) r) ^ 2) := by
  have hT : 0 < Fintype.card T := by omega
  let γ := traceSeparationGamma (T := T) r
  let a := (qform (twoCopySectorCC (T := T)) x).re
  let b := (qform (twoCopySectorCP (T := T)) x).re
  let c := (qform (twoCopySectorPC (T := T)) x).re
  let d := (qform (twoCopySectorPP (T := T)) x).re
  have ha : 0 ≤ a :=
    qform_re_nonneg_of_posSemidef (twoCopySectorCC_posSemidef hT) x
  have hb : 0 ≤ b :=
    qform_re_nonneg_of_posSemidef (twoCopySectorCP_posSemidef hT) x
  have hc : 0 ≤ c :=
    qform_re_nonneg_of_posSemidef (twoCopySectorPC_posSemidef hT) x
  have hd : 0 ≤ d :=
    qform_re_nonneg_of_posSemidef (twoCopySectorPP_posSemidef hT) x
  have hsum : a + b + c + d = 1 := by
    have h := re_qform_twoCopySectors_sum (T := T) x
    rw [hx, one_pow] at h
    exact h
  have hγ : 0 < γ := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hrTR : (r : ℝ) < Fintype.card T := by exact_mod_cast hrT
    dsimp only [γ, traceSeparationGamma]
    rw [sub_pos, one_lt_div hrR]
    exact hrTR
  have hq :
      (qform
        (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ)))
        x).re = a - γ * (b + c) + γ ^ 2 * d := by
    exact re_qform_productReductionChoi_inv hr hT x
  have hM1 : 1 ≤ max 1 (γ ^ 2) := le_max_left _ _
  have hMγ : γ ^ 2 ≤ max 1 (γ ^ 2) := le_max_right _ _
  have hM0 : 0 ≤ max 1 (γ ^ 2) := (zero_le_one.trans hM1)
  constructor
  · rw [hq]
    nlinarith [sq_nonneg γ]
  · rw [hq]
    nlinarith

/-- The midpoint-centered witness has operator bound half its spectral
diameter. -/
theorem abs_re_qform_twoCopyWitness_centered_le
    {r : ℕ} (hr : 0 < r) (hrT : r < Fintype.card T)
    (x : EuclideanSpace ℂ ((T × T) × (T × T))) (hx : ‖x‖ = 1) :
    let γ := traceSeparationGamma (T := T) r
    let M := max 1 (γ ^ 2)
    let center := (M - γ) / 2
    |(qform
        (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ))
          - (center : ℂ) • 1) x).re|
      ≤ traceSeparationDelta (T := T) r / 2 := by
  dsimp only
  let γ := traceSeparationGamma (T := T) r
  let M := max 1 (γ ^ 2)
  have hmem := re_qform_productReductionChoi_inv_mem hr hrT x hx
  have hγ : 0 < γ := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hrTR : (r : ℝ) < Fintype.card T := by exact_mod_cast hrT
    dsimp only [γ, traceSeparationGamma]
    rw [sub_pos, one_lt_div hrR]
    exact hrTR
  rw [qform_sub, qform_smul, qform_one, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hx, one_pow]
  rw [abs_le]
  dsimp only [traceSeparationDelta, γ, M] at hmem ⊢
  constructor <;> nlinarith

end TwoCopySpectrum

section TwoCopyTraceDistance

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- `cor:two-copy-trace-distance`, pointwise in the comparison state.

As elsewhere in the development, writing the lower bound for every admissible
`σ` is equivalent to the displayed infimum statement and avoids an unrelated
extended-real `sInf` layer.  The norm is the Hermitian trace norm, which is the
sum of the absolute eigenvalues of the Hermitian difference `σ - ρ`. -/
theorem twoCopy_traceDistance_lower
    {r : ℕ} (hr : 0 < r) (hrT : r < Fintype.card T)
    {ρ σ : Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hSN : SchmidtNumberLE (W := T × T) r σ)
    {ε : ℝ}
    (hdetect :
      ((productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ))
          * ρ).trace).re = -ε) :
    2 * ε / traceSeparationDelta (T := T) r
      ≤ hermitianTraceNorm (σ - ρ) (hσ.1.isHermitian.sub hρ.1.isHermitian) := by
  have hTtwo : 2 ≤ Fintype.card T := by omega
  have ht0 : 0 ≤ 1 / (r : ℝ) :=
    one_div_nonneg.mpr (by exact_mod_cast hr.le)
  have hBlock :
      IsBlockPositive r
        (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ))) := by
    apply (isBlockPositive_productReductionChoi_self_iff_le_inv_min
      hr hTtwo ht0).mpr
    rw [min_eq_left]
    exact_mod_cast (Nat.le_of_lt hrT)
  let γ := traceSeparationGamma (T := T) r
  let M := max 1 (γ ^ 2)
  let center := (M - γ) / 2
  have hγ : 0 < γ := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hrTR : (r : ℝ) < Fintype.card T := by exact_mod_cast hrT
    dsimp only [γ, traceSeparationGamma]
    rw [sub_pos, one_lt_div hrR]
    exact hrTR
  have hΔ : 0 < traceSeparationDelta (T := T) r := by
    dsimp only [traceSeparationDelta, γ, M]
    have hM : 0 ≤ max 1 (γ ^ 2) := le_max_left 1 (γ ^ 2) |>.trans' zero_le_one
    linarith
  exact two_mul_div_le_hermitianTraceNorm_of_witness
    (productReductionChoi_isHermitian (U := T) (V := T) _ _)
    hBlock hρ hσ hSN hΔ hdetect
    (abs_re_qform_twoCopyWitness_centered_le hr hrT)

end TwoCopyTraceDistance

end RankR
