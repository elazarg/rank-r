/-
Balanced finite-rank matrix factorizations.

A balanced factorization has identical left and right Gram matrices, and each
rank-one summand contributes the same scalar to the trace.
-/
import RankR.Library.Matrix.Rank
import RankR.Library.Matrix.ConstantDiagonal
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef

namespace RankR

open Matrix Finset ComplexConjugate

/-- Two rank-factor families have the same Gram matrix. -/
def IsEqualGramRankFactor {W : Type*} [Fintype W] {q : ℕ}
    (e d : Fin q → EuclideanSpace ℂ W) : Prop :=
  ∀ i j, inner ℂ (e i) (e j) = inner ℂ (d i) (d j)

/-- A rank factorization whose left and right families have the same Gram
matrix and whose trace contributions are all equal. -/
def IsBalancedRankFactor {W : Type*} [Fintype W] {q : ℕ}
    (e d : Fin q → EuclideanSpace ℂ W) (τ : ℂ) : Prop :=
  IsEqualGramRankFactor e d ∧ ∀ i, inner ℂ (d i) (e i) = τ

/-- A matrix admits an equal-Gram factorization indexed by its exact rank. -/
def HasEqualGramRankFactorization {W : Type*} [Fintype W]
    (C : Matrix W W ℂ) : Prop :=
  ∃ (e d : Fin C.rank → EuclideanSpace ℂ W),
    C = rankFactor e d ∧ IsEqualGramRankFactor e d

/-- A matrix admits a balanced factorization indexed by its exact rank. -/
def HasBalancedRankFactorization {W : Type*} [Fintype W]
    (C : Matrix W W ℂ) : Prop :=
  ∃ (e d : Fin C.rank → EuclideanSpace ℂ W) (τ : ℂ),
    C = rankFactor e d ∧ IsBalancedRankFactor e d τ

/-- A matrix class has balanced factorizations if every matrix in the class
admits one at its exact rank. -/
def HasBalancedRankFactorizations (W : Type*) [Fintype W] : Prop :=
  ∀ C : Matrix W W ℂ, HasBalancedRankFactorization C

section Mixing

variable {W : Type*} [Fintype W] {q : ℕ}

/-- Mix the members of a finite vector family by the columns of a matrix. -/
noncomputable def mixRankFamily
    (e : Fin q → EuclideanSpace ℂ W) (U : Matrix (Fin q) (Fin q) ℂ) :
    Fin q → EuclideanSpace ℂ W :=
  fun i => ∑ j, U j i • e j

/-- The Gram matrix of a finite vector family. -/
noncomputable def rankFamilyGram
    (e : Fin q → EuclideanSpace ℂ W) : Matrix (Fin q) (Fin q) ℂ :=
  Matrix.gram ℂ e

/-- The cross-Gram matrix whose diagonal entries are the trace contributions
of a rank factorization. -/
noncomputable def rankFactorCrossGram
    (e d : Fin q → EuclideanSpace ℂ W) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j => inner ℂ (d i) (e j)

@[simp]
theorem rankFamilyGram_apply
    (e : Fin q → EuclideanSpace ℂ W) (i j : Fin q) :
    rankFamilyGram e i j = inner ℂ (e i) (e j) :=
  rfl

@[simp]
theorem rankFactorCrossGram_apply
    (e d : Fin q → EuclideanSpace ℂ W) (i j : Fin q) :
    rankFactorCrossGram e d i j = inner ℂ (d i) (e j) :=
  rfl

/-- The trace of a Gram matrix is the total squared norm of the family. -/
theorem trace_rankFamilyGram
    (e : Fin q → EuclideanSpace ℂ W) :
    (rankFamilyGram e).trace = ((∑ i, ‖e i‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  exact Finset.sum_congr rfl fun i _ => inner_self_eq_norm_sq_to_K (e i)

/-- The squared Hilbert--Schmidt norm of a Gram matrix is the total squared
modulus of its entries. -/
theorem hsNormSq_rankFamilyGram
    (e : Fin q → EuclideanSpace ℂ W) :
    hsNormSq (rankFamilyGram e) =
      ∑ i, ∑ j, Complex.normSq (inner ℂ (e i) (e j)) :=
  rfl

/-- Centering a Gram matrix removes the squared mean of its diagonal. -/
theorem hsNormSq_centered_rankFamilyGram
    (e : Fin q → EuclideanSpace ℂ W) (hq : 0 < q) :
    hsNormSq
        (rankFamilyGram e
          - ((rankFamilyGram e).trace / (q : ℂ))
              • (1 : Matrix (Fin q) (Fin q) ℂ)) =
      (∑ i, ∑ j, Complex.normSq (inner ℂ (e i) (e j)))
        - (∑ i, ‖e i‖ ^ 2) ^ 2 / (q : ℝ) := by
  have hcenter := hsNormSq_sub_trace_smul_one
    (rankFamilyGram e) (by simpa using hq)
  simp only [Fintype.card_fin] at hcenter
  rw [hcenter, hsNormSq_rankFamilyGram, trace_rankFamilyGram,
    Complex.normSq_ofReal]
  ring

/-- In a balanced factorization, the trace is the number of summands times
their common scalar overlap. -/
theorem trace_rankFactor_of_isBalanced
    {e d : Fin q → EuclideanSpace ℂ W} {τ : ℂ}
    (hbal : IsBalancedRankFactor e d τ) :
    (rankFactor e d).trace = (q : ℂ) * τ := by
  rw [contraction_trace]
  simp_rw [hbal.2]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Mixing a family conjugates its Gram matrix. -/
theorem rankFamilyGram_mixRankFamily
    (e : Fin q → EuclideanSpace ℂ W) (U : Matrix (Fin q) (Fin q) ℂ) :
    rankFamilyGram (mixRankFamily e U) = Uᴴ * rankFamilyGram e * U := by
  ext i j
  simp only [rankFamilyGram_apply, mixRankFamily, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Simultaneous mixing conjugates the cross-Gram matrix. -/
theorem rankFactorCrossGram_mixRankFamily
    (e d : Fin q → EuclideanSpace ℂ W) (U : Matrix (Fin q) (Fin q) ℂ) :
    rankFactorCrossGram (mixRankFamily e U) (mixRankFamily d U)
      = Uᴴ * rankFactorCrossGram e d * U := by
  ext i j
  simp only [rankFactorCrossGram_apply, mixRankFamily, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype W] in
/-- Simultaneous unitary mixing leaves a rank factorization unchanged. -/
theorem rankFactor_mixRankFamily
    (e d : Fin q → EuclideanSpace ℂ W) (U : Matrix (Fin q) (Fin q) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin q) ℂ) :
    rankFactor (mixRankFamily e U) (mixRankFamily d U) = rankFactor e d := by
  have hrow : U * Uᴴ = (1 : Matrix (Fin q) (Fin q) ℂ) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  ext p r
  rw [rankFactor_apply, rankFactor_apply]
  have heval (i : Fin q) :
      mixRankFamily e U i p = ∑ j, U j i * e j p := by
    change WithLp.ofLp (∑ j, U j i • e j) p = _
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    rfl
  have hdeval (i : Fin q) :
      mixRankFamily d U i r = ∑ k, U k i * d k r := by
    change WithLp.ofLp (∑ k, U k i • d k) r = _
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    rfl
  simp_rw [heval, hdeval]
  simp only [map_sum, map_mul]
  simp_rw [Finset.sum_mul_sum]
  calc
    (∑ i, ∑ j, ∑ k,
        U j i * e j p * (conj (U k i) * conj (d k r)))
        = ∑ j, ∑ i, ∑ k,
            U j i * e j p * (conj (U k i) * conj (d k r)) :=
      Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i,
        U j i * e j p * (conj (U k i) * conj (d k r)) := by
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ k,
        e j p * (∑ i, U j i * conj (U k i)) * conj (d k r) := by
          refine Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => ?_
          calc
            ∑ i, U j i * e j p * (conj (U k i) * conj (d k r))
                = ∑ i, e j p * (U j i * conj (U k i)) * conj (d k r) :=
              Finset.sum_congr rfl fun i _ => by ring
            _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = ∑ j, ∑ k, e j p * (1 : Matrix (Fin q) (Fin q) ℂ) j k * conj (d k r) := by
      refine Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => ?_
      have hjk : ∑ i, U j i * conj (U k i)
          = (1 : Matrix (Fin q) (Fin q) ℂ) j k := by
        simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
          RCLike.star_def] using congrFun (congrFun hrow j) k
      rw [hjk]
    _ = ∑ j, e j p * conj (d j r) := by
      simp [Matrix.one_apply]

/-- Spectral mixing makes the right Gram matrix diagonal while keeping an
orthonormal left family orthonormal. -/
theorem exists_spectral_mixRankFamily
    (e d : Fin q → EuclideanSpace ℂ W) (he : Orthonormal ℂ e) :
    ∃ (e' d' : Fin q → EuclideanSpace ℂ W) (lam : Fin q → ℝ),
      rankFactor e d = rankFactor e' d'
        ∧ rankFamilyGram e' = 1
        ∧ rankFamilyGram d' = Matrix.diagonal (RCLike.ofReal ∘ lam)
        ∧ ∀ i, 0 ≤ lam i := by
  classical
  let G := rankFamilyGram d
  have hG : G.IsHermitian := by
    exact Matrix.isHermitian_gram ℂ d
  let U : Matrix (Fin q) (Fin q) ℂ := hG.eigenvectorUnitary
  let lam : Fin q → ℝ := hG.eigenvalues
  have hU : U ∈ Matrix.unitaryGroup (Fin q) ℂ :=
    SetLike.coe_mem hG.eigenvectorUnitary
  have hGramE : rankFamilyGram e = 1 := by
    ext i j
    rw [rankFamilyGram_apply, Matrix.one_apply]
    exact orthonormal_iff_ite.mp he i j
  have hmixE : rankFamilyGram (mixRankFamily e U) = 1 := by
    rw [rankFamilyGram_mixRankFamily, hGramE, Matrix.mul_one]
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hmixD :
      rankFamilyGram (mixRankFamily d U) =
        Matrix.diagonal (RCLike.ofReal ∘ lam) := by
    rw [rankFamilyGram_mixRankFamily]
    have hspectral := hG.conjStarAlgAut_star_eigenvectorUnitary
    simpa only [G, U, lam, Unitary.conjStarAlgAut_star_apply,
      Matrix.star_eq_conjTranspose] using hspectral
  have hlam : ∀ i, 0 ≤ lam i := by
    intro i
    exact (Matrix.posSemidef_gram ℂ d).eigenvalues_nonneg i
  exact ⟨mixRankFamily e U, mixRankFamily d U, lam,
    (rankFactor_mixRankFamily e d U hU).symm, hmixE, hmixD, hlam⟩

/-- The positive fourth-root scale that equalizes the two diagonal Gram
entries in a spectral rank factorization. -/
noncomputable def gramQuarterRoot (lam : Fin q → ℝ) (i : Fin q) : ℝ :=
  √(√(lam i))

/-- Scale the orthonormal side of a spectral factorization. -/
noncomputable def balanceSpectralLeft
    (e : Fin q → EuclideanSpace ℂ W) (lam : Fin q → ℝ) :
    Fin q → EuclideanSpace ℂ W :=
  fun i => (gramQuarterRoot lam i : ℂ) • e i

/-- Inversely scale the orthogonal side of a spectral factorization.  The
inverse of zero is zero, so zero-eigenvalue summands vanish on both sides. -/
noncomputable def balanceSpectralRight
    (d : Fin q → EuclideanSpace ℂ W) (lam : Fin q → ℝ) :
    Fin q → EuclideanSpace ℂ W :=
  fun i => ((gramQuarterRoot lam i : ℂ)⁻¹) • d i

/-- Spectral fourth-root scaling turns an orthonormal/orthogonal
factorization into an equal-Gram factorization without changing its sum. -/
theorem spectralBalance_isEqualGram
    (e d : Fin q → EuclideanSpace ℂ W) (lam : Fin q → ℝ)
    (hE : rankFamilyGram e = 1)
    (hD : rankFamilyGram d = Matrix.diagonal (RCLike.ofReal ∘ lam))
    (hlam : ∀ i, 0 ≤ lam i) :
    rankFactor e d =
        rankFactor (balanceSpectralLeft e lam) (balanceSpectralRight d lam)
      ∧ IsEqualGramRankFactor
        (balanceSpectralLeft e lam) (balanceSpectralRight d lam) := by
  have hEij : ∀ i j, inner ℂ (e i) (e j) = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun hE i) j
    simpa only [rankFamilyGram_apply, Matrix.one_apply] using h
  have hDij : ∀ i j, inner ℂ (d i) (d j) =
      if i = j then RCLike.ofReal (lam i) else 0 := by
    intro i j
    have h := congrFun (congrFun hD i) j
    simpa [rankFamilyGram_apply, Matrix.diagonal_apply, Function.comp_apply] using h
  have hterm : ∀ i,
      rankOne (balanceSpectralLeft e lam i) (balanceSpectralRight d lam i)
        = rankOne (e i) (d i) := by
    intro i
    by_cases hi : lam i = 0
    · have hd0 : d i = 0 := by
        apply norm_eq_zero.mp
        have h := hDij i i
        rw [if_pos rfl, inner_self_eq_norm_sq_to_K, hi] at h
        have hsq : ‖d i‖ ^ 2 = 0 := by exact_mod_cast h
        nlinarith [sq_nonneg ‖d i‖]
      ext p r
      simp [balanceSpectralLeft, balanceSpectralRight, rankOne,
        gramQuarterRoot, hi, hd0]
    · have hpos : 0 < lam i := lt_of_le_of_ne (hlam i) (Ne.symm hi)
      have hroot : gramQuarterRoot lam i ≠ 0 := by
        exact ne_of_gt (Real.sqrt_pos.2 (Real.sqrt_pos.2 hpos))
      have hrootC : (gramQuarterRoot lam i : ℂ) ≠ 0 := by
        exact_mod_cast hroot
      ext p r
      change (gramQuarterRoot lam i : ℂ) * e i p *
          conj ((gramQuarterRoot lam i : ℂ)⁻¹ * d i r) =
        e i p * conj (d i r)
      calc
        _ = (gramQuarterRoot lam i : ℂ) * e i p *
            ((gramQuarterRoot lam i : ℂ)⁻¹ * conj (d i r)) := by
              rw [map_mul, map_inv₀]
              simp only [Complex.conj_ofReal]
        _ = _ := by field_simp
  constructor
  · rw [rankFactor_eq_sum, rankFactor_eq_sum]
    exact Finset.sum_congr rfl fun i _ => (hterm i).symm
  · intro i j
    by_cases hij : i = j
    · subst j
      by_cases hi : lam i = 0
      · simp [balanceSpectralLeft, balanceSpectralRight, gramQuarterRoot, hi]
      · have hpos : 0 < lam i := lt_of_le_of_ne (hlam i) (Ne.symm hi)
        have ha : 0 < gramQuarterRoot lam i :=
          Real.sqrt_pos.2 (Real.sqrt_pos.2 hpos)
        have ha2 : gramQuarterRoot lam i ^ 2 = √(lam i) := by
          exact Real.sq_sqrt (Real.sqrt_nonneg _)
        have hs2 : (√(lam i)) ^ 2 = lam i := Real.sq_sqrt (hlam i)
        have ha4 : gramQuarterRoot lam i ^ 4 = lam i := by
          calc
            gramQuarterRoot lam i ^ 4 =
                (gramQuarterRoot lam i ^ 2) ^ 2 := by ring
            _ = lam i := by rw [ha2, hs2]
        have hreal :
            gramQuarterRoot lam i * gramQuarterRoot lam i =
              (gramQuarterRoot lam i)⁻¹ *
                ((gramQuarterRoot lam i)⁻¹ * lam i) := by
          field_simp [ne_of_gt ha]
          nlinarith
        have hcomplex :
            (gramQuarterRoot lam i : ℂ) * (gramQuarterRoot lam i : ℂ) =
              (gramQuarterRoot lam i : ℂ)⁻¹ *
                ((gramQuarterRoot lam i : ℂ)⁻¹ * (lam i : ℂ)) := by
          exact_mod_cast hreal
        calc
          inner ℂ (balanceSpectralLeft e lam i)
              (balanceSpectralLeft e lam i) =
              conj (gramQuarterRoot lam i : ℂ) *
                ((gramQuarterRoot lam i : ℂ) * inner ℂ (e i) (e i)) := by
                  rw [balanceSpectralLeft,
                    inner_smul_left, inner_smul_right]
          _ = (gramQuarterRoot lam i : ℂ) *
                (gramQuarterRoot lam i : ℂ) := by
                  rw [hEij i i, if_pos rfl]
                  simp only [Complex.conj_ofReal, mul_one]
          _ = (gramQuarterRoot lam i : ℂ)⁻¹ *
                ((gramQuarterRoot lam i : ℂ)⁻¹ * (lam i : ℂ)) :=
            hcomplex
          _ = conj ((gramQuarterRoot lam i : ℂ)⁻¹) *
                ((gramQuarterRoot lam i : ℂ)⁻¹ * inner ℂ (d i) (d i)) := by
                  rw [hDij i i, if_pos rfl]
                  simp only [map_inv₀, Complex.conj_ofReal]
                  rfl
          _ = inner ℂ (balanceSpectralRight d lam i)
                (balanceSpectralRight d lam i) := by
                  rw [balanceSpectralRight,
                    inner_smul_left, inner_smul_right]
    · calc
        inner ℂ (balanceSpectralLeft e lam i)
            (balanceSpectralLeft e lam j) =
            conj (gramQuarterRoot lam i : ℂ) *
              ((gramQuarterRoot lam j : ℂ) * inner ℂ (e i) (e j)) := by
                simp only [balanceSpectralLeft]
                rw [inner_smul_left, inner_smul_right]
        _ = 0 := by rw [hEij i j, if_neg hij, mul_zero, mul_zero]
        _ = conj ((gramQuarterRoot lam i : ℂ)⁻¹) *
              ((gramQuarterRoot lam j : ℂ)⁻¹ * inner ℂ (d i) (d j)) := by
                rw [hDij i j, if_neg hij, mul_zero, mul_zero]
        _ = inner ℂ (balanceSpectralRight d lam i)
              (balanceSpectralRight d lam j) := by
                simp only [balanceSpectralRight]
                rw [inner_smul_left, inner_smul_right]

end Mixing

section Balance

variable {W : Type*} [Fintype W] {q : ℕ}

/-- Every square complex matrix has an equal-Gram factorization indexed by
its exact rank. -/
theorem hasEqualGramRankFactorization (C : Matrix W W ℂ) :
    HasEqualGramRankFactorization C := by
  obtain ⟨e, d, he, hC⟩ := exists_rankFactor_rank C
  obtain ⟨e', d', lam, hspectral, hE, hD, hlam⟩ :=
    exists_spectral_mixRankFamily e d he
  obtain ⟨hscale, hG⟩ :=
    spectralBalance_isEqualGram e' d' lam hE hD hlam
  exact ⟨balanceSpectralLeft e' lam, balanceSpectralRight d' lam,
    hC.trans (hspectral.trans hscale), hG⟩

/-- Constant-diagonal unitary mixing balances an equal-Gram factorization. -/
theorem exists_balanced_mixRankFamily
    (e d : Fin q → EuclideanSpace ℂ W)
    (hG : IsEqualGramRankFactor e d)
    (hdiag : HasConstantDiagonal (rankFactorCrossGram e d)) :
    ∃ (e' d' : Fin q → EuclideanSpace ℂ W) (τ : ℂ),
      rankFactor e d = rankFactor e' d' ∧ IsBalancedRankFactor e' d' τ := by
  obtain ⟨U, hU, hdiag⟩ := hdiag
  refine ⟨mixRankFamily e U, mixRankFamily d U,
    (rankFactorCrossGram e d).trace / (q : ℂ), ?_, ?_⟩
  · exact (rankFactor_mixRankFamily e d U hU).symm
  · constructor
    · have hGram : rankFamilyGram e = rankFamilyGram d := by
        ext i j
        exact hG i j
      intro i j
      change rankFamilyGram (mixRankFamily e U) i j =
        rankFamilyGram (mixRankFamily d U) i j
      rw [rankFamilyGram_mixRankFamily, rankFamilyGram_mixRankFamily, hGram]
    · intro i
      change rankFactorCrossGram (mixRankFamily e U) (mixRankFamily d U) i i =
        (rankFactorCrossGram e d).trace / (q : ℂ)
      rw [rankFactorCrossGram_mixRankFamily]
      exact hdiag i

/-- Equal-Gram exact-rank factorizations and the constant-diagonal property
produce balanced exact-rank factorizations. -/
theorem hasBalancedRankFactorization_of_equalGram_of_constantDiagonals
    {C : Matrix W W ℂ}
    (hfac : HasEqualGramRankFactorization C)
    (hdiag : HasConstantDiagonals C.rank) :
    HasBalancedRankFactorization C := by
  obtain ⟨e, d, hC, hG⟩ := hfac
  obtain ⟨e', d', τ, hmix, hbal⟩ :=
    exists_balanced_mixRankFamily e d hG
      (hdiag (rankFactorCrossGram e d))
  exact ⟨e', d', τ, hC.trans hmix, hbal⟩

/-- The constant-diagonal property in the matrix rank produces a balanced
exact-rank factorization. -/
theorem hasBalancedRankFactorization_of_constantDiagonals
    (C : Matrix W W ℂ) (hdiag : HasConstantDiagonals C.rank) :
    HasBalancedRankFactorization C :=
  hasBalancedRankFactorization_of_equalGram_of_constantDiagonals
    (hasEqualGramRankFactorization C) hdiag

/-- Constant diagonals in every dimension give balanced exact-rank
factorizations for every square matrix on `W`. -/
theorem hasBalancedRankFactorizations_of_constantDiagonals
    (hdiag : ∀ q, HasConstantDiagonals q) :
    HasBalancedRankFactorizations W :=
  fun C => hasBalancedRankFactorization_of_constantDiagonals C (hdiag C.rank)

/-- Every square complex matrix has a balanced exact-rank factorization. -/
theorem hasBalancedRankFactorization (C : Matrix W W ℂ) :
    HasBalancedRankFactorization C :=
  hasBalancedRankFactorization_of_constantDiagonals C
    (hasConstantDiagonals C.rank)

/-- Every square complex matrix on `W` has a balanced exact-rank
factorization. -/
theorem hasBalancedRankFactorizations :
    HasBalancedRankFactorizations W :=
  fun C => hasBalancedRankFactorization C

end Balance

end RankR
