/-
Balanced finite-rank matrix factorizations.

A balanced factorization has identical left and right Gram matrices, and each
rank-one summand contributes the same scalar to the trace.
-/
import RankR.Library.Matrix.Rank

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
  fun i j => inner ℂ (e i) (e j)

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

end Mixing

section ConstantDiagonal

variable {q : ℕ}

/-- A matrix has a constant diagonal up to unitary similarity. -/
def HasConstantDiagonal (A : Matrix (Fin q) (Fin q) ℂ) : Prop :=
  ∃ U : Matrix (Fin q) (Fin q) ℂ,
    U ∈ Matrix.unitaryGroup (Fin q) ℂ
      ∧ ∀ i, (Uᴴ * A * U) i i = A.trace / (q : ℂ)

/-- The Parker--Fillmore property in a fixed dimension. -/
def HasConstantDiagonals (q : ℕ) : Prop :=
  ∀ A : Matrix (Fin q) (Fin q) ℂ, HasConstantDiagonal A

/-- The constant-diagonal property in dimension zero. -/
theorem hasConstantDiagonals_zero : HasConstantDiagonals 0 := by
  intro A
  refine ⟨1, by simp, ?_⟩
  intro i
  exact Fin.elim0 i

/-- The constant-diagonal property in dimension one. -/
theorem hasConstantDiagonals_one : HasConstantDiagonals 1 := by
  intro A
  refine ⟨1, by simp, ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [Matrix.trace]

end ConstantDiagonal

section Balance

variable {W : Type*} [Fintype W] {q : ℕ}

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

end Balance

end RankR
