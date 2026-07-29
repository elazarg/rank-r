/-
Range factorization: from a matrix `C`, produce orthonormal `eᵢ` spanning
`range C` and columns `dᵢ` with `C = rankFactor e d`.

Section 3 of the manuscript opens by choosing "an orthonormal basis `{eᵢ}` of
`ran C`" and setting `dᵢ := C* eᵢ`; this supplies both.
-/
import RankR.Library.Matrix.Elementary

namespace RankR

open Matrix Finset ComplexConjugate

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The `q`-th column of `C`, as a vector. -/
def col (C : Matrix W W ℂ) (q : W) : EuclideanSpace ℂ W :=
  WithLp.toLp 2 (fun p => C p q)

omit [Fintype W] [DecidableEq W] in
@[simp] theorem col_apply (C : Matrix W W ℂ) (q p : W) : col C q p = C p q := rfl

theorem col_mem_range (C : Matrix W W ℂ) (q : W) :
    col C q ∈ LinearMap.range (Matrix.toEuclideanLin C) := by
  refine ⟨EuclideanSpace.single q 1, ?_⟩
  ext p
  simp [Matrix.mulVec, dotProduct, col, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq']

/-- **Range factorization.**  Every `C` factors as `∑ᵢ |eᵢ⟩⟨dᵢ|` with `{eᵢ}` an
orthonormal basis of `range C`, indexed by `Fin (finrank (range C))`. -/
theorem exists_rankFactor (C : Matrix W W ℂ) :
    ∃ (e d : Fin (Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin C))) →
        EuclideanSpace ℂ W),
      Orthonormal ℂ e ∧ C = rankFactor e d := by
  classical
  set R := LinearMap.range (Matrix.toEuclideanLin C) with hR
  set b := stdOrthonormalBasis ℂ R with hb
  refine ⟨fun i => (b i : EuclideanSpace ℂ W),
    fun i => WithLp.toLp 2 (fun q => ∑ p, conj (C p q) * (b i : EuclideanSpace ℂ W) p),
    ?_, ?_⟩
  · constructor
    · intro i
      exact b.orthonormal.1 i
    · intro i j hij
      exact b.orthonormal.2 hij
  · ext p q
    have hy : (⟨col C q, col_mem_range C q⟩ : R) = ∑ i, (inner ℂ (b i)
        (⟨col C q, col_mem_range C q⟩ : R)) • b i := (b.sum_repr' _).symm
    have hcoe := congrArg (fun y : R => (y : EuclideanSpace ℂ W) p) hy
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hcoe
    rw [rankFactor_apply]
    have hinner : ∀ i, inner ℂ (b i) (⟨col C q, col_mem_range C q⟩ : R)
        = ∑ p', conj ((b i : EuclideanSpace ℂ W) p') * C p' q := by
      intro i
      have hEq : inner ℂ (b i) (⟨col C q, col_mem_range C q⟩ : R)
          = inner ℂ ((b i : EuclideanSpace ℂ W)) (col C q) := rfl
      rw [hEq, PiLp.inner_apply]
      exact Finset.sum_congr rfl fun p' _ => by
        rw [RCLike.inner_apply']
        rfl
    simp only [hinner] at hcoe
    simpa [mul_comm] using hcoe

end RankR
