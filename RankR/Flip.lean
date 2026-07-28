/-
The two partial transposes on `L(U ⊗ V)`, and the quadratic form of the double
antisymmetrizer written in terms of them.

`Qm` is defined in `Antisym.lean` through the index swaps `swU` and `swV`.  At
the level of matrices those swaps are the two partial transposes: `flipU N` has
the two `U` indices of `N` exchanged and `flipV N` the two `V` indices, so that
`vec (flipU N) = vec N ∘ swU` and likewise for `V`, while their composite is the
ordinary transpose.  Expanding `qform Qm (vec N)` over the resulting Klein
four-group orbit gives

  `⟨N, Π N⟩ = ¼ (‖N‖₂² − ⟨N, N^{T_U}⟩ − ⟨N, N^{T_V}⟩ + ⟨N, Nᵀ⟩)`,

and when `N` is symmetric the first and last terms coincide and so do the two
middle ones, leaving

  `⟨N, Π N⟩ = ½ (‖N‖₂² − ⟨N, N^{T_U}⟩).`

That identity is Fu-Gao-Park's Lemma 2.3 in matrix form: it turns their
projection bound into the single scalar assertion `⟨N, N^{T_U}⟩ ≥ 0`.
-/
import RankR.Antisym

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## The two partial transposes

Rearrangements of the four indices, matching the swaps of `Antisym.lean` entry by
entry, so this section carries no instances. -/

section Flip

variable {U V : Type*}

/-- Partial transposition on the `U` factor: exchange the two `U` indices,
keeping the two `V` indices in place. -/
def flipU (N : Matrix (U × V) (U × V) ℂ) : Matrix (U × V) (U × V) ℂ :=
  Matrix.of fun p q => N (q.1, p.2) (p.1, q.2)

@[simp] theorem flipU_apply (N : Matrix (U × V) (U × V) ℂ) (p q : U × V) :
    flipU N p q = N (q.1, p.2) (p.1, q.2) := rfl

/-- Partial transposition on the `V` factor. -/
def flipV (N : Matrix (U × V) (U × V) ℂ) : Matrix (U × V) (U × V) ℂ :=
  Matrix.of fun p q => N (p.1, q.2) (q.1, p.2)

@[simp] theorem flipV_apply (N : Matrix (U × V) (U × V) ℂ) (p q : U × V) :
    flipV N p q = N (p.1, q.2) (q.1, p.2) := rfl

/-- The vectorization of `flipU N` is that of `N` precomposed with `swU`. -/
theorem vec_flipU (N : Matrix (U × V) (U × V) ℂ) (X : Idx U V) :
    vec (flipU N) X = vec N (swU X) := rfl

/-- The vectorization of `flipV N` is that of `N` precomposed with `swV`. -/
theorem vec_flipV (N : Matrix (U × V) (U × V) ℂ) (X : Idx U V) :
    vec (flipV N) X = vec N (swV X) := rfl

/-- The composite of the two swaps is the ordinary transpose. -/
theorem vec_transpose (N : Matrix (U × V) (U × V) ℂ) (X : Idx U V) :
    vec Nᵀ X = vec N (swV (swU X)) := rfl

/-- For a symmetric `N` the two partial transposes agree. -/
theorem flipV_eq_flipU {N : Matrix (U × V) (U × V) ℂ} (hN : Nᵀ = N) :
    flipV N = flipU N := by
  have h : ∀ x y : U × V, N x y = N y x := fun x y => by
    have hxy := congrFun (congrFun hN y) x
    rwa [Matrix.transpose_apply] at hxy
  ext p q
  simp only [flipV_apply, flipU_apply]
  exact h _ _

end Flip

section Expansion

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- The quadratic form of the double antisymmetrizer, as the four-term
alternating combination of `N` with its two partial transposes and its
transpose. -/
theorem qform_Qm_vec (N : Matrix (U × V) (U × V) ℂ) :
    qform Qm (vec N)
      = (4 : ℂ)⁻¹ * (hsInner N N - hsInner N (flipU N) - hsInner N (flipV N)
          + hsInner N Nᵀ) := by
  rw [qform_Qm_eq, hsInner_eq_sum_vec, hsInner_eq_sum_vec, hsInner_eq_sum_vec,
    hsInner_eq_sum_vec, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun X _ => ?_)
  rw [vec_flipU, vec_flipV, vec_transpose]
  ring

/-- **Fu-Gao-Park Lemma 2.3, matrix form.**  For symmetric `N`,
`⟨N, Π N⟩ = ½ (‖N‖₂² − ⟨N, N^{T_U}⟩)`, so the projection bound
`⟨N, Π N⟩ ≤ ½‖N‖₂²` is exactly the assertion `⟨N, N^{T_U}⟩ ≥ 0`. -/
theorem qform_Qm_vec_of_transpose_eq {N : Matrix (U × V) (U × V) ℂ} (hN : Nᵀ = N) :
    qform Qm (vec N) = (2 : ℂ)⁻¹ * ((hsNormSq N : ℂ) - hsInner N (flipU N)) := by
  rw [qform_Qm_vec, flipV_eq_flipU hN, hN, hsInner_self]
  ring

/-- `‖Π z‖² = ⟨z, Π z⟩` for the orthogonal projection `Qm`; the real part is
taken because `qform` lands in `ℂ`. -/
theorem norm_mulVecE_Qm_sq (z : EuclideanSpace ℂ (Idx U V)) :
    ‖mulVecE Qm z‖ ^ 2 = (qform Qm z).re := by
  have key := inner_mulVecE_left (Qm (U := U) (V := V)) z (mulVecE Qm z)
  rw [mulVecE_mul, Qm_mul_self, Qm_conjTranspose] at key
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), qform_eq_inner, ← key]
  rfl

end Expansion

end RankR
