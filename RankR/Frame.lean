/-
The frame lemmas relating the negative sector `Pneg` to the synthesized vector.

Three ingredients are collected here.  First the adjoint move
`⟪z, A x⟫ = ⟪Aᴴ z, x⟫`, which is what lets a Kraus pullback be moved from one
side of an inner product to the other.  Second the evaluation of the quadratic
form of `Pneg` at an arbitrary test vector as the sum, over the edges `i < j`,
of the squared moduli `|⟪ζ_{ij}, z⟫|²`.  Third the orthogonality
`eq:T-orthogonal`: for a *symmetric* operator `N` on `U ⊗ V`, the vector
`(N ⊗ I_Q) ζ_{ij}` is orthogonal to `δ`.  Since every element of
`so(U) ⊗ so(V)` is symmetric, the orthogonality applies in particular to the
elementary tensors `L ⊗ M` of skew matrices.

The mechanism behind the orthogonality is that `(N ⊗ I_Q) ζ_{ij}` places
`N ēᵢ` at `Q`-coordinate `j` and `-N ēⱼ` at `Q`-coordinate `i`, so pairing with
`δ` produces the difference of the two bilinear expressions
`∑_{p,q} conj(e_j p) N p q conj(e_i q)` and `∑_{p,q} conj(e_i p) N p q conj(e_j q)`,
which coincide once the summation indices are exchanged.  No orthonormality of
the family `e` is used.
-/
import RankR.Synth

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

/-! ## The adjoint move -/

section Adjoint

variable {W : Type*} [Fintype W]

/-- `⟪z, A x⟫ = ⟪Aᴴ z, x⟫`: both sides equal the double sum
`∑_p ∑_q conj(z p) A_{pq} x_q`. -/
theorem inner_mulVecE_left (A : Matrix W W ℂ) (z x : EuclideanSpace ℂ W) :
    inner ℂ z (mulVecE A x) = inner ℂ (mulVecE Aᴴ z) x := by
  have hL : (inner ℂ z (mulVecE A x) : ℂ) = ∑ p, ∑ q, conj (z p) * A p q * x q := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [RCLike.inner_apply', mulVecE_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => (mul_assoc _ _ _).symm
  have hR : (inner ℂ (mulVecE Aᴴ z) x : ℂ) = ∑ q, ∑ p, conj (z p) * A p q * x q := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [RCLike.inner_apply', mulVecE_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]
    ring
  rw [hL, hR, Finset.sum_comm]

end Adjoint

section Frame

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

/-! ## The quadratic form of the negative sector -/

omit [DecidableEq U] [DecidableEq V] in
/-- The quadratic form of `Pneg` at `z` is the total edge weight
`∑_{i < j} |⟪ζ_{ij}, z⟫|²`. -/
theorem qform_Pneg_eq (e : Fin s → EuclideanSpace ℂ (U × V))
    (z : EuclideanSpace ℂ ((U × V) × Fin s)) :
    qform (Pneg e) z
      = ∑ p ∈ Edges, ((Complex.normSq (inner ℂ (zetaV e p.1 p.2) z) : ℝ) : ℂ) := by
  rw [Pneg, qform_sum_finset, Edges_def]
  exact Finset.sum_congr rfl fun p _ => qform_rankOne _ _

/-! ## Orthogonality to `δ` -/

omit [DecidableEq U] [DecidableEq V] in
/-- Pairing `δ` with a vector placed at the single `Q`-coordinate `k` collapses
the `Q`-sum and leaves the pairing of `e k` with the placed vector. -/
theorem inner_delta_epsOf (e : Fin s → EuclideanSpace ℂ (U × V)) (v : EuclideanSpace ℂ (U × V))
    (k : Fin s) : inner ℂ (delta e) (epsOf v k) = inner ℂ (e k) v := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ m : Fin s, (inner ℂ (delta e (p, m)) (epsOf v k (p, m)) : ℂ)
      = if m = k then conj (e k p) * v p else 0 := by
    intro m
    rw [RCLike.inner_apply', delta_apply, epsOf_apply]
    by_cases hm : m = k
    · subst hm; simp
    · simp [hm]
  rw [Finset.sum_congr rfl fun m _ => h m, Finset.sum_ite_eq', if_pos (Finset.mem_univ k),
    RCLike.inner_apply']

omit [DecidableEq U] [DecidableEq V] in
/-- The bilinear expansion of `⟪e_a, N ē_b⟫` in the entries of `N`. -/
theorem inner_mulVecE_ebar (e : Fin s → EuclideanSpace ℂ (U × V))
    (N : Matrix (U × V) (U × V) ℂ) (a b : Fin s) :
    inner ℂ (e a) (mulVecE N (ebar e b)) = ∑ p, ∑ q, conj (e a p) * N p q * conj (e b q) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [RCLike.inner_apply', mulVecE_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [ebar_apply, mul_assoc]

omit [DecidableEq U] [DecidableEq V] in
/-- `eq:T-orthogonal`: for a symmetric operator `N` on `U ⊗ V`, the vector
`(N ⊗ I_Q) ζ_{ij}` is orthogonal to `δ`.

The two placed blocks contribute the bilinear forms of `N` on the pairs
`(ē_j, ē_i)` and `(ē_i, ē_j)`, which agree by symmetry of `N`. -/
theorem inner_delta_placeQ_zetaV (e : Fin s → EuclideanSpace ℂ (U × V))
    {N : Matrix (U × V) (U × V) ℂ} (hN : Nᵀ = N) (i j : Fin s) :
    inner ℂ (delta e) (mulVecE (placeQ N) (zetaV e i j)) = 0 := by
  rw [mulVecE_placeQ_zetaV e (fun _ _ => N) i j, inner_sub_right, inner_delta_epsOf,
    inner_delta_epsOf, sub_eq_zero, inner_mulVecE_ebar, inner_mulVecE_ebar, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hsym : N y x = N x y := by
    have hxy := congrFun (congrFun hN x) y
    rwa [Matrix.transpose_apply] at hxy
  rw [hsym]; ring

/-- The double-skew specialization of `eq:T-orthogonal`: an elementary tensor of
skew matrices is symmetric, hence its `Q`-placement sends every `ζ_{ij}` into the
orthogonal complement of `δ`. -/
theorem inner_delta_placeQ_kron_zetaV (e : Fin s → EuclideanSpace ℂ (U × V))
    {L : Matrix U U ℂ} {M : Matrix V V ℂ} (hL : IsSkew L) (hM : IsSkew M) (i j : Fin s) :
    inner ℂ (delta e) (mulVecE (placeQ (L ⊗ₖ M)) (zetaV e i j)) = 0 :=
  inner_delta_placeQ_zetaV e
    (transpose_eq_self_of_mem_doubleSkew (kron_mem_doubleSkew hL hM)) i j

end Frame

end RankR
