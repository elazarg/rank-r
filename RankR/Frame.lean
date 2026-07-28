/-
The frame lemmas relating the negative sector `Pneg` to the synthesized vector.

Two ingredients are collected here.  First the evaluation of the quadratic form
of `Pneg` at an arbitrary test vector as the sum, over the edges `i < j`, of the
squared moduli `|⟪ζ_{ij}, z⟫|²`.  Second the orthogonality `eq:T-orthogonal`: for
a *symmetric* operator `N`, the vector `(N ⊗ I_Q) ζ_{ij}` is orthogonal to `δ`.
Since every element of `so(U) ⊗ so(V)` is symmetric, the orthogonality applies in
particular to the elementary tensors `L ⊗ M` of skew matrices.

The mechanism behind the orthogonality is that `(N ⊗ I_Q) ζ_{ij}` places
`N ēᵢ` at `Q`-coordinate `j` and `-N ēⱼ` at `Q`-coordinate `i`, so pairing with
`δ` produces the difference of the two bilinear expressions
`∑_{p,q} conj(e_j p) N p q conj(e_i q)` and `∑_{p,q} conj(e_i p) N p q conj(e_j q)`,
which coincide once the summation indices are exchanged.  No orthonormality of
the family `e` is used, and the whole hypothesis is that those two expressions
coincide — that is, that the compression `E^*NĒ` of `N` to the frame is a
symmetric matrix, `IsFrameSymmetric e N` below.  Transpose symmetry `Nᵀ = N` is
the frame-independent strengthening of that condition and is what the double-skew
family supplies; the tensor structure enters only in the specialization at the
end.
-/
import RankR.Synth

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

section Frame

variable {W : Type*} [Fintype W] {s : ℕ}

/-! ## The quadratic form of the negative sector -/

/-- The quadratic form of `Pneg` at `z` is the total edge weight
`∑_{i < j} |⟪ζ_{ij}, z⟫|²`. -/
theorem qform_Pneg_eq (e : Fin s → EuclideanSpace ℂ W) (z : EuclideanSpace ℂ (W × Fin s)) :
    qform (Pneg e) z
      = ∑ p ∈ Edges, ((Complex.normSq (inner ℂ (zetaV e p.1 p.2) z) : ℝ) : ℂ) := by
  rw [Pneg, qform_sum_finset, Edges_def]
  exact Finset.sum_congr rfl fun p _ => qform_rankOne _ _

/-! ## Orthogonality to `δ` -/

/-- Pairing `δ` with a vector placed at the single `Q`-coordinate `k` collapses
the `Q`-sum and leaves the pairing of `e k` with the placed vector. -/
theorem inner_delta_epsOf (e : Fin s → EuclideanSpace ℂ W) (v : EuclideanSpace ℂ W)
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

/-- The bilinear expansion of `⟪e_a, N ē_b⟫` in the entries of `N`. -/
theorem inner_mulVecE_ebar (e : Fin s → EuclideanSpace ℂ W) (N : Matrix W W ℂ) (a b : Fin s) :
    inner ℂ (e a) (mulVecE N (ebar e b)) = ∑ p, ∑ q, conj (e a p) * N p q * conj (e b q) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [RCLike.inner_apply', mulVecE_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [ebar_apply, mul_assoc]

/-- `N` is **symmetric on the frame `e`**: the compression `E^*NĒ` of `N` by the
synthesis map `E : q_i ↦ e_i` is a symmetric matrix.  No orthonormality of `e` is
required, so `E` need not be an isometry.

This, and not `Nᵀ = N`, is what `eq:T-orthogonal` and its higher-arity form
actually consume.  The two conditions are not equivalent for a fixed frame:
`Nᵀ = N` is the frame-independent strengthening, recovered by quantifying over
every frame (`transpose_eq_of_forall_isFrameSymmetric`).  The weaker one suffices
because the frame is fixed — it comes from the range factorization of `C` —
before any Kraus operator is chosen.

In the Koszul language of the exterior development, the composite
`ε_E^* (N ⊗ I) ∂_E` is contraction by the alternating part of `E^*NĒ`, and this
predicate is the vanishing of that alternating part; the direction used
downstream is that it forces the composite to vanish. -/
def IsFrameSymmetric (e : Fin s → EuclideanSpace ℂ W) (N : Matrix W W ℂ) : Prop :=
  ∀ a b, inner ℂ (e a) (mulVecE N (ebar e b)) = inner ℂ (e b) (mulVecE N (ebar e a))

/-- A transpose-symmetric operator is symmetric on every frame: a compression of
a symmetric matrix is symmetric. -/
theorem isFrameSymmetric_of_transpose_eq {N : Matrix W W ℂ} (hN : Nᵀ = N)
    (e : Fin s → EuclideanSpace ℂ W) : IsFrameSymmetric e N := fun a b => by
  rw [inner_mulVecE_ebar, inner_mulVecE_ebar, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hsym : N y x = N x y := by
    have hxy := congrFun (congrFun hN x) y
    rwa [Matrix.transpose_apply] at hxy
  rw [hsym]; ring

/-- **Frame symmetry over all frames is transpose symmetry.**  Reading the
predicate off at the two-element frame `(δ_p, δ_q)` of standard basis vectors
gives `N p q = N q p`, so quantifying over frames recovers `Nᵀ = N`.

Together with `isFrameSymmetric_of_transpose_eq` this pins down the relation
between the two hypotheses: frame symmetry is the frame-local shadow of transpose
symmetry, and all that separates them is the choice of a single frame.  Two
vectors already suffice. -/
theorem transpose_eq_of_forall_isFrameSymmetric [DecidableEq W] {N : Matrix W W ℂ}
    (h : ∀ e : Fin 2 → EuclideanSpace ℂ W, IsFrameSymmetric e N) : Nᵀ = N := by
  ext p q
  have h2 := h ![EuclideanSpace.single p 1, EuclideanSpace.single q 1] 0 1
  rw [inner_mulVecE_ebar, inner_mulVecE_ebar] at h2
  simpa [PiLp.single_apply, Matrix.transpose_apply, eq_comm] using h2.symm

/-- `eq:T-orthogonal`: for an operator symmetric on the frame, the vector
`(N ⊗ I_Q) ζ_{ij}` is orthogonal to `δ`.

The two placed blocks contribute the bilinear forms of `N` on the pairs
`(ē_j, ē_i)` and `(ē_i, ē_j)`, which agree precisely by that symmetry. -/
theorem inner_delta_placeT_zetaV (e : Fin s → EuclideanSpace ℂ W) {N : Matrix W W ℂ}
    (hN : IsFrameSymmetric e N) (i j : Fin s) :
    inner ℂ (delta e) (mulVecE (placeT N) (zetaV e i j)) = 0 := by
  rw [mulVecE_placeT_zetaV e (fun _ _ => N) i j, inner_sub_right, inner_delta_epsOf,
    inner_delta_epsOf, sub_eq_zero]
  exact hN _ _

end Frame

/-! ## The double-skew specialization -/

section DoubleSkew

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

omit [DecidableEq U] [DecidableEq V] in
/-- The double-skew specialization of `eq:T-orthogonal`: an elementary tensor of
skew matrices is symmetric, hence its `Q`-placement sends every `ζ_{ij}` into the
orthogonal complement of `δ`. -/
theorem inner_delta_placeT_kron_zetaV (e : Fin s → EuclideanSpace ℂ (U × V))
    {L : Matrix U U ℂ} {M : Matrix V V ℂ} (hL : IsSkew L) (hM : IsSkew M) (i j : Fin s) :
    inner ℂ (delta e) (mulVecE (placeT (L ⊗ₖ M)) (zetaV e i j)) = 0 :=
  inner_delta_placeT_zetaV e
    (isFrameSymmetric_of_transpose_eq
      (transpose_eq_self_of_mem_doubleSkew (kron_mem_doubleSkew hL hM)) e) i j

end DoubleSkew

end RankR
