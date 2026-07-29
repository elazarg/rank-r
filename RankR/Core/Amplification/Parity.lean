/-
The parity dichotomy behind `eq:T-orthogonal`, in both directions.

`Frame.lean` proves that frame symmetry of `N` makes `(N ⊗ I_Q) ζ_{ij}`
orthogonal to `δ_e`, and `Lifting.lean` uses that to sharpen form (A₀) to form
(A) by the single direction `δ_e`.  Here is the converse dichotomy: for an odd
number of skew factors the Kraus operators are antisymmetric instead, the
orthogonality fails, and the `1/s` correction is lost.  Parity is what protects
the dark state.

Two statements, of different strengths.

* `inner_delta_placeT_zetaV_iff` upgrades `eq:T-orthogonal` to an equivalence:
  the pairing `⟪δ_e, (N ⊗ I_Q) ζ_{ij}⟫` is the *difference* of the two bilinear
  forms, so it vanishes for every edge exactly when `IsFrameSymmetric e N`.  This
  is to `inner_delta_placeT_zetaV` what
  `transpose_eq_of_forall_isFrameSymmetric` is to
  `isFrameSymmetric_of_transpose_eq`, and it is where the `ℤ/2`-degree enters:
  `inner_delta_placeT_zetaV_of_isSkew` evaluates the same pairing on a *skew*
  operator, where the two forms are negatives and the difference becomes twice a
  single one.

* The rest of the file refutes form (A) outright.  A skew family cannot merely
  fail to satisfy the hypothesis of `qform_krausQ_Pneg_le`; the conclusion itself
  is false.  The certificate is exact and finite: one Kraus operator
  `J = E_{01} - E_{10}` on `W = ℂ²`, the standard frame of `s = 2` vectors, and
  the test vector `y = δ_e`.  For that data `‖y‖² = 2` and `|⟪δ_e, y⟫|²/s = 2`,
  so the protected right-hand side of form (A) is exactly `0`, while the left-hand
  side is `4`.

The failure is sharp in a second way worth recording.  Form (A₀), which does not
use the hypothesis, holds on the same data *with equality*: `2β(s-1)‖y‖² = 4`
too.  So the skew family saturates the unprotected bound and refutes the
protected one, which is exactly the assertion that the whole gap between the two
forms is the direction `δ_e` and that transposition parity decides it.
-/
import RankR.Core.Amplification.OperatorForms

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## `eq:T-orthogonal` is an equivalence -/

section Converse

variable {W : Type*} [Fintype W] {s : ℕ}

/-- The pairing of `δ_e` against a placed edge vector, evaluated.  It is the
*difference* of the two bilinear forms of `N` on the pair `(e_i, e_j)`; both
directions of the dichotomy read off this one identity. -/
theorem inner_delta_placeT_zetaV_eq (e : Fin s → EuclideanSpace ℂ W) (N : Matrix W W ℂ)
    (i j : Fin s) :
    inner ℂ (delta e) (mulVecE (placeT N) (zetaV e i j))
      = inner ℂ (e j) (mulVecE N (ebar e i)) - inner ℂ (e i) (mulVecE N (ebar e j)) := by
  rw [mulVecE_placeT_zetaV e (fun _ _ => N) i j, inner_sub_right, inner_delta_epsOf,
    inner_delta_epsOf]

/-- **`eq:T-orthogonal` is an equivalence.**  Orthogonality of every placed edge
vector to `δ_e` is not merely implied by frame symmetry: it *is* frame symmetry.

`Frame.lean` supplies the direction used downstream; this is the converse, and it
is what makes `IsFrameSymmetric` the exact hypothesis rather than a convenient
sufficient one. -/
theorem inner_delta_placeT_zetaV_iff (e : Fin s → EuclideanSpace ℂ W) (N : Matrix W W ℂ) :
    (∀ i j, inner ℂ (delta e) (mulVecE (placeT N) (zetaV e i j)) = 0)
      ↔ IsFrameSymmetric e N := by
  constructor
  · intro h a b
    have hab := h b a
    rw [inner_delta_placeT_zetaV_eq, sub_eq_zero] at hab
    exact hab
  · intro h i j
    rw [inner_delta_placeT_zetaV_eq, sub_eq_zero]
    exact h j i

/-- **The skew case: the pairing is the sum, not the difference.**

For `Nᵀ = -N` the two bilinear forms of `inner_delta_placeT_zetaV_eq` are
negatives of one another, so the difference doubles instead of cancelling.  This
is the `ℤ/2`-degree dichotomy of `rem:parity` made explicit: degree `0` protects
`δ_e`, degree `1` pairs against it twice over. -/
theorem inner_delta_placeT_zetaV_of_isSkew (e : Fin s → EuclideanSpace ℂ W)
    {N : Matrix W W ℂ} (hN : Nᵀ = -N) (i j : Fin s) :
    inner ℂ (delta e) (mulVecE (placeT N) (zetaV e i j))
      = -2 * inner ℂ (e i) (mulVecE N (ebar e j)) := by
  have hskew : ∀ a b : Fin s, inner ℂ (e a) (mulVecE N (ebar e b))
      = -inner ℂ (e b) (mulVecE N (ebar e a)) := by
    intro a b
    rw [inner_mulVecE_ebar, inner_mulVecE_ebar, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hsym : N y x = -N x y := by
      have hxy := congrFun (congrFun hN x) y
      rwa [Matrix.transpose_apply, Matrix.neg_apply] at hxy
    rw [hsym]; ring
  rw [inner_delta_placeT_zetaV_eq, hskew j i]
  ring

end Converse

/-! ## A rank-two bound from the Kraus norms

Cauchy-Schwarz against each Kraus operator separately.  Crude in general --- it
ignores every cancellation between family members --- but exact enough for a
one-element family, which is all the certificate below needs. -/

section CrudeBound

variable {W : Type*} [Fintype W] {ι : Type*} [Fintype ι]

/-- `∑_f ‖A_f‖₂² ≤ 2β` suffices for `ChoiTwoBound (choiOf A) β`. -/
theorem choiTwoBound_of_sum_hsNormSq (A : ι → Matrix W W ℂ) {β : ℝ}
    (h : ∑ f, hsNormSq (A f) ≤ 2 * β) : ChoiTwoBound (choiOf A) β := by
  intro u₁ v₁ u₂ v₂
  set M := rankOne u₁ v₁ + rankOne u₂ v₂ with hM
  have hstep : ∀ f : ι, Complex.normSq (inner ℂ (vec (A f)) (vec M))
      ≤ hsNormSq (A f) * hsNormSq M := by
    intro f
    have hcs := norm_inner_le_norm (𝕜 := ℂ) (vec (A f)) (vec M)
    have hsq : ‖inner ℂ (vec (A f)) (vec M)‖ ^ 2 ≤ (‖vec (A f)‖ * ‖vec M‖) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖vec (A f)‖ * ‖vec M‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      nlinarith [norm_nonneg (inner ℂ (vec (A f)) (vec M) : ℂ)]
    rw [hsNormSq_eq_norm_sq, hsNormSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [hsq]
  have hsum : ∑ f, Complex.normSq (inner ℂ (vec (A f)) (vec M))
      ≤ (∑ f, hsNormSq (A f)) * hsNormSq M := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun f _ => hstep f
  have hMn : (0 : ℝ) ≤ hsNormSq M := hsNormSq_nonneg _
  rw [re_qform_choiOf]
  nlinarith

end CrudeBound

end RankR
