/-
Symmetric rank-one matrices, and the Hilbert-Schmidt estimates the double-skew
argument needs.

A Takagi decomposition expresses a symmetric matrix as a combination of the
matrices `w wᵀ`, which are symmetric rather than positive: `w wᵀ = |w⟩⟨w̄|`.
Their pairings are collected here, together with the flip trace identity
(Fu-Gao-Park Lemma 2.2) and the two Cauchy-Schwarz consequences that make their
Lemma 2.3 elementary.  Nothing in this file mentions Takagi or the double-skew
subspace.
-/
import RankR.Core.DoubleSkew.Flip
import RankR.Core.PartialTrace.OneSided

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## Symmetric rank-one matrices -/

section Entrywise

variable {W : Type*}

/-- The entrywise conjugate of a vector. -/
def bar (w : EuclideanSpace ℂ W) : EuclideanSpace ℂ W :=
  WithLp.toLp 2 (fun p => conj (w p))

@[simp] theorem bar_apply (w : EuclideanSpace ℂ W) (p : W) : bar w p = conj (w p) := rfl

/-- `w wᵀ`, the symmetric rank-one matrix built from a vector.  This is
`|w⟩⟨w̄|`, not `|w⟩⟨w|`: it is symmetric, not positive semidefinite. -/
def symOuter (w : EuclideanSpace ℂ W) : Matrix W W ℂ := Matrix.of fun p q => w p * w q

@[simp] theorem symOuter_apply (w : EuclideanSpace ℂ W) (p q : W) :
    symOuter w p q = w p * w q := rfl

theorem transpose_symOuter (w : EuclideanSpace ℂ W) : (symOuter w)ᵀ = symOuter w := by
  ext p q; simp [mul_comm]

end Entrywise

section SymOuter

variable {W : Type*} [Fintype W]

/-- `⟨u uᵀ, v vᵀ⟩ = ⟪u,v⟫²`.  The double sum factorizes into two copies of the
same inner product.  In particular an orthonormal family of vectors gives an
orthonormal family of symmetric rank-ones. -/
theorem hsInner_symOuter (u v : EuclideanSpace ℂ W) :
    hsInner (symOuter u) (symOuter v) = (inner ℂ u v : ℂ) ^ 2 := by
  have h : (inner ℂ u v : ℂ) = ∑ r, conj (u r) * v r := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun r _ => RCLike.inner_apply' (u r) (v r)
  rw [h, sq, Finset.sum_mul_sum]
  simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, symOuter_apply, map_mul]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- `(u uᵀ)ᴴ (v vᵀ) = ⟪u,v⟫ · |ū⟩⟨v̄|`.  Used to compute `KᴴK` from a Takagi
decomposition, where orthonormality collapses the double sum to the diagonal. -/
theorem conjTranspose_symOuter_mul (u v : EuclideanSpace ℂ W) :
    (symOuter u)ᴴ * symOuter v = (inner ℂ u v : ℂ) • rankOne (bar u) (bar v) := by
  have h : (inner ℂ u v : ℂ) = ∑ r, conj (u r) * v r := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun r _ => RCLike.inner_apply' (u r) (v r)
  ext p q
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, h, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, symOuter_apply, rankOne,
    Matrix.of_apply, bar_apply, map_mul, Complex.conj_conj]
  ring

/-- `‖Kx‖² = ⟪x, KᴴK x⟫`, the bridge from the action of `K` to a quadratic form
in `KᴴK`.  Compare `norm_mulVecE_Qm_sq` in `Flip.lean`, which is the case of a
self-adjoint idempotent. -/
theorem norm_mulVecE_sq (K : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    ‖mulVecE K x‖ ^ 2 = (qform (Kᴴ * K) x).re := by
  have key := inner_mulVecE_left Kᴴ x (mulVecE K x)
  rw [mulVecE_mul, Matrix.conjTranspose_conjTranspose] at key
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), qform_eq_inner, ← key]
  rfl

end SymOuter

/-! ## Two Hilbert-Schmidt estimates

Fu-Gao-Park bound their cross term by Hölder's inequality for Schatten norms,
`|Tr(PQRS)| ≤ ‖P‖₄‖Q‖₄‖R‖₄‖S‖₄`.  Only the two special cases below are needed,
and both are Cauchy-Schwarz for the Hilbert-Schmidt inner product, so no
Schatten-`p` theory is required.  Note `‖V‖₄² = ‖VᴴV‖₂`, which is how the
statements line up with theirs. -/

section Estimates

/-- `|Tr (X²)| ≤ ‖X‖₂²`, by Cauchy-Schwarz applied to `⟨Xᴴ, X⟩ = Tr(X²)`
together with `‖Xᴴ‖₂ = ‖X‖₂`. -/
theorem norm_trace_mul_self_le {m : Type*} [Fintype m] (X : Matrix m m ℂ) :
    ‖(X * X).trace‖ ≤ hsNormSq X := by
  have h1 : hsInner Xᴴ X = (X * X).trace := by
    rw [hsInner, Matrix.conjTranspose_conjTranspose]
  have h3 : ‖vec Xᴴ‖ = ‖vec X‖ := by
    have h := hsNormSq_conjTranspose X
    rw [hsNormSq_eq_norm_sq, hsNormSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (vec Xᴴ), norm_nonneg (vec X)]
  calc ‖(X * X).trace‖ = ‖(inner ℂ (vec Xᴴ) (vec X) : ℂ)‖ := by rw [← h1, hsInner_eq_inner]
    _ ≤ ‖vec Xᴴ‖ * ‖vec X‖ := norm_inner_le_norm _ _
    _ = ‖vec X‖ ^ 2 := by rw [h3]; ring
    _ = hsNormSq X := (hsNormSq_eq_norm_sq X).symm

/-- `‖AᴴB‖₂² ≤ ‖AᴴA‖₂ ‖BᴴB‖₂`.

Expand `‖AᴴB‖₂² = Tr(BᴴA AᴴB) = Tr(AAᴴ · BBᴴ) = ⟨AAᴴ, BBᴴ⟩`, apply
Cauchy-Schwarz, and finish with `‖AAᴴ‖₂ = ‖AᴴA‖₂`, which is cyclicity of the
trace applied to `Tr(AAᴴAAᴴ) = Tr(AᴴAAᴴA)`. -/
theorem hsNormSq_conjTranspose_mul_le {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (A : Matrix m n ℂ) (B : Matrix m k ℂ) :
    hsNormSq (Aᴴ * B) ≤ Real.sqrt (hsNormSq (Aᴴ * A)) * Real.sqrt (hsNormSq (Bᴴ * B)) := by
  have hi : ((hsNormSq (Aᴴ * B) : ℝ) : ℂ) = hsInner (A * Aᴴ) (B * Bᴴ) := by
    rw [← hsInner_self]
    simp only [hsInner, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Bᴴ]
    simp only [Matrix.mul_assoc]
  have hAA : hsNormSq (A * Aᴴ) = hsNormSq (Aᴴ * A) := by
    have h : ((hsNormSq (A * Aᴴ) : ℝ) : ℂ) = ((hsNormSq (Aᴴ * A) : ℝ) : ℂ) := by
      rw [← hsInner_self, ← hsInner_self]
      simp only [hsInner, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm A]
      simp only [Matrix.mul_assoc]
    exact_mod_cast h
  have hBB : hsNormSq (B * Bᴴ) = hsNormSq (Bᴴ * B) := by
    have h : ((hsNormSq (B * Bᴴ) : ℝ) : ℂ) = ((hsNormSq (Bᴴ * B) : ℝ) : ℂ) := by
      rw [← hsInner_self, ← hsInner_self]
      simp only [hsInner, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm B]
      simp only [Matrix.mul_assoc]
    exact_mod_cast h
  have h1 : ‖((hsNormSq (Aᴴ * B) : ℝ) : ℂ)‖ = hsNormSq (Aᴴ * B) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hsNormSq_nonneg _)]
  have h2 : Real.sqrt (hsNormSq (A * Aᴴ)) = ‖vec (A * Aᴴ)‖ := by
    rw [hsNormSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have h3 : Real.sqrt (hsNormSq (B * Bᴴ)) = ‖vec (B * Bᴴ)‖ := by
    rw [hsNormSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [← hAA, ← hBB, h2, h3, ← h1, hi, hsInner_eq_inner]
  exact norm_inner_le_norm _ _

end Estimates

/-! ## The flip trace identity -/

section FlipTrace

variable {U V : Type*} [Fintype U] [Fintype V]

/-- **The flip trace identity**, Fu-Gao-Park Lemma 2.2 in matrix form.

Writing `Mᵤ`, `Mᵥ` for the `U × V` coefficient matrices of `u`, `v`, pairing a
symmetric rank-one against the `U`-partial-transpose of another gives
`Tr((MᵤᴴMᵥ)²)`: in

  `∑ conj(u(a,b)) · conj(u(a',b')) · v(a',b) · v(a,b')`

the sum over `a` and the sum over `a'` each collapse to an entry of `MᵤᴴMᵥ`,
leaving `∑_{b,b'} (MᵤᴴMᵥ)(b,b') · (MᵤᴴMᵥ)(b',b)`. -/
theorem hsInner_symOuter_flipU (u v : EuclideanSpace ℂ (U × V)) :
    hsInner (symOuter u) (flipU (symOuter v))
      = (((matOf u)ᴴ * matOf v) * ((matOf u)ᴴ * matOf v)).trace := by
  have reorder : ∀ G : U → V → U → V → ℂ,
      ∑ a, ∑ b, ∑ a', ∑ b', G a b a' b' = ∑ b, ∑ b', ∑ a, ∑ a', G a b a' b' := fun G =>
    calc ∑ a, ∑ b, ∑ a', ∑ b', G a b a' b'
        = ∑ b, ∑ a, ∑ a', ∑ b', G a b a' b' := Finset.sum_comm
      _ = ∑ b, ∑ a, ∑ b', ∑ a', G a b a' b' :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ b, ∑ b', ∑ a, ∑ a', G a b a' b' :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hL : hsInner (symOuter u) (flipU (symOuter v))
      = ∑ a, ∑ b, ∑ a', ∑ b',
          conj (u (a, b)) * conj (u (a', b')) * (v (a, b') * v (a', b)) := by
    simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def, symOuter_apply, flipU_apply,
      Fintype.sum_prod_type, map_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hR : (((matOf u)ᴴ * matOf v) * ((matOf u)ᴴ * matOf v)).trace
      = ∑ b, ∑ b', ∑ a, ∑ a',
          conj (u (a, b)) * conj (u (a', b')) * (v (a, b') * v (a', b)) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    simp only [Matrix.conjTranspose_apply, RCLike.star_def, matOf_apply]
    ring
  rw [hL, reorder, hR]

end FlipTrace

end RankR
