/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The Autonne-Takagi factorization

Every complex **symmetric** matrix `K` (that is, `Kᵀ = K`, *not* `Kᴴ = K`) can be written as
`K = U * diagonal d * Uᵀ` with `U` unitary and `d` a nonnegative real vector.  This is the
Autonne-Takagi factorization; see Horn-Johnson, *Matrix Analysis*, 2nd ed., Corollary 4.4.4 and
Theorem 4.4.16.

Note the plain transpose `Uᵀ` in the conclusion: this is what distinguishes the statement from the
spectral theorem, and the `d i` are the singular values of `K`, not its eigenvalues.

## Main results

* `LinearMap.IsConjSymmetric`: the coordinate-free notion behind the theorem.  A conjugate-linear
  self-map `σ` of a complex inner product space is *conjugate-symmetric* when the ℂ-bilinear form
  `(u, v) ↦ ⟪σ u, v⟫` is symmetric.
* `LinearMap.IsConjSymmetric.exists_orthonormalBasis`: such a `σ` is diagonalized, with nonnegative
  real eigenvalues, by some orthonormal basis.  This is the coordinate-free Autonne-Takagi theorem.
* `Matrix.exists_takagi`: the matrix form stated above.

## Upstreaming

For a Mathlib contribution this file would additionally be split along its two namespaces and
converted to the module system (`module` / `public import` / `public section`); both are
mechanical.  The mathematical content and the namespacing are as they would be upstream.

## Implementation notes

The map attached to a symmetric matrix `K` is the conjugate-linear `σ v = conj (K *ᵥ v)`; its
defining symmetry `⟪σ u, v⟫ = ⟪σ v, u⟫` is exactly `uᵀ K v = vᵀ K u`.  The proof of
`RankR.IsConjSymmetric.exists_orthonormalBasis` is by induction on the dimension: one produces a
single unit eigenvector with nonnegative eigenvalue, and then restricts `σ` to the orthogonal
complement of the line it spans, which is again `σ`-invariant.

The eigenvector is found by diagonalizing the ℂ-linear map `σ ∘ σ`, whose eigenvalues are
automatically real and nonnegative; if `σ ∘ σ v = μ v` and `s = √μ`, then `σ v + s • v` is fixed
up to the factor `s` by `σ`, and in the degenerate case `σ v = -s • v` the vector `I • v` works.
-/

open ComplexConjugate Matrix Module
open scoped InnerProductSpace

universe u

namespace LinearMap

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A conjugate-linear self-map `σ` of a complex inner product space is *conjugate-symmetric* if
the ℂ-bilinear form `(u, v) ↦ ⟪σ u, v⟫` it defines is symmetric.

This is the coordinate-free form of a matrix being symmetric (`Kᵀ = K`); compare
`LinearMap.IsSymmetric`, which is the coordinate-free form of `Kᴴ = K`. -/
def IsConjSymmetric (σ : E →ₗ⋆[ℂ] E) : Prop := ∀ u v : E, ⟪σ u, v⟫_ℂ = ⟪σ v, u⟫_ℂ

variable {σ : E →ₗ⋆[ℂ] E}

/-- An eigenvector of a conjugate-linear map for a *real* eigenvalue can be normalized: the
eigenvalue is unchanged, since conjugation fixes it. -/
theorem exists_norm_one_of_conj_smul_eq {z : E} {s : ℝ} (hz : z ≠ 0) (h : σ z = (s : ℂ) • z) :
    ∃ v : E, ‖v‖ = 1 ∧ σ v = (s : ℂ) • v := by
  refine ⟨((‖z‖⁻¹ : ℝ) : ℂ) • z, ?_, ?_⟩
  · rw [norm_smul]
    simp [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  · rw [map_smulₛₗ, h, Complex.conj_ofReal, smul_comm]

namespace IsConjSymmetric

/-- For a conjugate-symmetric `σ`, the ℂ-linear map `σ ∘ σ` satisfies
`⟪σ (σ u), v⟫ = ⟪σ v, σ u⟫`.  Taking `u = v` shows that `σ ∘ σ` is a positive operator. -/
theorem inner_comp_self (hσ : IsConjSymmetric σ) (u v : E) : ⟪σ (σ u), v⟫_ℂ = ⟪σ v, σ u⟫_ℂ :=
  hσ (σ u) v

/-- **Existence of a Takagi eigenvector.** A conjugate-symmetric conjugate-linear map on a
nonzero finite-dimensional complex inner product space has a unit vector `v` with
`σ v = t • v` for some real `t ≥ 0`. -/
theorem exists_eigenvector [FiniteDimensional ℂ E] [Nontrivial E] (hσ : IsConjSymmetric σ) :
    ∃ (v : E) (t : ℝ), ‖v‖ = 1 ∧ 0 ≤ t ∧ σ v = (t : ℂ) • v := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (σ.comp σ)
  obtain ⟨v, hmem, hv0⟩ := hμ.exists_hasEigenvector
  have hvv : σ (σ v) = μ • v := Module.End.mem_eigenspace_iff.mp hmem
  -- `μ` is the nonnegative real `‖σ v‖ ^ 2 / ‖v‖ ^ 2`.
  set r : ℝ := ‖σ v‖ ^ 2 / ‖v‖ ^ 2 with hr
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have hkey : (starRingEnd ℂ) μ * (‖v‖ : ℂ) ^ 2 = (‖σ v‖ : ℂ) ^ 2 := by
    have h1 : ⟪σ (σ v), v⟫_ℂ = ⟪σ v, σ v⟫_ℂ := hσ.inner_comp_self v v
    rwa [hvv, inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have hr0 : 0 ≤ r := by positivity
  have hμr : μ = (r : ℂ) := by
    have hne : (‖v‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hnv)
    have hcm : (starRingEnd ℂ) μ = (r : ℂ) := by
      rw [hr]
      push_cast
      rw [eq_div_iff hne]
      exact hkey
    have := congrArg (starRingEnd ℂ) hcm
    rwa [Complex.conj_conj, Complex.conj_ofReal] at this
  set s : ℝ := Real.sqrt r with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg r
  have hs2 : (s : ℂ) ^ 2 = μ := by
    rw [hμr, ← Complex.ofReal_pow, hs, Real.sq_sqrt hr0]
  -- The vector `w = σ v + s • v` is scaled by `s` under `σ`.
  set w : E := σ v + (s : ℂ) • v with hw
  have hwe : σ w = (s : ℂ) • w := by
    rw [hw, map_add, map_smulₛₗ, hvv, Complex.conj_ofReal, ← hs2]
    module
  rcases eq_or_ne w 0 with hw0 | hw0
  · -- Degenerate case `σ v = -s • v`: use `I • v` instead.
    have hσv : σ v = -((s : ℂ) • v) := by
      rw [hw] at hw0
      linear_combination (norm := module) hw0
    have hIe : σ (Complex.I • v) = (s : ℂ) • (Complex.I • v) := by
      rw [map_smulₛₗ, hσv]
      simp only [Complex.conj_I]
      module
    have hI0 : Complex.I • v ≠ 0 := by
      simpa [Complex.I_ne_zero] using hv0
    obtain ⟨u, hu1, hu2⟩ := exists_norm_one_of_conj_smul_eq hI0 hIe
    exact ⟨u, s, hu1, hs0, hu2⟩
  · obtain ⟨u, hu1, hu2⟩ := exists_norm_one_of_conj_smul_eq hw0 hwe
    exact ⟨u, s, hu1, hs0, hu2⟩

/-- The orthogonal complement of the line through a `σ`-eigenvector is `σ`-invariant. -/
theorem orthogonal_invariant (hσ : IsConjSymmetric σ) {v : E} {t : ℝ} (h : σ v = (t : ℂ) • v)
    {x : E} (hx : x ∈ (ℂ ∙ v)ᗮ) : σ x ∈ (ℂ ∙ v)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
  rw [← inner_conj_symm, hσ x v, h, inner_smul_left, hx, mul_zero, map_zero]

end IsConjSymmetric

/-- The restriction of a conjugate-linear map to an invariant submodule. -/
@[simps]
def restrictConj (σ : E →ₗ⋆[ℂ] E) {p : Submodule ℂ E} (hp : ∀ x ∈ p, σ x ∈ p) : p →ₗ⋆[ℂ] p where
  toFun x := ⟨σ x, hp x x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)

/-- Conjugate-symmetry is inherited by the restriction to an invariant submodule. -/
theorem IsConjSymmetric.restrict {σ : E →ₗ⋆[ℂ] E} (hσ : IsConjSymmetric σ) {p : Submodule ℂ E}
    (hp : ∀ x ∈ p, σ x ∈ p) : IsConjSymmetric (restrictConj σ hp) := by
  intro u v
  rw [Submodule.coe_inner, Submodule.coe_inner]
  exact hσ u v

end Abstract

section Induction

/-- Auxiliary induction on the dimension for `LinearMap.IsConjSymmetric.exists_orthonormalBasis`. -/
private theorem exists_orthonormalBasis_aux (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
      (σ : E →ₗ⋆[ℂ] E), IsConjSymmetric σ → Module.finrank ℂ E = n →
      ∃ (e : OrthonormalBasis (Fin n) ℂ E) (d : Fin n → ℝ),
        (∀ i, 0 ≤ d i) ∧ ∀ i, σ (e i) = (d i : ℂ) • e i := by
  induction n with
  | zero =>
    intro E _ _ _ σ _ hn
    have hsub : Subsingleton E := Module.finrank_zero_iff.mp hn
    have hsp : ⊤ ≤ Submodule.span ℂ (Set.range (fun _ : Fin 0 => (0 : E))) := by
      intro x _
      rw [Subsingleton.elim x 0]
      exact Submodule.zero_mem _
    exact ⟨OrthonormalBasis.mk (Orthonormal.of_isEmpty (𝕜 := ℂ) (fun _ : Fin 0 => (0 : E))) hsp,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro E _ _ _ σ hσ hn
    have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
    obtain ⟨v, t, hv1, ht0, hvt⟩ := hσ.exists_eigenvector
    have hv0 : v ≠ 0 := by
      intro h
      rw [h, norm_zero] at hv1
      exact zero_ne_one hv1
    have hinv : ∀ x ∈ (ℂ ∙ v)ᗮ, σ x ∈ (ℂ ∙ v)ᗮ := fun _ hx => hσ.orthogonal_invariant hvt hx
    have hrank : Module.finrank ℂ ((ℂ ∙ v)ᗮ : Submodule ℂ E) = n := by
      have h := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℂ) (ℂ ∙ v)
      rw [finrank_span_singleton hv0, hn] at h
      omega
    obtain ⟨e', d', hd'0, he'⟩ := ih (restrictConj σ hinv) (hσ.restrict hinv) hrank
    -- Assemble `v` and the basis of the orthogonal complement.
    set f : Fin (n + 1) → E := Fin.cases v (fun i => ((e' i : E))) with hf
    have hf0 : f 0 = v := by simp [hf]
    have hfs : ∀ i : Fin n, f i.succ = (e' i : E) := by intro i; simp [hf]
    have hvperp : ∀ i : Fin n, ⟪v, (e' i : E)⟫_ℂ = 0 := fun i =>
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (e' i).2
    have hon : Orthonormal ℂ f := by
      constructor
      · intro i
        induction i using Fin.cases with
        | zero => rw [hf0]; exact hv1
        | succ j => rw [hfs]; exact e'.orthonormal.1 j
      · intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ l => rw [hf0, hfs]; exact hvperp l
        | succ k =>
          induction j using Fin.cases with
          | zero =>
            rw [hf0, hfs, ← inner_conj_symm, hvperp k, map_zero]
          | succ l =>
            rw [hfs, hfs, ← Submodule.coe_inner]
            exact e'.orthonormal.2 (fun h => hij (by rw [h]))
    have hcard : Fintype.card (Fin (n + 1)) = Module.finrank ℂ E := by simp [hn]
    have hbasis : Orthonormal ℂ ⇑(basisOfOrthonormalOfCardEqFinrank hon hcard) := by
      rwa [coe_basisOfOrthonormalOfCardEqFinrank]
    refine ⟨(basisOfOrthonormalOfCardEqFinrank hon hcard).toOrthonormalBasis hbasis,
      Fin.cases t d', ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using ht0
      | succ j => simpa using hd'0 j
    · intro i
      have hcoe : ∀ i, ((basisOfOrthonormalOfCardEqFinrank hon hcard).toOrthonormalBasis
          hbasis) i = f i := by
        intro i
        rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
      rw [hcoe]
      induction i using Fin.cases with
      | zero => rw [hf0]; simpa using hvt
      | succ j =>
        rw [hfs]
        have := congrArg (Subtype.val) (he' j)
        simpa using this

end Induction

section Main

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Autonne-Takagi, coordinate-free form.**  A conjugate-symmetric conjugate-linear self-map of a
finite-dimensional complex inner product space is diagonalized by an orthonormal basis, with
nonnegative real eigenvalues.

Concretely, `σ (e i) = d i • e i` with `d i ≥ 0` real, even though `σ` is only conjugate-linear. -/
theorem IsConjSymmetric.exists_orthonormalBasis {σ : E →ₗ⋆[ℂ] E} (hσ : IsConjSymmetric σ)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = Module.finrank ℂ E) :
    ∃ (e : OrthonormalBasis ι ℂ E) (d : ι → ℝ),
      (∀ i, 0 ≤ d i) ∧ ∀ i, σ (e i) = (d i : ℂ) • e i := by
  obtain ⟨e, d, hd, he⟩ := exists_orthonormalBasis_aux (Module.finrank ℂ E) σ hσ rfl
  let g : Fin (Module.finrank ℂ E) ≃ ι := (Fintype.equivFinOfCardEq hι).symm
  refine ⟨e.reindex g, fun i => d (g.symm i), fun i => hd _, fun i => ?_⟩
  simpa using he (g.symm i)

end Main

end LinearMap

namespace Matrix

section Matrices

variable {W : Type*} [Fintype W]

/-- The conjugate-linear map `v ↦ conj (K *ᵥ v)` on `EuclideanSpace ℂ W` attached to a square
complex matrix `K`.  It is conjugate-symmetric when `K` is symmetric, and its Takagi
diagonalization is the Autonne-Takagi factorization of `K`. -/
noncomputable def conjMulVec (K : Matrix W W ℂ) :
    EuclideanSpace ℂ W →ₗ⋆[ℂ] EuclideanSpace ℂ W where
  toFun x := WithLp.toLp 2 fun i => conj ((K *ᵥ WithLp.ofLp x) i)
  map_add' x y := by ext i; simp [Matrix.mulVec_add]
  map_smul' c x := by ext i; simp [Matrix.mulVec_smul]

@[simp]
theorem conjMulVec_apply (K : Matrix W W ℂ) (x : EuclideanSpace ℂ W) (i : W) :
    conjMulVec K x i = conj ((K *ᵥ WithLp.ofLp x) i) := rfl

/-- For a symmetric matrix `K`, the map `v ↦ conj (K *ᵥ v)` is conjugate-symmetric: the identity
`⟪σ u, v⟫ = ⟪σ v, u⟫` is exactly `uᵀ K v = vᵀ K u`. -/
theorem isConjSymmetric_conjMulVec {K : Matrix W W ℂ} (hK : Kᵀ = K) :
    LinearMap.IsConjSymmetric (conjMulVec K) := by
  have hsym : ∀ a b : W, K b a = K a b := fun a b => congrFun (congrFun hK a) b
  have key : ∀ x y : EuclideanSpace ℂ W,
      ⟪conjMulVec K x, y⟫_ℂ = ∑ i, ∑ j, K i j * x j * y i := by
    intro x y
    simp only [PiLp.inner_apply, RCLike.inner_apply, conjMulVec_apply, Complex.conj_conj,
      Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  intro u v
  rw [key, key, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => by rw [hsym a b]; ring

variable [DecidableEq W]

/-- **Autonne-Takagi factorization.** Every complex symmetric matrix `K` factors
as `K = U * diagonal d * Uᵀ` with `U` unitary and `d` nonnegative real.

Note the plain transpose `Uᵀ`, not the conjugate transpose: this is what distinguishes the
statement from the spectral theorem.  See Horn-Johnson, *Matrix Analysis*, 2nd ed.,
Corollary 4.4.4. -/
theorem exists_takagi (K : Matrix W W ℂ) (hK : Kᵀ = K) :
    ∃ (U : Matrix W W ℂ) (d : W → ℝ),
      U ∈ Matrix.unitaryGroup W ℂ ∧ (∀ i, 0 ≤ d i) ∧
      K = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᵀ := by
  obtain ⟨e, d, hd0, he⟩ :=
    (isConjSymmetric_conjMulVec hK).exists_orthonormalBasis (ι := W) (by simp)
  -- The eigenvector relation, in coordinates: `K *ᵥ e j = d j • conj (e j)`.
  have hev : ∀ j i : W, (K *ᵥ WithLp.ofLp (e j)) i = (d j : ℂ) * conj (e j i) := by
    intro j i
    have h := congrArg (fun x : EuclideanSpace ℂ W => x i) (he j)
    simp only [conjMulVec_apply, PiLp.smul_apply, smul_eq_mul] at h
    have := congrArg (starRingEnd ℂ) h
    rwa [Complex.conj_conj, map_mul, Complex.conj_ofReal] at this
  set U : Matrix W W ℂ := Matrix.of fun i j => conj (e j i) with hU
  have hUmem : U ∈ Matrix.unitaryGroup W ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext j k
    have hjk : ⟪e k, e j⟫_ℂ = if k = j then 1 else 0 := orthonormal_iff_ite.mp e.orthonormal k j
    simp only [PiLp.inner_apply, RCLike.inner_apply] at hjk
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, hU, Matrix.of_apply,
      Complex.star_def, Complex.conj_conj]
    rw [hjk]
    simp [eq_comm]
  -- The rows of `U` are orthonormal too, which is completeness of the basis `e`.
  have hdelta : ∀ i k : W, ∑ j, conj (e j i) * e j k = if i = k then 1 else 0 := by
    intro i k
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hUmem) i) k
    simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, hU, Matrix.of_apply,
      Complex.star_def, Complex.conj_conj] using h
  refine ⟨U, d, hUmem, hd0, ?_⟩
  have hUd : U * Matrix.diagonal (fun i => (d i : ℂ))
      = Matrix.of fun i j => conj (e j i) * (d j : ℂ) := by
    ext i j
    rw [Matrix.mul_diagonal]
    simp [hU]
  ext i k
  have hlhs : (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᵀ) i k
      = ∑ j, conj (e j i) * (d j : ℂ) * conj (e j k) := by
    rw [hUd]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, hU]
  rw [hlhs]
  calc K i k
      = ∑ m, K i m * (if k = m then 1 else 0) := by simp
    _ = ∑ m, K i m * ∑ j, conj (e j k) * e j m := by simp_rw [hdelta k]
    _ = ∑ j, conj (e j k) * ∑ m, K i m * e j m := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by ring
    _ = ∑ j, conj (e j k) * (K *ᵥ WithLp.ofLp (e j)) i := by
        simp [Matrix.mulVec, dotProduct]
    _ = ∑ j, conj (e j i) * (d j : ℂ) * conj (e j k) := by
        simp_rw [hev]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- **Autonne-Takagi factorization**, with the unitary factor bundled as an element of
`Matrix.unitaryGroup W ℂ`. -/
theorem exists_takagi_unitaryGroup (K : Matrix W W ℂ) (hK : Kᵀ = K) :
    ∃ (U : Matrix.unitaryGroup W ℂ) (d : W → ℝ), (∀ i, 0 ≤ d i) ∧
      K = (U : Matrix W W ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix W W ℂ)ᵀ := by
  obtain ⟨U, d, hU, hd, hfac⟩ := exists_takagi K hK
  exact ⟨⟨U, hU⟩, d, hd, hfac⟩

/-- The converse of `Matrix.exists_takagi`: any matrix of the form `U * diagonal d * Uᵀ` is
symmetric, for any `U` and any diagonal.  Together with `Matrix.exists_takagi` this characterizes
the complex symmetric matrices. -/
theorem transpose_mul_diagonal_mul_transpose (U : Matrix W W ℂ) (d : W → ℂ) :
    (U * Matrix.diagonal d * Uᵀ)ᵀ = U * Matrix.diagonal d * Uᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

end Matrices

end Matrix
