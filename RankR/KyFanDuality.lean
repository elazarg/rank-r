/-
Frobenius Ky Fan duality for finite complex matrices.

The proof is deliberately reusable: a finite majorization lemma controls the
action of an operator on any orthonormal tuple by its leading squared singular
values, while a truncated spectral factor constructs an optimal
rank-constrained Frobenius test matrix.  The two directions identify the
rank-`k`, unit-Frobenius dual supremum with the sum of the first `k` squared
singular values, including `k = 0` and `k` beyond the ambient dimension.
-/
import RankR.Kronecker

namespace RankR

open Finset

/-- A finite rearrangement inequality: bounded nonnegative weights of total
mass `r` maximize an antitone nonnegative sequence on its first `r` terms. -/
theorem weighted_antitone_sum_le_head
    {n r : ℕ} (hr : r ≤ n) (lam w : Fin n → ℝ)
    (hlam : Antitone lam) (hlam0 : ∀ i, 0 ≤ lam i)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hwsum : ∑ i, w i = r) :
    ∑ i, lam i * w i ≤
      ∑ i : Fin r, lam (Fin.castLE hr i) := by
  classical
  let H : Finset (Fin n) := Finset.univ.filter fun i => i.val < r
  let castEmb : Fin r ↪ Fin n := ⟨Fin.castLE hr, Fin.castLE_injective hr⟩
  have hH : H = Finset.univ.map castEmb := by
    ext i
    simp only [H, mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk,
      castEmb]
    constructor
    · intro hi
      exact ⟨⟨i, hi⟩, by simp⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  have hHcard : H.card = r := by simp [hH]
  have hhead :
      ∑ i : Fin r, lam (Fin.castLE hr i) = ∑ i ∈ H, lam i := by
    rw [hH, sum_map]
    rfl
  rw [hhead]
  by_cases heq : r = n
  · subst n
    have hHuniv : H = Finset.univ := by
      ext i
      simp [H]
    rw [hHuniv]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_of_le_one_right (hlam0 i) (hw1 i)
  · have hrlt : r < n := lt_of_le_of_ne hr heq
    let t : ℝ := lam ⟨r, hrlt⟩
    have htail : ∑ i ∈ Hᶜ, lam i * w i ≤ t * ∑ i ∈ Hᶜ, w i := by
      rw [mul_sum]
      exact Finset.sum_le_sum fun i hi => by
        have hir : r ≤ i.val := by
          simpa only [H, mem_compl, mem_filter, mem_univ, true_and, not_lt] using hi
        exact mul_le_mul_of_nonneg_right (hlam hir) (hw0 i)
    have hdef :
        t * ∑ i ∈ Hᶜ, w i = t * ∑ i ∈ H, (1 - w i) := by
      congr 1
      have hsplit := H.sum_add_sum_compl w
      calc
        ∑ i ∈ Hᶜ, w i = (r : ℝ) - ∑ i ∈ H, w i := by
          linarith
        _ = ∑ i ∈ H, (1 - w i) := by
          rw [sum_sub_distrib]
          simp [hHcard]
    have hheaddef :
        t * ∑ i ∈ H, (1 - w i) ≤ ∑ i ∈ H, lam i * (1 - w i) := by
      rw [mul_sum]
      exact Finset.sum_le_sum fun i hi => by
        have hir : i.val ≤ r := by
          have : i.val < r := by
            simpa only [H, mem_filter, mem_univ, true_and] using hi
          omega
        exact mul_le_mul_of_nonneg_right (hlam hir) (sub_nonneg.mpr (hw1 i))
    have hsplit_lam := H.sum_add_sum_compl (fun i => lam i * w i)
    calc
      ∑ i, lam i * w i =
          (∑ i ∈ H, lam i * w i) + ∑ i ∈ Hᶜ, lam i * w i := hsplit_lam.symm
      _ ≤ (∑ i ∈ H, lam i * w i) + t * ∑ i ∈ Hᶜ, w i :=
        add_le_add (le_refl _) htail
      _ = (∑ i ∈ H, lam i * w i) + t * ∑ i ∈ H, (1 - w i) := by rw [hdef]
      _ ≤ (∑ i ∈ H, lam i * w i) + ∑ i ∈ H, lam i * (1 - w i) :=
        add_le_add (le_refl _) hheaddef
      _ = ∑ i ∈ H, lam i := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro i hi
        ring

open Matrix ComplexConjugate

/-- Spectral expansion of the squared norm of a finite complex matrix acting
on a Euclidean vector. -/
theorem norm_sq_toEuclideanLin_eq_sum_eigenvalues
    {W : Type*} [Fintype W] [DecidableEq W]
    (M : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    ‖Matrix.toEuclideanLin M x‖ ^ 2 =
      ∑ i : Fin (Fintype.card W),
        (Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvalues
            finrank_euclideanSpace i *
          ‖inner ℂ
            ((Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvectorBasis
              finrank_euclideanSpace i) x‖ ^ 2 := by
  let T := Matrix.toEuclideanLin M
  let S := T.adjoint ∘ₗ T
  let hS := T.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis finrank_euclideanSpace
  have hnorm :
      ‖T x‖ ^ 2 = Complex.re (inner ℂ x (S x)) := by
    simp only [S, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (T x)).symm
  rw [hnorm]
  have hrepr : S x = ∑ i, (b.repr (S x) i) • b i := (b.sum_repr _).symm
  rw [hrepr, inner_sum, Complex.re_sum]
  simp_rw [inner_smul_right]
  change
    ∑ i, Complex.re
      (((hS.eigenvectorBasis finrank_euclideanSpace).repr (S x) i) *
        inner ℂ x (hS.eigenvectorBasis finrank_euclideanSpace i)) =
      ∑ i, hS.eigenvalues finrank_euclideanSpace i *
        ‖inner ℂ (hS.eigenvectorBasis finrank_euclideanSpace i) x‖ ^ 2
  have hreprS : ∀ i,
      (hS.eigenvectorBasis finrank_euclideanSpace).repr (S x) i =
        (hS.eigenvalues finrank_euclideanSpace i : ℂ) *
          (hS.eigenvectorBasis finrank_euclideanSpace).repr x i := by
    intro i
    change
      (hS.eigenvectorBasis finrank_euclideanSpace).repr
          ((T.adjoint ∘ₗ T) x) i =
        (hS.eigenvalues finrank_euclideanSpace i : ℂ) *
          (hS.eigenvectorBasis finrank_euclideanSpace).repr x i
    exact hS.eigenvectorBasis_apply_self_apply finrank_euclideanSpace x i
  simp_rw [hreprS]
  simp_rw [OrthonormalBasis.repr_apply_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← inner_conj_symm x (hS.eigenvectorBasis finrank_euclideanSpace i)]
  rw [mul_assoc, Complex.mul_conj]
  norm_cast
  exact congrArg (fun z : ℝ => hS.eigenvalues finrank_euclideanSpace i * z)
    (Complex.normSq_eq_norm_sq _)

/-- A right singular eigenvector is sent to a vector whose squared norm is its
eigenvalue for `MᴴM`. -/
theorem norm_sq_mulVecE_eigenvector
    {W : Type*} [Fintype W] [DecidableEq W]
    (M : Matrix W W ℂ) (i : Fin (Fintype.card W)) :
    ‖mulVecE M
        ((Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvectorBasis
          finrank_euclideanSpace i)‖ ^ 2 =
      (Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvalues
        finrank_euclideanSpace i := by
  let T := Matrix.toEuclideanLin M
  let hS := T.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis finrank_euclideanSpace
  change ‖T (b i)‖ ^ 2 = hS.eigenvalues finrank_euclideanSpace i
  calc
    ‖T (b i)‖ ^ 2 =
        Complex.re (inner ℂ (b i) ((T.adjoint ∘ₗ T) (b i))) := by
      simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (T (b i))).symm
    _ = Complex.re
        (inner ℂ (b i)
          ((hS.eigenvalues finrank_euclideanSpace i : ℂ) • b i)) := by
      have hev := hS.apply_eigenvectorBasis finrank_euclideanSpace i
      change
        (T.adjoint ∘ₗ T) (b i) =
          (hS.eigenvalues finrank_euclideanSpace i : ℂ) • b i at hev
      exact congrArg (fun y => Complex.re (inner ℂ (b i) y)) hev
    _ = hS.eigenvalues finrank_euclideanSpace i := by
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K, b.norm_eq_one]
      simp

/-- The top right singular eigenvectors attain the squared Ky Fan sum. -/
theorem sum_norm_sq_top_eigenvectors_eq_kyFanSq
    {W : Type*} [Fintype W] [DecidableEq W]
    (k : ℕ) (M : Matrix W W ℂ) :
    let ell := min k (Fintype.card W)
    let hEll : ell ≤ Fintype.card W := min_le_right _ _
    let b :=
      (Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvectorBasis
        finrank_euclideanSpace
    ∑ i : Fin ell, ‖mulVecE M (b (Fin.castLE hEll i))‖ ^ 2 =
      kyFanSq k M := by
  dsimp only
  let T := Matrix.toEuclideanLin M
  let hS := T.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis finrank_euclideanSpace
  let ell := min k (Fintype.card W)
  let hEll : ell ≤ Fintype.card W := min_le_right _ _
  change
    ∑ i : Fin ell, ‖T (b (Fin.castLE hEll i))‖ ^ 2 =
      ∑ i ∈ Finset.range k, T.singularValues i ^ 2
  calc
    ∑ i : Fin ell, ‖T (b (Fin.castLE hEll i))‖ ^ 2 =
        ∑ i : Fin ell,
          T.singularValues (Fin.castLE hEll i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hnorm :=
        norm_sq_mulVecE_eigenvector M (Fin.castLE hEll i)
      change
        ‖T (b (Fin.castLE hEll i))‖ ^ 2 =
          hS.eigenvalues finrank_euclideanSpace (Fin.castLE hEll i) at hnorm
      rw [hnorm]
      exact (T.sq_singularValues_fin finrank_euclideanSpace
        (Fin.castLE hEll i)).symm
    _ = ∑ i ∈ Finset.range ell, T.singularValues i ^ 2 := by
      change
        (∑ i : Fin ell, T.singularValues i.val ^ 2) =
          ∑ i ∈ Finset.range ell, T.singularValues i ^ 2
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    _ = ∑ i ∈ Finset.range k, T.singularValues i ^ 2 := by
      apply Finset.sum_subset (Finset.range_mono (min_le_left _ _))
      intro i hik hiell
      have hni : Fintype.card W ≤ i := by
        have hil : ¬i < min k (Fintype.card W) := by
          simpa [ell] using hiell
        have hik' : i < k := Finset.mem_range.mp hik
        omega
      rw [T.singularValues_of_finrank_le (by simpa [finrank_euclideanSpace])]
      simp

/-- An orthonormal tuple captures at most the leading spectral mass of
`MᴴM`. -/
theorem sum_norm_sq_mulVecE_le_eigenvalue_head
    {W : Type*} [Fintype W] [DecidableEq W]
    {r : ℕ} (hr : r ≤ Fintype.card W)
    (M : Matrix W W ℂ) (x : Fin r → EuclideanSpace ℂ W)
    (hx : Orthonormal ℂ x) :
    ∑ i, ‖mulVecE M (x i)‖ ^ 2 ≤
      ∑ i : Fin r,
        (Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvalues
          finrank_euclideanSpace (Fin.castLE hr i) := by
  let T := Matrix.toEuclideanLin M
  let hS := T.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis finrank_euclideanSpace
  let w : Fin (Fintype.card W) → ℝ :=
    fun a => ∑ i, ‖inner ℂ (b a) (x i)‖ ^ 2
  have hw0 : ∀ a, 0 ≤ w a := fun a =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hw1 : ∀ a, w a ≤ 1 := by
    intro a
    have hb :
        ∑ i, ‖inner ℂ (b a) (x i)‖ ^ 2 =
          ∑ i, ‖inner ℂ (x i) (b a)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_inner_symm]
    change (∑ i, ‖inner ℂ (b a) (x i)‖ ^ 2) ≤ 1
    rw [hb]
    exact (hx.sum_inner_products_le (b a)).trans_eq (by rw [b.norm_eq_one]; norm_num)
  have hwsum : ∑ a, w a = r := by
    change (∑ a, ∑ i, ‖inner ℂ (b a) (x i)‖ ^ 2) = r
    rw [Finset.sum_comm]
    calc
      ∑ i, ∑ a, ‖inner ℂ (b a) (x i)‖ ^ 2 =
          ∑ i, ‖x i‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact b.sum_sq_norm_inner_right (x i)
      _ = r := by simp [hx.1]
  have hweighted := weighted_antitone_sum_le_head hr
    (fun a => hS.eigenvalues finrank_euclideanSpace a) w
    (hS.eigenvalues_antitone finrank_euclideanSpace)
    (T.isPositive_adjoint_comp_self.nonneg_eigenvalues finrank_euclideanSpace)
    hw0 hw1 hwsum
  change
    ∑ i, ‖T (x i)‖ ^ 2 ≤
      ∑ i : Fin r, hS.eigenvalues finrank_euclideanSpace (Fin.castLE hr i)
  rw [Finset.sum_congr rfl fun i _ =>
    norm_sq_toEuclideanLin_eq_sum_eigenvalues M (x i)]
  rw [Finset.sum_comm]
  change
    ∑ a, ∑ i, hS.eigenvalues finrank_euclideanSpace a *
        ‖inner ℂ (b a) (x i)‖ ^ 2 ≤ _
  simp_rw [← Finset.mul_sum]
  exact hweighted

/-- The action of a matrix on any orthonormal `r`-tuple is bounded by its
squared Ky Fan `k`-sum whenever `r ≤ k`. -/
theorem sum_norm_sq_mulVecE_le_kyFanSq
    {W : Type*} [Fintype W] [DecidableEq W]
    {r k : ℕ} (hrk : r ≤ k)
    (M : Matrix W W ℂ) (x : Fin r → EuclideanSpace ℂ W)
    (hx : Orthonormal ℂ x) :
    ∑ i, ‖mulVecE M (x i)‖ ^ 2 ≤ kyFanSq k M := by
  have hrdim : r ≤ Fintype.card W := by
    simpa [finrank_euclideanSpace] using
      hx.linearIndependent.fintype_card_le_finrank
  have hhead := sum_norm_sq_mulVecE_le_eigenvalue_head hrdim M x hx
  have heq :
      (∑ i : Fin r,
          (Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self.eigenvalues
            finrank_euclideanSpace (Fin.castLE hrdim i)) =
        kyFanSq r M := by
    rw [kyFanSq, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    exact
      ((Matrix.toEuclideanLin M).sq_singularValues_fin
        finrank_euclideanSpace (Fin.castLE hrdim i)).symm
  rw [heq] at hhead
  exact hhead.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hrk) (fun i hi hik => sq_nonneg _))

/-- Hilbert--Schmidt pairing against a rank-one matrix is matrix action inside
the vector inner product. -/
theorem hsInner_rankOne_left
    {W : Type*} [Fintype W]
    (x y : EuclideanSpace ℂ W) (M : Matrix W W ℂ) :
    hsInner (rankOne x y) M = inner ℂ x (mulVecE M y) := by
  calc
    hsInner (rankOne x y) M = conj (hsInner M (rankOne x y)) := by
      rw [hsInner_eq_inner, hsInner_eq_inner, inner_conj_symm]
    _ = inner ℂ x (mulVecE M y) := by
      rw [hsInner_rankOne_right, Complex.conj_conj]

/-- Every square matrix has a rank-exact decomposition with an orthonormal
right family and the correct Frobenius energy. -/
theorem exists_right_orthonormal_rankFactor
    {W : Type*} [Fintype W] [DecidableEq W]
    (C : Matrix W W ℂ) :
    ∃ d e : Fin C.rank → EuclideanSpace ℂ W,
      Orthonormal ℂ e ∧
        C = ∑ i, rankOne (d i) (e i) ∧
        ∑ i, ‖d i‖ ^ 2 = hsNormSq C := by
  obtain ⟨n, hn, e₀, d₀, he₀, hCT⟩ :
      ∃ n : ℕ, n = C.rank ∧
        ∃ e d : Fin n → EuclideanSpace ℂ W,
          Orthonormal ℂ e ∧ Cᵀ = rankFactor e d := by
    obtain ⟨e₀, d₀, he₀, hCT⟩ := exists_rankFactor_rank Cᵀ
    exact ⟨Cᵀ.rank, Matrix.rank_transpose C, e₀, d₀, he₀, hCT⟩
  subst n
  refine ⟨fun i => bar (d₀ i), fun i => bar (e₀ i),
    orthonormal_conj he₀, ?_, ?_⟩
  · have h := congrArg (·ᵀ) hCT
    rw [Matrix.transpose_transpose, rankFactor_eq_sum,
      Matrix.transpose_sum] at h
    exact h.trans
      (Finset.sum_congr rfl fun i _ => transpose_rankOne _ _)
  · rw [← hsNormSq_transpose C, hCT,
      hsNormSq_rankFactor_eq e₀ d₀ he₀]
    exact Finset.sum_congr rfl fun i _ => by rw [norm_bar]

/-- A rank-one sum with an orthonormal right family has Frobenius energy equal
to the total squared norm of its left vectors. -/
theorem hsNormSq_sum_rankOne_right
    {W : Type*} [Fintype W]
    {r : ℕ} (d e : Fin r → EuclideanSpace ℂ W)
    (he : Orthonormal ℂ e) :
    hsNormSq (∑ i, rankOne (d i) (e i)) =
      ∑ i, ‖d i‖ ^ 2 := by
  let ec : Fin r → EuclideanSpace ℂ W := fun i => bar (e i)
  let dc : Fin r → EuclideanSpace ℂ W := fun i => bar (d i)
  have hec : Orthonormal ℂ ec := orthonormal_conj he
  have htrans :
      (∑ i, rankOne (d i) (e i))ᵀ = rankFactor ec dc := by
    rw [Matrix.transpose_sum, rankFactor_eq_sum]
    exact Finset.sum_congr rfl fun i _ => transpose_rankOne _ _
  rw [← hsNormSq_transpose, htrans, hsNormSq_rankFactor_eq ec dc hec]
  exact Finset.sum_congr rfl fun i _ => by
    change ‖bar (d i)‖ ^ 2 = ‖d i‖ ^ 2
    rw [norm_bar]

theorem hsNormSq_smul
    {m n : Type*} [Fintype m] [Fintype n]
    (c : ℂ) (A : Matrix m n ℂ) :
    hsNormSq (c • A) = Complex.normSq c * hsNormSq A := by
  rw [hsNormSq_eq_norm_sq, vec_smul, norm_smul, mul_pow,
    ← Complex.normSq_eq_norm_sq, hsNormSq_eq_norm_sq]

theorem exists_kyFan_optimal_test
    {W : Type*} [Fintype W] [DecidableEq W]
    (k : ℕ) (M : Matrix W W ℂ) :
    ∃ C : Matrix W W ℂ,
      C.rank ≤ k ∧
        hsNormSq C = kyFanSq k M ∧
        hsInner C M = (kyFanSq k M : ℂ) := by
  let T := Matrix.toEuclideanLin M
  let hS := T.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis finrank_euclideanSpace
  let ell := min k (Fintype.card W)
  let hEll : ell ≤ Fintype.card W := min_le_right _ _
  let e : Fin ell → EuclideanSpace ℂ W := fun i => b (Fin.castLE hEll i)
  let d : Fin ell → EuclideanSpace ℂ W := fun i => T (e i)
  let C : Matrix W W ℂ := ∑ i, rankOne (d i) (e i)
  have he : Orthonormal ℂ e :=
    b.orthonormal.comp (Fin.castLE hEll) (Fin.castLE_injective hEll)
  have henergy : ∑ i, ‖d i‖ ^ 2 = kyFanSq k M := by
    change
      ∑ i : Fin ell, ‖mulVecE M (b (Fin.castLE hEll i))‖ ^ 2 =
        kyFanSq k M
    exact sum_norm_sq_top_eigenvectors_eq_kyFanSq k M
  refine ⟨C, ?_, ?_, ?_⟩
  · have hrankEll : C.rank ≤ ell := by
      exact (rank_le_iff_exists_sum_rankOne (k := ell) C).2 ⟨d, e, rfl⟩
    exact hrankEll.trans (min_le_left _ _)
  · change hsNormSq (∑ i, rankOne (d i) (e i)) = kyFanSq k M
    rw [hsNormSq_sum_rankOne_right d e he, henergy]
  · change hsInner (∑ i, rankOne (d i) (e i)) M = _
    rw [hsInner_sum_left]
    have hterm : ∀ i,
        hsInner (rankOne (d i) (e i)) M = (‖d i‖ ^ 2 : ℂ) := by
      intro i
      rw [hsInner_rankOne_left]
      change inner ℂ (d i) (d i) = _
      exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (d i)
    simp_rw [hterm]
    norm_cast

theorem kyFanSq_nonneg
    {W : Type*} [Fintype W] [DecidableEq W]
    (k : ℕ) (M : Matrix W W ℂ) :
    0 ≤ kyFanSq k M :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem normSq_hsInner_le_hsNormSq_mul_kyFanSq
    {W : Type*} [Fintype W] [DecidableEq W]
    {k : ℕ} (C M : Matrix W W ℂ) (hrank : C.rank ≤ k) :
    Complex.normSq (hsInner C M) ≤ hsNormSq C * kyFanSq k M := by
  obtain ⟨d, e, he, hC, hdC⟩ := exists_right_orthonormal_rankFactor C
  have hterm : ∀ i,
      ‖hsInner (rankOne (d i) (e i)) M‖
        ≤ ‖d i‖ * ‖mulVecE M (e i)‖ := fun i => by
    rw [hsInner_rankOne_left]
    exact norm_inner_le_norm _ _
  have hsum :
      ‖hsInner C M‖ ≤
        ∑ i, ‖d i‖ * ‖mulVecE M (e i)‖ := by
    have hp :
        hsInner C M =
          ∑ i, hsInner (rankOne (d i) (e i)) M := by
      calc
        hsInner C M =
            hsInner (∑ i, rankOne (d i) (e i)) M :=
          congrArg (fun A => hsInner A M) hC
        _ = _ := hsInner_sum_left _ _
    rw [hp]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => hterm i)
  have hcs :
      ∑ i, ‖d i‖ * ‖mulVecE M (e i)‖ ≤
        Real.sqrt (∑ i, ‖d i‖ ^ 2) *
          Real.sqrt (∑ i, ‖mulVecE M (e i)‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have haction :
      ∑ i, ‖mulVecE M (e i)‖ ^ 2 ≤ kyFanSq k M :=
    sum_norm_sq_mulVecE_le_kyFanSq hrank M e he
  have hA0 : 0 ≤ ∑ i, ‖d i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB0 : 0 ≤ ∑ i, ‖mulVecE M (e i)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsquared :
      ‖hsInner C M‖ ^ 2 ≤
        (∑ i, ‖d i‖ ^ 2) *
          (∑ i, ‖mulVecE M (e i)‖ ^ 2) := by
    have hnonneg : 0 ≤ ‖hsInner C M‖ := norm_nonneg _
    have h2 := mul_self_le_mul_self hnonneg (hsum.trans hcs)
    rw [← Real.sq_sqrt hA0, ← Real.sq_sqrt hB0]
    nlinarith [h2]
  rw [Complex.normSq_eq_norm_sq, ← hdC]
  exact hsquared.trans
    (mul_le_mul_of_nonneg_left haction hA0)

theorem frobeniusRankTestSq_le_kyFanSq
    {W : Type*} [Fintype W] [DecidableEq W]
    (k : ℕ) (M : Matrix W W ℂ) :
    frobeniusRankTestSq k M ≤ kyFanSq k M := by
  apply frobeniusRankTestSq_le_of_pointwise (kyFanSq_nonneg k M)
  intro C hrank
  simpa [mul_comm] using
    normSq_hsInner_le_hsNormSq_mul_kyFanSq C M hrank

theorem kyFanSq_le_frobeniusRankTestSq
    {W : Type*} [Fintype W] [DecidableEq W]
    (k : ℕ) (M : Matrix W W ℂ) :
    kyFanSq k M ≤ frobeniusRankTestSq k M := by
  let S := kyFanSq k M
  have hSnonneg : 0 ≤ S := kyFanSq_nonneg k M
  by_cases hSzero : S = 0
  · have hzero : 0 ∈ frobeniusRankTestValues k M := by
      refine ⟨0, ?_, ?_, ?_⟩
      · simp
      · simp [hsNormSq]
      · simp [hsInner]
    change S ≤ sSup (frobeniusRankTestValues k M)
    rw [hSzero]
    exact le_csSup (frobeniusRankTestValues_bddAbove k M) hzero
  · have hSpos : 0 < S := lt_of_le_of_ne hSnonneg (Ne.symm hSzero)
    obtain ⟨C₀, hrank₀, hnorm₀, hpair₀⟩ :=
      exists_kyFan_optimal_test k M
    let c : ℂ := ((Real.sqrt S : ℝ) : ℂ)⁻¹
    let C : Matrix W W ℂ := c • C₀
    have hsqrt : Real.sqrt S ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hSpos)
    have hc : c ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hsqrt)
    have hcnorm : Complex.normSq c = S⁻¹ := by
      change Complex.normSq (((Real.sqrt S : ℝ) : ℂ)⁻¹) = S⁻¹
      rw [Complex.normSq_inv, Complex.normSq_ofReal, ← pow_two,
        Real.sq_sqrt hSnonneg]
    have hrank : C.rank ≤ k := by
      change (c • C₀).rank ≤ k
      rw [rank_smul_eq_of_ne_zero C₀ hc]
      exact hrank₀
    have hnorm : hsNormSq C = 1 := by
      change hsNormSq (c • C₀) = 1
      rw [hsNormSq_smul, hcnorm, hnorm₀]
      change S⁻¹ * S = 1
      exact inv_mul_cancel₀ hSzero
    have hpair : Complex.normSq (hsInner C M) = S := by
      change Complex.normSq (hsInner (c • C₀) M) = S
      rw [hsInner_smul_left, hpair₀, Complex.normSq_mul,
        Complex.normSq_conj, hcnorm, Complex.normSq_ofReal]
      change S⁻¹ * (S * S) = S
      rw [← mul_assoc, inv_mul_cancel₀ hSzero, one_mul]
    have hmem : S ∈ frobeniusRankTestValues k M :=
      ⟨C, hrank, hnorm.le, hpair.symm⟩
    change S ≤ sSup (frobeniusRankTestValues k M)
    exact le_csSup (frobeniusRankTestValues_bddAbove k M) hmem

/-- Frobenius Ky Fan duality for finite complex matrices. -/
theorem kyFanFrobeniusDuality
    {W : Type*} [Fintype W] [DecidableEq W]
    (k : ℕ) (M : Matrix W W ℂ) :
    KyFanFrobeniusDuality k M := by
  exact le_antisymm
    (kyFanSq_le_frobeniusRankTestSq k M)
    (frobeniusRankTestSq_le_kyFanSq k M)

section KroneckerKyFan

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The literal singular-value form of the Kronecker-sum bound. -/
theorem kyFanSq_kroneckerSum_le {k : ℕ} (hk : 0 < k)
    (A B : Matrix D D ℂ) (hA : A.trace = 0) (hB : B.trace = 0)
    (hd : 0 < Fintype.card D) :
    kyFanSq k (kroneckerSum A B) ≤
      kroneckerKyFanCoeff k (Fintype.card D)
        * (hsNormSq A + hsNormSq B) :=
  kyFanSq_kroneckerSum_le_of_duality hk A B hA hB hd
    (kyFanFrobeniusDuality k (kroneckerSum A B))

/-- When `d ≤ 2k`, the Kronecker-sum Ky Fan coefficient simplifies to `k`. -/
theorem kyFanSq_kroneckerSum_le_of_card_le_two_mul {k : ℕ} (hk : 0 < k)
    (A B : Matrix D D ℂ) (hA : A.trace = 0) (hB : B.trace = 0)
    (hd : 0 < Fintype.card D) (hdk : Fintype.card D ≤ 2 * k) :
    kyFanSq k (kroneckerSum A B) ≤
      (k : ℝ) * (hsNormSq A + hsNormSq B) :=
  kyFanSq_kroneckerSum_le_of_card_le_two_mul_of_duality
    hk A B hA hB hd hdk
    (kyFanFrobeniusDuality k (kroneckerSum A B))

end KroneckerKyFan

end RankR
