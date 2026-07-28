/-
Rigidity of marginal-preserving classical embeddings.

A classical joint distribution on `U × V` can be carried to an operator on
`U ⊗ V` in many ways.  Requiring only two things of the encoding --- that it
send entrywise-nonnegative matrices to positive semidefinite operators, and
that it reproduce the two classical marginals as the two partial traces ---
already forces it to be the diagonal embedding
`P ↦ ∑_{a,b} P_{ab} |ab⟩⟨ab|`.

The consequence is that operator rank of the image is the *support size* of
`P`, never its matrix rank.  So the coupled-marginal inequalities of this
development cannot distinguish a low-rank classical distribution from a
small-support one: the two notions coincide on the image of any encoding
meeting those hypotheses, and no other encoding meets them.

The argument stays on the diagonal.  A pure marginal forces a whole slab of
diagonal entries to vanish, positivity propagates each vanishing diagonal
entry to its row and column, and what survives is a single entry pinned to `1`
by the trace.
-/
import RankR.Results

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## Positivity on the diagonal

Two facts about a matrix whose quadratic form has nonnegative real part.  They
are stated for the pair (`Fᴴ = F`, `0 ≤ (qform F z).re`) rather than through
`Matrix.PosSemidef`, matching the idiom of the rest of the development; the
Hermitian hypothesis is needed because nonnegativity of the *real part* alone
does not force self-adjointness. -/

section Positivity

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The quadratic form at a standard basis vector is the corresponding diagonal
entry. -/
theorem qform_single (F : Matrix W W ℂ) (x : W) :
    qform F (eBasis x) = F x x := by
  rw [qform]
  have hinner : ∀ p : W, ∑ q, conj (eBasis x p) * F p q * eBasis x q
      = conj (eBasis x p) * F p x := fun p => by
    rw [Finset.sum_eq_single x (fun q _ hq => by simp [hq])
      (fun h => absurd (Finset.mem_univ x) h)]
    simp
  rw [Finset.sum_congr rfl fun p _ => hinner p,
    Finset.sum_eq_single x (fun p _ hp => by simp [hp])
      (fun h => absurd (Finset.mem_univ x) h)]
  simp

/-- A matrix with nonnegative quadratic form has nonnegative diagonal. -/
theorem diag_re_nonneg {F : Matrix W W ℂ} (hpos : ∀ z, 0 ≤ (qform F z).re) (x : W) :
    0 ≤ (F x x).re := by
  have h := hpos (eBasis x)
  rwa [qform_single] at h

/-- The quadratic form on the span of two basis vectors.  The two need not be
distinct: at `x = y` both sides collapse to `‖a+b‖² F x x`. -/
theorem qform_pair (F : Matrix W W ℂ) (a b : ℂ) {x y : W} :
    qform F (a • eBasis x + b • eBasis y)
      = conj a * a * F x x + conj a * b * F x y
        + (conj b * a * F y x + conj b * b * F y y) := by
  set z : EuclideanSpace ℂ W := a • eBasis x + b • eBasis y with hzdef
  have hz : ∀ p : W, z p = (if p = x then a else 0) + (if p = y then b else 0) := by
    intro p
    simp only [hzdef, PiLp.add_apply, PiLp.smul_apply, eBasis_apply, smul_eq_mul]
    split_ifs <;> ring
  have hinner : ∀ p : W, ∑ q, conj (z p) * F p q * z q
      = conj (z p) * (F p x * a + F p y * b) := fun p => by
    have hstep : ∀ q : W, conj (z p) * F p q * z q
        = (if q = x then conj (z p) * F p q * a else 0)
          + (if q = y then conj (z p) * F p q * b else 0) := fun q => by
      rw [hz q]; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun q _ => hstep q, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ x, Finset.sum_ite_eq' Finset.univ y]
    simp only [Finset.mem_univ, if_true]
    ring
  rw [qform, Finset.sum_congr rfl fun p _ => hinner p]
  have hsplit : ∀ p : W, conj (z p) * (F p x * a + F p y * b)
      = (if p = x then conj a * (F p x * a + F p y * b) else 0)
        + (if p = y then conj b * (F p x * a + F p y * b) else 0) := fun p => by
    rw [hz p, map_add, apply_ite conj, apply_ite conj, map_zero]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun p _ => hsplit p, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ x, Finset.sum_ite_eq' Finset.univ y]
  simp only [Finset.mem_univ, if_true]
  ring

/-- **A vanishing diagonal entry annihilates its row.**  For `F` Hermitian with
nonnegative quadratic form, `F x x = 0` forces `F x y = 0` for every `y`.

Testing on `−λ\overline{F_{xy}}` at `x` and `1` at `y` gives
`−2λ|F_{xy}|² + (F_{yy})_{re} ≥ 0` for every `λ > 0`, which is possible only if
`F x y` vanishes. -/
theorem row_eq_zero_of_diag_eq_zero {F : Matrix W W ℂ} (hherm : Fᴴ = F)
    (hpos : ∀ z, 0 ≤ (qform F z).re) {x : W} (hx : F x x = 0) (y : W) :
    F x y = 0 := by
  rcases eq_or_ne x y with rfl | hxy
  · exact hx
  by_contra hc
  have hcc : (0 : ℝ) < Complex.normSq (F x y) := Complex.normSq_pos.mpr hc
  have hyx : F y x = conj (F x y) := by
    have h := congrFun (congrFun hherm x) y
    rw [Matrix.conjTranspose_apply] at h
    rw [← h]
    simp
  -- the quadratic form at `(-λ (F x y)) e_x + e_y`
  have hval : ∀ lam : ℝ,
      (qform F ((-(lam : ℂ) * F x y) • eBasis x + (1 : ℂ) • eBasis y)).re
      = -2 * lam * Complex.normSq (F x y) + (F y y).re := by
    intro lam
    have hns : conj (F x y) * F x y = (Complex.normSq (F x y) : ℂ) :=
      (Complex.normSq_eq_conj_mul_self).symm
    have heq : qform F ((-(lam : ℂ) * F x y) • eBasis x + (1 : ℂ) • eBasis y)
        = (((-2 * lam * Complex.normSq (F x y) : ℝ)) : ℂ) + F y y := by
      rw [qform_pair F, hx, hyx]
      simp only [map_mul, map_neg, map_one, Complex.conj_ofReal, mul_zero, zero_add,
        mul_one, one_mul]
      push_cast
      linear_combination (-2 * (lam : ℂ)) * hns
    rw [heq, Complex.add_re, Complex.ofReal_re]
  have hMnonneg : 0 ≤ (F y y).re := diag_re_nonneg hpos y
  have hbound : ∀ lam : ℝ, 0 < lam → 2 * lam * Complex.normSq (F x y) ≤ (F y y).re := by
    intro lam _
    have h := hpos ((-(lam : ℂ) * F x y) • eBasis x + (1 : ℂ) • eBasis y)
    rw [hval lam] at h
    linarith
  have hSne : Complex.normSq (F x y) ≠ 0 := hcc.ne'
  have hbig := hbound (((F y y).re + 1) / Complex.normSq (F x y)) (div_pos (by linarith) hcc)
  rw [mul_assoc, div_mul_cancel₀ _ hSne] at hbig
  linarith

end Positivity

/-! ## Rigidity -/

section Rigidity

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- The rank-one projection onto a standard basis vector. -/
noncomputable def basisProj {W : Type*} [Fintype W] [DecidableEq W] (x : W) :
    Matrix W W ℂ :=
  rankOne (eBasis x) (eBasis x)

/-- The entries of the standard basis-vector projection: `1` at `(x, x)`, else `0`. -/
theorem basisProj_apply {W : Type*} [Fintype W] [DecidableEq W] (x p q : W) :
    basisProj x p q = if p = x then (if q = x then (1 : ℂ) else 0) else 0 := by
  simp only [basisProj, rankOne, Matrix.of_apply, eBasis_apply]
  split_ifs <;> simp_all

/-- A slab of vanishing diagonal entries, read off a pure marginal.  If the
`U`-marginal of `F` is the projection onto `i`, then every diagonal entry over
a row `a ≠ i` vanishes. -/
theorem diag_eq_zero_of_ptraceV {F : Matrix (U × V) (U × V) ℂ} (hherm : Fᴴ = F)
    (hpos : ∀ z, 0 ≤ (qform F z).re) {i : U} (hU : ptraceV F = basisProj i)
    {a : U} (ha : a ≠ i) (b : V) : F (a, b) (a, b) = 0 := by
  have hsum : ∑ b' : V, F (a, b') (a, b') = 0 := by
    have h := congrFun (congrFun hU a) a
    rw [ptraceV_apply, basisProj_apply, if_neg ha] at h
    exact h
  have hre : ∑ b' : V, (F (a, b') (a, b')).re = 0 := by
    have := congrArg Complex.re hsum
    rwa [Complex.re_sum] at this
  have hall : ∀ b' : V, (F (a, b') (a, b')).re = 0 := fun b' =>
    (Finset.sum_eq_zero_iff_of_nonneg fun b' _ => diag_re_nonneg hpos (a, b')).mp hre
      b' (Finset.mem_univ b')
  have him : (F (a, b) (a, b)).im = 0 := by
    have h := congrFun (congrFun hherm (a, b)) (a, b)
    rw [Matrix.conjTranspose_apply] at h
    exact Complex.conj_eq_iff_im.mp h
  exact Complex.ext (hall b) him

/-- The mirror statement for the `V`-marginal. -/
theorem diag_eq_zero_of_ptraceU {F : Matrix (U × V) (U × V) ℂ} (hherm : Fᴴ = F)
    (hpos : ∀ z, 0 ≤ (qform F z).re) {j : V} (hV : ptraceU F = basisProj j)
    (a : U) {b : V} (hb : b ≠ j) : F (a, b) (a, b) = 0 := by
  have hsum : ∑ a' : U, F (a', b) (a', b) = 0 := by
    have h := congrFun (congrFun hV b) b
    rw [ptraceU_apply, basisProj_apply, if_neg hb] at h
    exact h
  have hre : ∑ a' : U, (F (a', b) (a', b)).re = 0 := by
    have := congrArg Complex.re hsum
    rwa [Complex.re_sum] at this
  have hall : ∀ a' : U, (F (a', b) (a', b)).re = 0 := fun a' =>
    (Finset.sum_eq_zero_iff_of_nonneg fun a' _ => diag_re_nonneg hpos (a', b)).mp hre
      a' (Finset.mem_univ a')
  have him : (F (a, b) (a, b)).im = 0 := by
    have h := congrFun (congrFun hherm (a, b)) (a, b)
    rw [Matrix.conjTranspose_apply] at h
    exact Complex.conj_eq_iff_im.mp h
  exact Complex.ext (hall a) him

/-- **Point-mass rigidity.**  A positive semidefinite operator on `U ⊗ V` whose
two partial traces are the pure states at `i` and at `j` is the pure product
state at `(i, j)`.

Every diagonal entry off the row `i` vanishes by `diag_eq_zero_of_ptraceV`, and
every one off the column `j` by `diag_eq_zero_of_ptraceU`; positivity carries
each vanishing diagonal entry to its whole row, so only the `(i, j)` entry can
survive, and the marginal pins it to `1`. -/
theorem eq_basisProj_of_pure_marginals {F : Matrix (U × V) (U × V) ℂ}
    (hherm : Fᴴ = F) (hpos : ∀ z, 0 ≤ (qform F z).re) {i : U} {j : V}
    (hU : ptraceV F = basisProj i) (hV : ptraceU F = basisProj j) :
    F = basisProj (i, j) := by
  have hdiag : ∀ x : U × V, x ≠ (i, j) → F x x = 0 := by
    rintro ⟨a, b⟩ hx
    rcases eq_or_ne a i with rfl | ha
    · exact diag_eq_zero_of_ptraceU hherm hpos hV a (fun hb => hx (by rw [hb]))
    · exact diag_eq_zero_of_ptraceV hherm hpos hU ha b
  have hone : F (i, j) (i, j) = 1 := by
    have h := congrFun (congrFun hU i) i
    rw [ptraceV_apply, basisProj_apply, if_pos rfl, if_pos rfl] at h
    rw [← h]
    refine (Finset.sum_eq_single (f := fun b : V => F (i, b) (i, b)) j
      (fun b _ hb => ?_) (fun hb => absurd (Finset.mem_univ j) hb)).symm
    exact hdiag (i, b) (fun hc => hb (congrArg Prod.snd hc))
  ext x y
  rcases eq_or_ne x (i, j) with rfl | hx
  · rcases eq_or_ne y (i, j) with rfl | hy
    · rw [hone, basisProj_apply, if_pos rfl, if_pos rfl]
    · have hyz : F y y = 0 := hdiag y hy
      have hyx0 : F y (i, j) = 0 := row_eq_zero_of_diag_eq_zero hherm hpos hyz (i, j)
      have hxy0 : F (i, j) y = 0 := by
        have hh := congrFun (congrFun hherm (i, j)) y
        rw [Matrix.conjTranspose_apply] at hh
        rw [← hh, hyx0]
        simp
      rw [hxy0, basisProj_apply, if_pos rfl, if_neg hy]
  · rw [row_eq_zero_of_diag_eq_zero hherm hpos (hdiag x hx) y,
      basisProj_apply, if_neg hx]

/-- **The encoding is the diagonal one.**  Any encoding that is determined by
its values on point masses, sends each point mass to a positive semidefinite
operator, and reproduces both classical marginals, is
`P ↦ ∑_{a,b} P_{ab}\,\lvert ab\rangle\langle ab\rvert`. -/
theorem eq_diagonal_embedding
    (E : Matrix U V ℝ → Matrix (U × V) (U × V) ℂ)
    (hlin : ∀ P : Matrix U V ℝ,
      E P = ∑ p : U × V, ((P p.1 p.2 : ℝ) : ℂ) • E (Matrix.single p.1 p.2 1))
    (hherm : ∀ p : U × V, (E (Matrix.single p.1 p.2 1))ᴴ = E (Matrix.single p.1 p.2 1))
    (hpos : ∀ (p : U × V) z, 0 ≤ (qform (E (Matrix.single p.1 p.2 1)) z).re)
    (hU : ∀ p : U × V, ptraceV (E (Matrix.single p.1 p.2 1)) = basisProj p.1)
    (hV : ∀ p : U × V, ptraceU (E (Matrix.single p.1 p.2 1)) = basisProj p.2)
    (P : Matrix U V ℝ) :
    E P = ∑ p : U × V, ((P p.1 p.2 : ℝ) : ℂ) • basisProj p := by
  rw [hlin P]
  exact Finset.sum_congr rfl fun p _ => by
    rw [eq_basisProj_of_pure_marginals (hherm p) (hpos p) (hU p) (hV p)]

/-- The diagonal embedding is `Matrix.diagonal` of the entries of `P`. -/
theorem sum_smul_basisProj_eq_diagonal (P : Matrix U V ℝ) :
    (∑ p : U × V, ((P p.1 p.2 : ℝ) : ℂ) • basisProj p)
      = Matrix.diagonal fun p : U × V => ((P p.1 p.2 : ℝ) : ℂ) := by
  ext x y
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  have hterm : ∀ p : U × V, (((P p.1 p.2 : ℝ) : ℂ) • basisProj p) x y
      = if p = x then (if x = y then ((P p.1 p.2 : ℝ) : ℂ) else 0) else 0 := by
    intro p
    rw [Matrix.smul_apply, smul_eq_mul, basisProj_apply]
    by_cases hpx : p = x
    · rw [hpx, if_pos rfl, if_pos rfl]
      by_cases hxy : x = y <;> simp [hxy, eq_comm]
    · rw [if_neg hpx, if_neg (Ne.symm hpx), mul_zero]
  rw [Finset.sum_congr rfl fun p _ => hterm p,
    Finset.sum_ite_eq' Finset.univ x
      (fun p : U × V => if x = y then ((P p.1 p.2 : ℝ) : ℂ) else 0)]
  simp

/-- **Operator rank is support size.**  Under the hypotheses of
`eq_diagonal_embedding`, the rank of the encoded operator counts the nonzero
entries of `P`, whatever the matrix rank of `P` may be. -/
theorem rank_eq_card_support
    (E : Matrix U V ℝ → Matrix (U × V) (U × V) ℂ)
    (hlin : ∀ P : Matrix U V ℝ,
      E P = ∑ p : U × V, ((P p.1 p.2 : ℝ) : ℂ) • E (Matrix.single p.1 p.2 1))
    (hherm : ∀ p : U × V, (E (Matrix.single p.1 p.2 1))ᴴ = E (Matrix.single p.1 p.2 1))
    (hpos : ∀ (p : U × V) z, 0 ≤ (qform (E (Matrix.single p.1 p.2 1)) z).re)
    (hU : ∀ p : U × V, ptraceV (E (Matrix.single p.1 p.2 1)) = basisProj p.1)
    (hV : ∀ p : U × V, ptraceU (E (Matrix.single p.1 p.2 1)) = basisProj p.2)
    (P : Matrix U V ℝ) :
    (E P).rank = (Finset.univ.filter fun p : U × V => P p.1 p.2 ≠ 0).card := by
  rw [eq_diagonal_embedding E hlin hherm hpos hU hV P, sum_smul_basisProj_eq_diagonal,
    Matrix.rank_diagonal, Fintype.card_subtype]
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  simp [Complex.ofReal_eq_zero]

end Rigidity

end RankR
