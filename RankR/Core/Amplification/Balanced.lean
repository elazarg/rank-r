/-
The balanced-polarization lifting mechanism.

This is independent of the Choi pair construction.  Its inputs are a sharp
rank-one estimate, a four-linear crossed-polarization identity, and a balanced
rank factorization with equal left and right Gram matrices.
-/
import RankR.Library.Matrix.BalancedFactorization

namespace RankR

open Matrix Finset ComplexConjugate

section Definitions

variable {W E : Type*} [Fintype W]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The rank-one input used by the balanced-polarization lift. -/
def HasRankOneTraceBound (L : Matrix W W ℂ →ₗ[ℂ] E) : Prop :=
  ∀ x y : EuclideanSpace ℂ W,
    ‖L (rankOne x y)‖ ^ 2
      ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 + Complex.normSq (inner ℂ y x)

/-- The four-linear crossing symmetry used to control off-diagonal summands. -/
def HasCrossedPolarization (L : Matrix W W ℂ →ₗ[ℂ] E) : Prop :=
  ∀ u v s t : EuclideanSpace ℂ W,
    inner ℂ (L (rankOne u v)) (L (rankOne s t))
      = inner ℂ (L (rankOne t v)) (L (rankOne s u))

end Definitions

section Elementary

variable {W E : Type*} [Fintype W]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {q : ℕ}

/-- The squared norm of a finite sum as the real part of its full Gram sum. -/
theorem norm_sum_sq_eq_sum_re_inner (z : Fin q → E) :
    ‖∑ i, z i‖ ^ 2 = ∑ i, ∑ j, (inner ℂ (z i) (z j)).re := by
  calc
    ‖∑ i, z i‖ ^ 2 = (inner ℂ (∑ i, z i) (∑ j, z j)).re := by
      change ‖∑ i, z i‖ ^ 2 = (inner ℂ (∑ i, z i) (∑ i, z i)).re
      exact InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (∑ i, ∑ j, inner ℂ (z i) (z j)).re := by
      congr 1
      simp only [sum_inner, inner_sum]
      rw [Finset.sum_comm]
    _ = _ := by simp only [Complex.re_sum]

/-- Removing the diagonal from a real double sum. -/
theorem sum_sum_ite_ne_balanced (f : Fin q → Fin q → ℝ) :
    ∑ i, ∑ j, (if i ≠ j then f i j else 0)
      = (∑ i, ∑ j, f i j) - ∑ i, f i i := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j : Fin q,
      (if i ≠ j then f i j else 0)
        = f i j - (if i = j then f i j else 0) :=
    fun j => by by_cases hij : i = j <;> simp [hij]
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_sub_distrib,
    Finset.sum_ite_eq]
  simp

/-- Equal Gram matrices give equal squared norms term by term. -/
theorem norm_sq_eq_of_gram_eq
    {e d : Fin q → EuclideanSpace ℂ W}
    (hG : ∀ i j, inner ℂ (e i) (e j) = inner ℂ (d i) (d j)) (i : Fin q) :
    ‖e i‖ ^ 2 = ‖d i‖ ^ 2 := by
  have h := hG i i
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- The Hilbert--Schmidt norm of an equal-Gram rank factorization is the
sum of the squared moduli of its Gram entries. -/
theorem hsNormSq_rankFactor_of_gram_eq
    {e d : Fin q → EuclideanSpace ℂ W}
    (hG : ∀ i j, inner ℂ (e i) (e j) = inner ℂ (d i) (d j)) :
    hsNormSq (rankFactor e d)
      = ∑ i, ∑ j, Complex.normSq (inner ℂ (e i) (e j)) := by
  rw [← Complex.ofReal_inj, hsNormSq_rankFactor]
  push_cast
  refine Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  rw [← hG i j, Complex.normSq_eq_conj_mul_self]
  ring

end Elementary

section PairBounds

variable {W E : Type*} [Fintype W]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {q : ℕ} {L : Matrix W W ℂ →ₗ[ℂ] E}
  {e d : Fin q → EuclideanSpace ℂ W} {τ : ℂ}

/-- The diagonal estimate after the trace overlaps have been balanced. -/
theorem balanced_diagonal_bound
    (hOne : HasRankOneTraceBound L)
    (hbal : IsBalancedRankFactor e d τ) (i : Fin q) :
    ‖L (rankOne (e i) (d i))‖ ^ 2
      ≤ ‖e i‖ ^ 4 + Complex.normSq τ := by
  have h := hOne (e i) (d i)
  rw [← norm_sq_eq_of_gram_eq hbal.1 i, hbal.2 i] at h
  nlinarith

/-- Crossed polarization turns every off-diagonal interaction into two
rank-one terms with the same upper bound. -/
theorem balanced_crossed_re_le
    (hOne : HasRankOneTraceBound L) (hCross : HasCrossedPolarization L)
    (hbal : IsBalancedRankFactor e d τ) (i j : Fin q) :
    (inner ℂ (L (rankOne (e i) (d i)))
      (L (rankOne (e j) (d j)))).re
      ≤ ‖e j‖ ^ 2 * ‖e i‖ ^ 2
        + Complex.normSq (inner ℂ (e i) (e j)) := by
  let R : ℝ :=
    ‖e j‖ ^ 2 * ‖e i‖ ^ 2
      + Complex.normSq (inner ℂ (e i) (e j))
  have hA := hOne (d j) (d i)
  have hB := hOne (e j) (e i)
  have hni := norm_sq_eq_of_gram_eq hbal.1 i
  have hnj := norm_sq_eq_of_gram_eq hbal.1 j
  rw [← hnj, ← hni, ← hbal.1 i j] at hA
  have hprod :
      ‖L (rankOne (d j) (d i))‖ * ‖L (rankOne (e j) (e i))‖ ≤ R := by
    dsimp [R] at hA hB ⊢
    nlinarith [sq_nonneg
      (‖L (rankOne (d j) (d i))‖ - ‖L (rankOne (e j) (e i))‖)]
  rw [hCross (e i) (d i) (e j) (d j)]
  exact (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans hprod)

end PairBounds

section Summation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {q : ℕ}

/-- The sharp expansion bound before the complete-graph variance and
off-diagonal terms are absorbed into `q` times the full Gram sum. -/
theorem norm_sum_sq_le_balanced_expansion
    (z : Fin q → E) (δ : Fin q → ℝ)
    (b : Fin q → Fin q → ℝ) (t : ℝ)
    (hdiag : ∀ i, ‖z i‖ ^ 2 ≤ δ i ^ 2 + t)
    (hoff : ∀ i j, i ≠ j →
      (inner ℂ (z i) (z j)).re ≤ δ i * δ j + b i j) :
    ‖∑ i, z i‖ ^ 2
      ≤ (∑ i, δ i) ^ 2 + (q : ℝ) * t
        + ∑ i, ∑ j, (if i ≠ j then b i j else 0) := by
  have hpair : ∀ i j,
      (inner ℂ (z i) (z j)).re
        ≤ δ i * δ j + if i = j then t else b i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      calc
        (inner ℂ (z i) (z i)).re = ‖z i‖ ^ 2 :=
          (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
        _ ≤ δ i ^ 2 + t := hdiag i
        _ = δ i * δ i + t := by ring
    · simpa [hij] using hoff i j hij
  have hite :
      (∑ i : Fin q, ∑ j : Fin q, if i = j then t else b i j)
        = (q : ℝ) * t
          + ∑ i : Fin q, ∑ j : Fin q, (if i ≠ j then b i j else 0) := by
    calc
      _ = ∑ i : Fin q, ∑ j : Fin q,
          ((if i = j then t else 0) + if i ≠ j then b i j else 0) := by
            refine Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun j _ => ?_
            by_cases hij : i = j <;> simp [hij]
      _ = (∑ i : Fin q, ∑ j : Fin q, if i = j then t else 0)
          + ∑ i : Fin q, ∑ j : Fin q, (if i ≠ j then b i j else 0) := by
            simp only [Finset.sum_add_distrib]
      _ = _ := by
        congr 1
        calc
          (∑ i, ∑ j, if i = j then t else 0) = ∑ _i : Fin q, t := by
            exact Finset.sum_congr rfl fun i _ => by
              rw [Finset.sum_ite_eq]
              simp
          _ = (q : ℝ) * t := by
            simp [Finset.sum_const, nsmul_eq_mul]
  rw [norm_sum_sq_eq_sum_re_inner]
  calc
    _ ≤ ∑ i, ∑ j,
        (δ i * δ j + if i = j then t else b i j) :=
      Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hpair i j
    _ = (∑ i, δ i) ^ 2 + (∑ i, ∑ j, if i = j then t else b i j) := by
      rw [show (∑ i, ∑ j, (δ i * δ j
          + if i = j then t else b i j))
            = (∑ i, ∑ j, δ i * δ j)
              + ∑ i, ∑ j, (if i = j then t else b i j) by
            simp only [Finset.sum_add_distrib]]
      congr 1
      rw [← Finset.sum_mul_sum]
      ring
    _ = _ := by rw [hite]; ring

/-- The real finite-sum core of the balanced lift.  The diagonal terms pay the
single scalar cost `t`, while crossed polarization supplies the off-diagonal
Gram costs `b`. -/
theorem norm_sum_sq_le_of_balanced_pairs
    (hq : 0 < q) (z : Fin q → E) (δ : Fin q → ℝ)
    (b : Fin q → Fin q → ℝ) (t : ℝ)
    (hb : ∀ i j, 0 ≤ b i j)
    (hbdiag : ∀ i, b i i = δ i ^ 2)
    (hdiag : ∀ i, ‖z i‖ ^ 2 ≤ δ i ^ 2 + t)
    (hoff : ∀ i j, i ≠ j →
      (inner ℂ (z i) (z j)).re ≤ δ i * δ j + b i j) :
    ‖∑ i, z i‖ ^ 2 ≤ (q : ℝ) * (∑ i, ∑ j, b i j) + (q : ℝ) * t := by
  have hupper :
      ‖∑ i, z i‖ ^ 2
        ≤ (∑ i, δ i) ^ 2 + (q : ℝ) * t
          + ∑ i, ∑ j, (if i ≠ j then b i j else 0) :=
    norm_sum_sq_le_balanced_expansion z δ b t hdiag hoff
  have hdiagSum :
      ∑ i, b i i = ∑ i, δ i ^ 2 :=
    Finset.sum_congr rfl fun i _ => hbdiag i
  let off : ℝ := ∑ i, ∑ j, (if i ≠ j then b i j else 0)
  have hoffEq :
      off = (∑ i, ∑ j, b i j) - ∑ i, b i i := by
    exact sum_sum_ite_ne_balanced b
  have hoffNonneg : 0 ≤ off := by
    dsimp [off]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => by
        by_cases hij : i ≠ j
        · simp [hij, hb i j]
        · simp [hij]
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hcs : (∑ i, δ i) ^ 2 ≤ (q : ℝ) * ∑ i, δ i ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin q))) (f := δ))
  have hoffLe : off ≤ (q : ℝ) * off := by nlinarith
  have hgram :
      (∑ i, δ i) ^ 2 + off ≤ (q : ℝ) * (∑ i, ∑ j, b i j) := by
    rw [hoffEq, hdiagSum] at hoffNonneg ⊢
    nlinarith
  exact hupper.trans (by
    dsimp [off] at hgram
    linarith)

end Summation

section Lift

variable {W E : Type*} [Fintype W]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {q : ℕ} {L : Matrix W W ℂ →ₗ[ℂ] E}
  {e d : Fin q → EuclideanSpace ℂ W} {τ : ℂ}

/-- The balanced-polarization lift along a supplied balanced factorization. -/
theorem balancedPolarization_rankFactor_le
    (hq : 0 < q) (hOne : HasRankOneTraceBound L)
    (hCross : HasCrossedPolarization L)
    (hbal : IsBalancedRankFactor e d τ) :
    ‖L (rankFactor e d)‖ ^ 2
      ≤ (q : ℝ) * hsNormSq (rankFactor e d)
        + (q : ℝ) * Complex.normSq τ := by
  have hsum := norm_sum_sq_le_of_balanced_pairs hq
    (fun i => L (rankOne (e i) (d i)))
    (fun i => ‖e i‖ ^ 2)
    (fun i j => Complex.normSq (inner ℂ (e i) (e j)))
    (Complex.normSq τ)
    (fun i j => Complex.normSq_nonneg _)
    (fun i => by
      rw [inner_self_eq_norm_sq_to_K]
      simp [Complex.normSq_eq_norm_sq, norm_pow])
    (fun i => by
      have h := balanced_diagonal_bound hOne hbal i
      nlinarith)
    (fun i j _ => by
      have h := balanced_crossed_re_le hOne hCross hbal i j
      nlinarith)
  rw [← hsNormSq_rankFactor_of_gram_eq hbal.1] at hsum
  simpa only [← map_sum, ← rankFactor_eq_sum] using hsum

/-- The complete-graph defect retained by the balanced-polarization proof.
The first term is the variance of the diagonal Gram entries; the second is
`q - 1` times the ordered off-diagonal Gram mass. -/
theorem balancedPolarization_rankFactor_defect_le
    (hOne : HasRankOneTraceBound L)
    (hCross : HasCrossedPolarization L)
    (hbal : IsBalancedRankFactor e d τ) :
    (q : ℝ) * (∑ i, ‖e i‖ ^ 4) - (∑ i, ‖e i‖ ^ 2) ^ 2
        + ((q : ℝ) - 1) * ∑ i, ∑ j,
          (if i ≠ j then Complex.normSq (inner ℂ (e i) (e j)) else 0)
      ≤ (q : ℝ) * hsNormSq (rankFactor e d)
        + (q : ℝ) * Complex.normSq τ
        - ‖L (rankFactor e d)‖ ^ 2 := by
  let b : Fin q → Fin q → ℝ :=
    fun i j => Complex.normSq (inner ℂ (e i) (e j))
  let off : ℝ := ∑ i, ∑ j, (if i ≠ j then b i j else 0)
  have hsum := norm_sum_sq_le_balanced_expansion
    (fun i => L (rankOne (e i) (d i)))
    (fun i => ‖e i‖ ^ 2) b (Complex.normSq τ)
    (fun i => by
      have h := balanced_diagonal_bound hOne hbal i
      nlinarith)
    (fun i j _ => by
      have h := balanced_crossed_re_le hOne hCross hbal i j
      dsimp [b]
      nlinarith)
  have hsum' :
      ‖L (rankFactor e d)‖ ^ 2
        ≤ (∑ i, ‖e i‖ ^ 2) ^ 2
          + (q : ℝ) * Complex.normSq τ + off := by
    simpa only [← map_sum, ← rankFactor_eq_sum, off, b] using hsum
  have hdiag :
      ∑ i, b i i = ∑ i, ‖e i‖ ^ 4 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [b]
    rw [inner_self_eq_norm_sq_to_K]
    simp [Complex.normSq_eq_norm_sq, norm_pow]
    ring
  have hoff :
      off = (∑ i, ∑ j, b i j) - ∑ i, b i i :=
    sum_sum_ite_ne_balanced b
  have hgram :
      hsNormSq (rankFactor e d) = ∑ i, ∑ j, b i j := by
    simpa only [b] using hsNormSq_rankFactor_of_gram_eq hbal.1
  change (q : ℝ) * (∑ i, ‖e i‖ ^ 4) - (∑ i, ‖e i‖ ^ 2) ^ 2
      + ((q : ℝ) - 1) * off
    ≤ (q : ℝ) * hsNormSq (rankFactor e d)
      + (q : ℝ) * Complex.normSq τ - ‖L (rankFactor e d)‖ ^ 2
  rw [hoff, hdiag] at hsum' ⊢
  rw [hgram]
  linarith

/-- The manuscript form of the balanced lift: a constant diagonal turns the
scalar cost into `|Tr C|² / q`. -/
theorem balancedPolarization_rankFactor_trace_le
    (hq : 0 < q) (hOne : HasRankOneTraceBound L)
    (hCross : HasCrossedPolarization L)
    (hbal : IsBalancedRankFactor e d τ) :
    ‖L (rankFactor e d)‖ ^ 2
      ≤ (q : ℝ) * hsNormSq (rankFactor e d)
        + (1 / (q : ℝ)) * Complex.normSq (rankFactor e d).trace := by
  have h := balancedPolarization_rankFactor_le hq hOne hCross hbal
  have htrace : (rankFactor e d).trace = (q : ℂ) * τ := by
    rw [contraction_trace]
    simp_rw [hbal.2]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hscalar :
      (1 / (q : ℝ)) * ((q : ℝ) * (q : ℝ) * Complex.normSq τ)
        = (q : ℝ) * Complex.normSq τ := by
    field_simp
  rw [htrace, Complex.normSq_mul, Complex.normSq_natCast]
  rw [hscalar]
  exact h

end Lift

section MatrixLift

variable {W E : Type*} [Fintype W]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {L : Matrix W W ℂ →ₗ[ℂ] E}

/-- The balanced-polarization lift at the exact matrix rank. -/
theorem balancedPolarization_exact
    (C : Matrix W W ℂ) (hC : C ≠ 0)
    (hOne : HasRankOneTraceBound L)
    (hCross : HasCrossedPolarization L) :
    ‖L C‖ ^ 2
      ≤ (C.rank : ℝ) * hsNormSq C
        + (1 / (C.rank : ℝ)) * Complex.normSq C.trace := by
  obtain ⟨e, d, τ, hfac, hbal⟩ := hasBalancedRankFactorization C
  have h := balancedPolarization_rankFactor_trace_le
    (rank_pos_of_ne_zero hC) hOne hCross hbal
  rwa [← hfac] at h

/-- The balanced-polarization lift at any upper bound on the matrix rank. -/
theorem balancedPolarization
    (C : Matrix W W ℂ)
    (hOne : HasRankOneTraceBound L)
    (hCross : HasCrossedPolarization L)
    (r : ℕ) (hrank : C.rank ≤ r) :
    ‖L C‖ ^ 2
      ≤ (r : ℝ) * hsNormSq C
        + (1 / (r : ℝ)) * Complex.normSq C.trace := by
  rcases eq_or_ne C 0 with rfl | hC
  · simp [hsNormSq]
  · exact (balancedPolarization_exact C hC hOne hCross).trans
      (rank_mono (Complex.normSq_nonneg _) (rank_pos_of_ne_zero hC)
        hrank (normSq_trace_le_rank C))

end MatrixLift

end RankR
