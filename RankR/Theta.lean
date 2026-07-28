/-
The amplified map `Θ^Φ_{R,λ}` and its positivity threshold.

`paper/derivation-graph-inclusion.tex` studies

    Θ^Φ_{R,λ} = Φ ∘ τ + λ (Δ_d - id/R),        Δ_d(X) = Tr(X) I,

and its threshold `λ*_R(Φ) = inf {λ ≥ 0 : Θ^Φ_{R,λ} is R-positive}`.  Pair
amplification says `λ*_R(Φ) ≤ (R-1)β₂(Φ)`; `thm:clique` of that manuscript says
the bound is attained, and identifies the general obstruction as the maximum
induced average degree.

`R`-positivity is taken in its Choi form throughout: `Ψ` is `R`-positive when
`⟪vec C, J(Ψ) vec C⟫ ≥ 0` for every `C` of rank at most `R`.  Rather than build
`J(Θ)` as a matrix, the three terms are unrolled the way `ChoiTwoBound` unrolls
its rank hypothesis.  In that normalization `Δ_d` contributes `‖C‖₂²` and `id`
contributes `|Tr C|²`, and a computation with the Choi convention of
`Conventions.lean` gives the first term as

    ⟪vec C, J(Φ_A ∘ τ) vec C⟫ = ∑_a ⟪A_a C, (A_a C)ᵀ⟫,

the Hilbert-Schmidt pairing of each `A_a C` against its own transpose --- a
signed measure of how far `A_a C` is from antisymmetric.  That reading is what
makes the graph computation immediate: for a skew `L_e` and the diagonal
projection `P_S`, the product `L_e P_S` pairs against its transpose to `-2`
exactly when both endpoints of `e` lie in `S`.

`thetaPositive_mono` records that the condition is monotone in `λ` --- via the
trace-rank bound `|Tr C|² ≤ R‖C‖₂²`, which is what makes the correction term
nonnegative --- so `λ*` is a genuine threshold and, as with `ChoiTwoBound`, the
condition alone names no number.  `Sharp.lean` supplies the pattern for pinning
it: a witness attaining the bound.

The obstruction is `two_mul_card_le_of_thetaPositive`, and the clique reading is
`sub_one_le_lam_of_clique`.  Both run on the extremizer of `Optimal.lean`: the
witness `C = P_S ⊗ E_{01}` of `thm:clique` is `projWit S 0 1`, so its rank,
Hilbert-Schmidt norm and trace are already known.
-/
import RankR.GraphFamily

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

/-! ## The Choi pairing of `Φ ∘ τ` -/

section Theta

variable {W : Type*} [Fintype W] [DecidableEq W] {ι : Type*} [Fintype ι]

/-- `⟪vec C, J(Φ_A ∘ τ) vec C⟫`, the Choi pairing of the transposed Kraus sum. -/
noncomputable def thetaPair (A : ι → Matrix W W ℂ) (C : Matrix W W ℂ) : ℂ :=
  ∑ a, hsInner (A a * C) ((A a * C)ᵀ)

/-- **`R`-positivity of `Θ^Φ_{R,λ}`**, in Choi form and with each term unrolled.

`Δ_d` contributes `‖C‖₂²` and `id` contributes `|Tr C|²`, so the correction is
`λ(‖C‖₂² - |Tr C|²/R)`. -/
def ThetaPositive (A : ι → Matrix W W ℂ) (R : ℕ) (lam : ℝ) : Prop :=
  ∀ C : Matrix W W ℂ, C.rank ≤ R →
    0 ≤ (thetaPair A C).re + lam * (hsNormSq C - Complex.normSq C.trace / R)

/-- The correction term is nonnegative at rank `R`, by the trace-rank bound. -/
theorem correction_nonneg {C : Matrix W W ℂ} {R : ℕ} (hR : 0 < R) (hrank : C.rank ≤ R) :
    0 ≤ hsNormSq C - Complex.normSq C.trace / R := by
  have htr : Complex.normSq C.trace ≤ (C.rank : ℝ) * hsNormSq C := normSq_trace_le_rank C
  have hRr : (C.rank : ℝ) ≤ R := by exact_mod_cast hrank
  have hn : (0 : ℝ) ≤ hsNormSq C := hsNormSq_nonneg C
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  rw [sub_nonneg, div_le_iff₀ hRpos]
  nlinarith

/-- **`ThetaPositive` is monotone in `λ`.**  As with `choiTwoBound_mono`, this is
why the condition alone determines no number: the threshold needs a witness at
the other end. -/
theorem thetaPositive_mono {A : ι → Matrix W W ℂ} {R : ℕ} (hR : 0 < R) {lam lam' : ℝ}
    (h : ThetaPositive A R lam) (hle : lam ≤ lam') : ThetaPositive A R lam' := by
  intro C hrank
  have hc := correction_nonneg (C := C) hR hrank
  have := h C hrank
  nlinarith

end Theta

/-! ## Two missing pieces of `hsInner` bilinearity -/

section Bilinear

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `hsInner` is homogeneous in its second argument. -/
theorem hsInner_smul_right' (c : ℂ) (A B : Matrix m n ℂ) :
    hsInner A (c • B) = c * hsInner A B := by
  simp [hsInner, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- The two signs of a pairing of negatives cancel. -/
theorem hsInner_neg_neg (A B : Matrix m n ℂ) : hsInner (-A) (-B) = hsInner A B := by
  simp [hsInner]

end Bilinear

/-! ## The diagonal projection, and the witness as a Kronecker product -/

section ProjS

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `P_S = ∑_{i ∈ S} E_{ii}`, the diagonal projection onto a set of coordinates. -/
def projS (S : Finset U) : Matrix U U ℂ :=
  Matrix.diagonal fun i => if i ∈ S then 1 else 0

/-- Right multiplication by `P_S` keeps a matrix unit exactly when its column
index lies in `S`. -/
theorem single_mul_projS (S : Finset U) (i j : U) :
    Matrix.single i j (1 : ℂ) * projS S
      = (if j ∈ S then (1 : ℂ) else 0) • Matrix.single i j 1 := by
  ext p q
  rw [projS, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases hq : q = j
  · subst hq; ring
  · simp [Ne.symm hq]

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype U] [Fintype V] in
/-- **The extremizer of `Optimal.lean` is `P_S ⊗ E_{x₀x₁}`**, which is the
witness `C = P_S ⊗ E_{01}` of `thm:clique`. -/
theorem projWit_eq_kron (S : Finset U) (x₀ x₁ : V) :
    projWit S x₀ x₁ = projS S ⊗ₖ Matrix.single x₀ x₁ (1 : ℂ) := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  rw [projWit_apply, Matrix.kroneckerMap_apply, projS, Matrix.diagonal_apply,
    Matrix.single_apply]
  by_cases h1 : p1 = q1
  · subst h1
    by_cases h4 : p1 ∈ S
    · by_cases h2 : p2 = x₀
      · subst h2
        by_cases h3 : q2 = x₁
        · subst h3; simp [h4]
        · simp [h4, h3, Ne.symm h3]
      · simp [h4, h2, Ne.symm h2]
    · simp [h4, ite_and]
  · simp [h1, ite_and]

end ProjS

/-! ## The obstruction -/

section Obstruction

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- The qubit factor of the witness collapses: `(E_{01} - E_{10}) E_{01} = -E_{11}`. -/
theorem skewUnit_mul_single_qubit :
    skewUnit (0 : Fin 2) 1 * Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
      = -Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) := by
  rw [skewUnit, Matrix.sub_mul]
  simp

omit [LinearOrder U] in
/-- The pairing of a two-term combination of transposed matrix units against its
own transpose.  The diagonal terms vanish and the two cross terms survive. -/
private theorem hsInner_pair_single {i j : U} (hne : i ≠ j) (a b : ℂ) :
    hsInner (a • Matrix.single i j (1 : ℂ) - b • Matrix.single j i 1)
        (a • Matrix.single j i (1 : ℂ) - b • Matrix.single i j 1)
      = -(conj a * b) - conj b * a := by
  simp only [hsInner_sub_left, hsInner_sub_right, hsInner_smul_left, hsInner_smul_right',
    hsInner_single, if_neg hne, if_neg (Ne.symm hne), if_true, mul_one]
  ring

/-- **One edge's contribution.**  The Hilbert-Schmidt pairing of `A_e C` against
its transpose is `-2` when both endpoints of `e` lie in `S`, and `0` otherwise.

This is the whole of `thm:clique`'s computation.  Right multiplication by `P_S`
retains the matrix unit `E_{ij}` of `L_e` only when `j ∈ S`, so the surviving
combination is `[j ∈ S] E_{ij} - [i ∈ S] E_{ji}`; pairing it against its own
transpose kills both diagonal terms and leaves two cross terms, each carrying
both memberships. -/
theorem hsInner_edgeKraus_mul_projWit {p : U × U} (hp : p.1 < p.2) (S : Finset U) :
    hsInner (edgeKraus p * projWit S (0 : Fin 2) 1)
        ((edgeKraus p * projWit S (0 : Fin 2) 1)ᵀ)
      = if p.1 ∈ S ∧ p.2 ∈ S then -2 else 0 := by
  have hne : p.1 ≠ p.2 := ne_of_lt hp
  have hU : skewUnit p.1 p.2 * projS S
      = (if p.2 ∈ S then (1 : ℂ) else 0) • Matrix.single p.1 p.2 1
        - (if p.1 ∈ S then (1 : ℂ) else 0) • Matrix.single p.2 p.1 1 := by
    rw [skewUnit, Matrix.sub_mul, single_mul_projS, single_mul_projS]
  have hmul : edgeKraus p * projWit S (0 : Fin 2) 1
      = ((if p.2 ∈ S then (1 : ℂ) else 0) • Matrix.single p.1 p.2 1
          - (if p.1 ∈ S then (1 : ℂ) else 0) • Matrix.single p.2 p.1 1)
          ⊗ₖ (-Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)) := by
    rw [edgeKraus, projWit_eq_kron, ← Matrix.mul_kronecker_mul, hU]
    congr 1
    exact skewUnit_mul_single_qubit
  have htr : (((if p.2 ∈ S then (1 : ℂ) else 0) • Matrix.single p.1 p.2 1
        - (if p.1 ∈ S then (1 : ℂ) else 0) • Matrix.single p.2 p.1 1)
        ⊗ₖ (-Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)))ᵀ
      = ((if p.2 ∈ S then (1 : ℂ) else 0) • Matrix.single p.2 p.1 1
          - (if p.1 ∈ S then (1 : ℂ) else 0) • Matrix.single p.1 p.2 1)
          ⊗ₖ (-Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)) := by
    rw [← Matrix.kroneckerMap_transpose]
    congr 1
    · rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul,
        Matrix.transpose_single, Matrix.transpose_single]
    · rw [Matrix.transpose_neg, Matrix.transpose_single]
  have hqubit : hsInner (-Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ))
      (-Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)) = 1 := by
    rw [hsInner_neg_neg, hsInner_single]
    norm_num
  rw [hmul, htr, hsInner_kron, hqubit, mul_one, hsInner_pair_single hne]
  by_cases h1 : p.1 ∈ S <;> by_cases h2 : p.2 ∈ S <;> simp only [h1, h2, and_true,
    and_false, if_true, if_false, map_one, map_zero] <;> ring


end Obstruction

/-! ## Counting the pairs of a clique -/

section Counting

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

omit [Fintype U] in
/-- **The ordered pairs of a finite set, counted by trichotomy.**  The two strict
orders are exchanged by the swap and the diagonal has `S.card` points, so twice
the number of increasing pairs is `|S|² - |S|`. -/
theorem two_mul_card_ltPairs (S : Finset U) :
    2 * ((S ×ˢ S).filter (fun p : U × U => p.1 < p.2)).card + S.card
      = S.card * S.card := by
  have hswap : ∀ f : U → U → ℕ, ∑ p ∈ S ×ˢ S, f p.2 p.1 = ∑ p ∈ S ×ˢ S, f p.1 p.2 := by
    intro f
    rw [Finset.sum_product, Finset.sum_product]
    exact Finset.sum_comm
  have hlt : ((S ×ˢ S).filter (fun p : U × U => p.1 < p.2)).card
      = ∑ p ∈ S ×ˢ S, if p.1 < p.2 then 1 else 0 := Finset.card_filter _ _
  have hgt : (∑ p ∈ S ×ˢ S, if p.2 < p.1 then (1 : ℕ) else 0)
      = ∑ p ∈ S ×ˢ S, if p.1 < p.2 then 1 else 0 :=
    hswap (fun a b => if a < b then 1 else 0)
  have hdiag : (∑ p ∈ S ×ˢ S, if p.1 = p.2 then (1 : ℕ) else 0) = S.card := by
    rw [Finset.sum_product]
    have h : ∀ i ∈ S, (∑ y ∈ S, if i = y then (1 : ℕ) else 0) = 1 := by
      intro i hi
      rw [Finset.sum_ite_eq S i (fun _ => (1 : ℕ)), if_pos hi]
    rw [Finset.sum_congr rfl h]
    simp
  have htotal : (∑ p ∈ S ×ˢ S, ((if p.1 < p.2 then (1 : ℕ) else 0)
      + (if p.2 < p.1 then 1 else 0) + (if p.1 = p.2 then 1 else 0)))
      = S.card * S.card := by
    have h1 : ∀ p ∈ S ×ˢ S, ((if p.1 < p.2 then (1 : ℕ) else 0)
        + (if p.2 < p.1 then 1 else 0) + (if p.1 = p.2 then 1 else 0)) = 1 := by
      intro p _
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · simp [h, asymm h, ne_of_lt h]
      · simp [h]
      · simp [h, asymm h, Ne.symm (ne_of_lt h)]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_product, smul_eq_mul, mul_one]
  rw [hlt, ← htotal, Finset.sum_add_distrib, Finset.sum_add_distrib, hgt, hdiag]
  ring

omit [Fintype U] in
/-- A clique contributes all of its increasing pairs to the edge set. -/
theorem card_ltPairs_le_of_clique {E : Finset (U × U)} {S : Finset U}
    (hcl : ∀ i ∈ S, ∀ j ∈ S, i < j → (i, j) ∈ E) :
    ((S ×ˢ S).filter (fun p : U × U => p.1 < p.2)).card
      ≤ (E.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card := by
  refine Finset.card_le_card fun p hp => ?_
  rw [Finset.mem_filter, Finset.mem_product] at hp
  rw [Finset.mem_filter]
  exact ⟨by simpa using hcl p.1 hp.1.1 p.2 hp.1.2 hp.2, hp.1.1, hp.1.2⟩

end Counting

/-! ## The obstruction, and the clique reading -/

section Avgdeg

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- The Choi pairing of `Φ_G ∘ τ` at the witness `P_S ⊗ E_{01}` counts the edges
of the induced subgraph `G[S]`, each with weight `-2`. -/
theorem thetaPair_graphKraus_projWit {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    (S : Finset U) :
    thetaPair (graphKraus E) (projWit S (0 : Fin 2) 1)
      = -2 * ((E.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card : ℂ) := by
  have hterm : ∀ e : {p : U × U // p ∈ E},
      hsInner (graphKraus E e * projWit S (0 : Fin 2) 1)
          ((graphKraus E e * projWit S (0 : Fin 2) 1)ᵀ)
        = if e.val.1 ∈ S ∧ e.val.2 ∈ S then -2 else 0 := fun e =>
    hsInner_edgeKraus_mul_projWit (hE e.val e.property) S
  rw [thetaPair, Finset.sum_congr rfl fun e _ => hterm e,
    Finset.sum_coe_sort E (fun p => if p.1 ∈ S ∧ p.2 ∈ S then (-2 : ℂ) else 0),
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The induced-average-degree obstruction** (`eq:avgdeg`).

If `Θ^{Φ_G}_{R,λ}` is `R`-positive then `λ ≥ 2|E(G[S])|/|S|` for every `S` of at
most `R` vertices, in the cleared form `2|E(G[S])| ≤ λ|S|`.

The witness is `projWit S 0 1`, which is `P_S ⊗ E_{01}`: its rank is `|S|`, its
squared Hilbert-Schmidt norm is `|S|`, and its trace vanishes because the two
qubit labels differ, so the correction term contributes exactly `λ|S|` and the
protected `1/R` never enters. -/
theorem two_mul_card_le_of_thetaPositive {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {R : ℕ} {lam : ℝ} (h : ThetaPositive (graphKraus E) R lam)
    {S : Finset U} (hS : S.card ≤ R) :
    2 * ((E.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card : ℝ) ≤ lam * S.card := by
  have hrank : (projWit S (0 : Fin 2) 1).rank ≤ R := by
    rw [rank_projWit]; exact hS
  have hkey := h _ hrank
  rw [thetaPair_graphKraus_projWit hE S, hsNormSq_projWit, trace_projWit,
    if_neg (by decide : ¬ (0 : Fin 2) = 1)] at hkey
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re,
    Complex.natCast_im, Complex.neg_re, Complex.neg_im, map_zero,
    zero_div, sub_zero, mul_zero, neg_zero] at hkey
  linarith

/-- **Clique sharpness** (`thm:clique`, lower half): an `R`-clique forces
`λ ≥ R - 1`.

Every increasing pair inside the clique is an edge, and
`two_mul_card_ltPairs` counts those pairs, so the obstruction reads
`R(R-1) ≤ λR`. -/
theorem sub_one_le_lam_of_clique {E : Finset (U × U)} (hE : ∀ p ∈ E, p.1 < p.2)
    {R : ℕ} (hR : 0 < R) {lam : ℝ} (h : ThetaPositive (graphKraus E) R lam)
    {S : Finset U} (hSR : S.card = R)
    (hcl : ∀ i ∈ S, ∀ j ∈ S, i < j → (i, j) ∈ E) :
    (R : ℝ) - 1 ≤ lam := by
  have hobs := two_mul_card_le_of_thetaPositive hE h (S := S) (le_of_eq hSR)
  have hcount : R * R
      ≤ 2 * (E.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card + R := by
    calc R * R = 2 * ((S ×ˢ S).filter (fun p : U × U => p.1 < p.2)).card + S.card := by
          rw [two_mul_card_ltPairs S, hSR]
      _ ≤ 2 * (E.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card + R := by
          rw [hSR]
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_left 2 (card_ltPairs_le_of_clique hcl)) R
  have hcount' : (R : ℝ) * R
      ≤ 2 * ((E.filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card : ℝ) + R := by
    exact_mod_cast hcount
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  rw [hSR] at hobs
  have : (R : ℝ) * R ≤ lam * R + R := by linarith
  nlinarith

end Avgdeg

end RankR
