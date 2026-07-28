/-
Lifting II: from the rank-two Choi bound of a Kraus family to the operator
inequality on the negative sector.

Fix a family `A : ι → L(U ⊗ V)` and let `Φ_A` be the Kraus sum it generates,
acting trivially on the ancilla `Q = ℂ^s`.  Two hypotheses drive everything:

* `ChoiTwoBound (choiOf A) β` — the rank-two bound on the Choi operator, which
  `Choi.lean` turns into the edgewise estimate `‖K ēᵢ‖² + ‖K ēⱼ‖² ≤ 2β‖c‖²` for
  every `K` in the span of the family;
* `(A f)ᵀ = A f` — transpose symmetry of the Kraus operators, which makes every
  frame vector orthogonal to `δ_e` and so produces the trace correction.

The frame vectors are the images `(A_f ⊗ I_Q) ζ_{ij}` of the antisymmetric
combinations, one per Kraus index and edge.  Synthesizing them with coefficients
`c` gives `T` for the edge data `K_{ij} = ∑_f c_{f,ij} A_f`, so the vertex
regrouping of `Synth.lean` contributes `s − 1` and the edgewise estimate
contributes `2β`.  Bessel duality turns that synthesis bound into the analysis
bound, sharpened on the orthogonal complement of `δ_e`:

  (A)   `⟪y, Φ_A(P₋) y⟫ ≤ 2β(s−1)(‖y‖² − |⟪δ_e, y⟫|²/s)`

which is `eq:Phi-Pminus-goal` with `β` in place of the double-skew `1`.  Since
`Ppos − Pneg` is twice the partial transpose and Kraus sums preserve positivity,
(A) gives the two-sided form

  (B)   `⟪y, Φ_A(ρ₀^{T_UV}) y⟫ + β(s−1)(‖y‖² − |⟪δ_e, y⟫|²/s) ≥ 0`.

Here `s` is the rank parameter `r`, `s − 1` the degree of the frame, and the
`1/s` inside the projection term the protected direction `δ_e`.
-/
import RankR.Bessel
import RankR.Choi
import RankR.Edge
import RankR.Frame
import RankR.Restrict

namespace RankR

open Matrix Finset ComplexConjugate

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  {ι : Type*} [Fintype ι] {s : ℕ}

/-! ## The amplified map and its frame -/

/-- `Φ_A ⊗ id_Q`: the Kraus sum of a family on `U ⊗ V`, acting trivially on the
ancilla. -/
noncomputable def krausQ (A : ι → Matrix (U × V) (U × V) ℂ)
    (Y : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ) :
    Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ :=
  krausSum (fun f => placeQ (A f)) Y

omit [DecidableEq U] [DecidableEq V] in
/-- A Kraus sum preserves positive semidefiniteness. -/
theorem qform_krausQ_nonneg (A : ι → Matrix (U × V) (U × V) ℂ)
    {Y : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ}
    (hY : ∀ z : EuclideanSpace ℂ ((U × V) × Fin s), 0 ≤ (qform Y z).re)
    (x : EuclideanSpace ℂ ((U × V) × Fin s)) : 0 ≤ (qform (krausQ A Y) x).re :=
  qform_krausSum_nonneg _ hY x

omit [DecidableEq U] [DecidableEq V] in
theorem krausQ_sub (A : ι → Matrix (U × V) (U × V) ℂ)
    (Y Z : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ) :
    krausQ A (Y - Z) = krausQ A Y - krausQ A Z := by
  simp only [krausQ, krausSum, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq U] [DecidableEq V] in
theorem krausQ_smul (A : ι → Matrix (U × V) (U × V) ℂ) (t : ℂ)
    (Y : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ) :
    krausQ A (t • Y) = t • krausQ A Y := by
  simp only [krausQ, krausSum, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]

/-- The frame vectors: the images of the `ζ_p` under the Kraus operators,
extended by zero off the edge set `p.1 < p.2`. -/
noncomputable def wvec (A : ι → Matrix (U × V) (U × V) ℂ)
    (e : Fin s → EuclideanSpace ℂ (U × V)) (f : ι) (p : Fin s × Fin s) :
    EuclideanSpace ℂ ((U × V) × Fin s) :=
  if p.1 < p.2 then mulVecE (placeQ (A f)) (zetaV e p.1 p.2) else 0

omit [DecidableEq U] [DecidableEq V] in
/-- The quadratic form of `Φ_A(P₋)` is the total squared overlap with the frame.

Expanding the Kraus sum and then the rank-one sum defining `Pneg`, and moving the
Kraus operator across the inner product, exhibits it as a Bessel sum; the
synthesis bound below is then usable without ever forming the synthesis map as a
matrix. -/
theorem qform_krausQ_Pneg (A : ι → Matrix (U × V) (U × V) ℂ)
    (e : Fin s → EuclideanSpace ℂ (U × V)) (y : EuclideanSpace ℂ ((U × V) × Fin s)) :
    qform (krausQ A (Pneg e)) y
      = ∑ f : ι, ∑ p : Fin s × Fin s,
          ((Complex.normSq (inner ℂ (wvec A e f p) y) : ℝ) : ℂ) := by
  rw [krausQ, qform_krausSum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [qform_Pneg_eq, Edges_def, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p.1 < p.2
  · simp only [h, if_true, wvec]
    rw [inner_mulVecE_left, Matrix.conjTranspose_conjTranspose]
  · simp [h, wvec]

/-! ## Synthesis -/

/-- The edge matrix carried by the ordered pair `(i, j)`: the member of the Kraus
span whose coefficients are `c` restricted to that pair. -/
noncomputable def Kof (A : ι → Matrix (U × V) (U × V) ℂ)
    (c : ι × (Fin s × Fin s) → ℂ) (i j : Fin s) : Matrix (U × V) (U × V) ℂ :=
  ∑ f, c (f, (i, j)) • A f

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
/-- Contracting the Kraus operators against the coefficients of a single ordered
pair produces the placed edge matrix. -/
theorem sum_smul_placeQ (A : ι → Matrix (U × V) (U × V) ℂ)
    (c : ι × (Fin s × Fin s) → ℂ) (p : Fin s × Fin s) :
    ∑ f : ι, c (f, p) • placeQ (s := s) (A f) = placeQ (Kof A c p.1 p.2) := by
  rw [Kof, placeQ_sum]
  exact Finset.sum_congr rfl fun f _ => by rw [placeQ_smul]

omit [DecidableEq U] [DecidableEq V] in
/-- Synthesizing the frame with coefficients `c` produces exactly the vector `T`
of the edge data `Kof A c`: summing over the Kraus index first assembles the
member of the span, and the vanishing of `wvec` off the edge set restricts the
remaining sum to the edges. -/
theorem sum_smul_wvec (A : ι → Matrix (U × V) (U × V) ℂ)
    (e : Fin s → EuclideanSpace ℂ (U × V)) (c : ι × (Fin s × Fin s) → ℂ) :
    ∑ k : ι × (Fin s × Fin s), c k • wvec A e k.1 k.2 = Tsyn e (Kof A c) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Tsyn, Edges_def, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p.1 < p.2
  · simp only [wvec, h, if_true]
    rw [← sum_smul_placeQ A c p, mulVecE_sum]
    exact Finset.sum_congr rfl fun f _ => (mulVecE_smul _ _ _).symm
  · simp [wvec, h]

omit [DecidableEq U] [DecidableEq V] in
/-- **The uniform synthesis bound.**

`Synth.lean` regroups the synthesized vector by vertex, at a cost of `s − 1`;
Lifting I bounds each edge's contribution by `2β` times the squared coefficient
mass carried by that edge.  When `s < 2` there are no edges and both sides
vanish. -/
theorem norm_sum_smul_wvec_le {A : ι → Matrix (U × V) (U × V) ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β)
    {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (c : ι × (Fin s × Fin s) → ℂ) :
    ‖∑ k : ι × (Fin s × Fin s), c k • wvec A e k.1 k.2‖ ^ 2
      ≤ 2 * β * ((s : ℝ) - 1) * ∑ k : ι × (Fin s × Fin s), Complex.normSq (c k) := by
  rw [sum_smul_wvec]
  have hb := orthonormal_ebar he
  rcases Nat.lt_or_ge s 2 with hs | hs
  · have hE : (Edges : Finset (Fin s × Fin s)) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      have h1 : (p.1 : ℕ) < (p.2 : ℕ) := mem_Edges.1 hp
      have h2 : (p.2 : ℕ) < s := p.2.isLt
      omega
    have hT : Tsyn e (Kof A c) = 0 := by rw [Tsyn, hE, Finset.sum_empty]
    rw [hT, norm_zero]
    have hz : s = 0 ∨ s = 1 := by omega
    have hnn : (0 : ℝ) ≤ ∑ k : ι × (Fin s × Fin s), Complex.normSq (c k) :=
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    rcases hz with rfl | rfl
    · simp
    · norm_num
  · have hs1 : (0 : ℝ) ≤ (s : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      linarith
    have hsum : ∑ k : ι × (Fin s × Fin s), Complex.normSq (c k)
        = ∑ p : Fin s × Fin s, ∑ f : ι, Complex.normSq (c (f, p)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc ‖Tsyn e (Kof A c)‖ ^ 2
        ≤ ((s : ℝ) - 1) * ∑ p ∈ Edges, (‖mulVecE (Kof A c p.1 p.2) (ebar e p.1)‖ ^ 2
            + ‖mulVecE (Kof A c p.1 p.2) (ebar e p.2)‖ ^ 2) := norm_Tsyn_sq_le e (Kof A c)
      _ ≤ ((s : ℝ) - 1) * ∑ p ∈ Edges, 2 * β * ∑ f : ι, Complex.normSq (c (f, p)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp => ?_) hs1
          have hne : p.1 ≠ p.2 := ne_of_lt (mem_Edges.1 hp)
          have h := norm_sq_pair_le_of_choiTwoBound hβ hJ (fun f => c (f, p))
            (hb.1 p.1) (hb.1 p.2) (hb.2 hne)
          simpa [Kof, Prod.mk.eta] using h
      _ ≤ ((s : ℝ) - 1) * ∑ p : Fin s × Fin s, 2 * β * ∑ f : ι,
            Complex.normSq (c (f, p)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) fun p _ _ => ?_) hs1
          have hnn : (0 : ℝ) ≤ ∑ f : ι, Complex.normSq (c (f, p)) :=
            Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
          positivity
      _ = 2 * β * ((s : ℝ) - 1) * ∑ k : ι × (Fin s × Fin s), Complex.normSq (c k) := by
          rw [hsum, ← Finset.mul_sum]
          ring

/-! ## Orthogonality to the protected direction -/

omit [DecidableEq U] [DecidableEq V] [Fintype ι] in
/-- Transpose symmetry of the Kraus operators makes every frame vector orthogonal
to `δ_e`.

This is `eq:T-orthogonal`.  For an odd number of skew factors the Kraus
operators are antisymmetric instead, the orthogonality fails, and the `1/s`
correction below is lost; parity is what protects the dark state. -/
theorem inner_delta_wvec {A : ι → Matrix (U × V) (U × V) ℂ} (hsym : ∀ f, (A f)ᵀ = A f)
    (e : Fin s → EuclideanSpace ℂ (U × V)) (f : ι) (p : Fin s × Fin s) :
    inner ℂ (delta e) (wvec A e f p) = 0 := by
  rw [wvec]
  split
  · exact inner_delta_placeQ_zetaV e (hsym f) _ _
  · simp

/-! ## Lifting II -/

omit [DecidableEq U] [DecidableEq V] in
/-- **Lifting II, form (A)**: `(Φ_A ⊗ id)(P₋) ⪯ 2β(s−1)(I − Π_E)`.

Bessel duality converts the synthesis bound into the analysis bound, and the
orthogonality of the frame to `δ_e` sharpens it on the orthogonal complement of
that vector.  At `β = 1` this is `eq:Phi-Pminus-goal`. -/
theorem qform_krausQ_Pneg_le {A : ι → Matrix (U × V) (U × V) ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β) (hsym : ∀ f, (A f)ᵀ = A f) (hs : 0 < s)
    {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (y : EuclideanSpace ℂ ((U × V) × Fin s)) :
    (qform (krausQ A (Pneg e)) y).re
      ≤ 2 * β * ((s : ℝ) - 1) * (‖y‖ ^ 2 - Complex.normSq (inner ℂ (delta e) y) / s) := by
  have hM : (0 : ℝ) ≤ 2 * β * ((s : ℝ) - 1) := by
    have h1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have : (0 : ℝ) ≤ (s : ℝ) - 1 := by linarith
    positivity
  have hbess := frame_le_of_synthesis_le (fun k : ι × (Fin s × Fin s) => wvec A e k.1 k.2)
    hM (norm_sum_smul_wvec_le hβ hJ he)
  have hsr : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hsharp := frame_le_sub_proj (w := fun k : ι × (Fin s × Fin s) => wvec A e k.1 k.2)
    (z := delta e) hsr (norm_delta_orthonormal he)
    (fun k => inner_delta_wvec hsym e k.1 k.2) hbess y
  have hre : (qform (krausQ A (Pneg e)) y).re
      = ∑ k : ι × (Fin s × Fin s), Complex.normSq (inner ℂ (wvec A e k.1 k.2) y) := by
    rw [qform_krausQ_Pneg, Complex.re_sum]
    conv_rhs => rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun f _ => by
      rw [Complex.re_sum]
      exact Finset.sum_congr rfl fun p _ => Complex.ofReal_re _
  rw [hre]
  exact hsharp

omit [DecidableEq U] [DecidableEq V] in
/-- **Lifting II, form (B)**: `(Φ_A ⊗ id)(ρ_E^{T_H}) + β(s−1)(I − Π_E) ⪰ 0`.

The partial transpose is half the difference of the two sector operators, the
positive sector survives the Kraus sum, and the negative sector is controlled by
form (A).  At `β = 1` this is `prop:operator_ineq`. -/
theorem qform_krausQ_ptransposeUV_ge {A : ι → Matrix (U × V) (U × V) ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β) (hsym : ∀ f, (A f)ᵀ = A f) (hs : 0 < s)
    {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (y : EuclideanSpace ℂ ((U × V) × Fin s)) :
    0 ≤ (qform (krausQ A (ptransposeUV (rankOne (delta e) (delta e)))) y).re
        + β * ((s : ℝ) - 1) * (‖y‖ ^ 2 - Complex.normSq (inner ℂ (delta e) y) / s) := by
  have hpos : (0 : ℝ) ≤ (qform (krausQ A (Ppos e)) y).re :=
    qform_krausQ_nonneg A (fun z => qform_Ppos_nonneg e z) y
  have hneg := qform_krausQ_Pneg_le hβ hJ hsym hs he y
  have hsplit : (2 : ℝ) * (qform (krausQ A (ptransposeUV (rankOne (delta e) (delta e)))) y).re
      = (qform (krausQ A (Ppos e)) y).re - (qform (krausQ A (Pneg e)) y).re := by
    have h : krausQ A (Ppos e) - krausQ A (Pneg e)
        = (2 : ℂ) • krausQ A (ptransposeUV (rankOne (delta e) (delta e))) := by
      rw [← krausQ_sub, Ppos_sub_Pneg, krausQ_smul]
    have h2 := congrArg (fun M => (qform M y).re) h
    simp only [qform_sub, qform_smul, Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero] at h2
    linarith
  linarith

end RankR
