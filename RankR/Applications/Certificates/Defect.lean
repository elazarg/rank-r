/-
The exact complete-graph variance identity behind the synthesis estimate.
-/
import RankR.Applications.Certificates.Gram

namespace RankR

open Matrix Finset ComplexConjugate

section Variance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {s : ℕ}

/-- The ordered-pair form of the finite Hilbert-space variance identity. -/
theorem sum_sum_norm_sub_sq (v : Fin s → E) :
    ∑ i, ∑ j, ‖v i - v j‖ ^ 2
      = 2 * (s : ℝ) * ∑ i, ‖v i‖ ^ 2 - 2 * ‖∑ i, v i‖ ^ 2 := by
  have hleft : ∑ i, ∑ _j : Fin s, ‖v i‖ ^ 2 = (s : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hright : ∑ _i : Fin s, ∑ j, ‖v j‖ ^ 2 = (s : ℝ) * ∑ j, ‖v j‖ ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hinner : ∑ i, ∑ j, (inner ℂ (v i) (v j)).re = ‖∑ i, v i‖ ^ 2 := by
    calc
      _ = (∑ i, ∑ j, inner ℂ (v i) (v j)).re := by
        simp only [Complex.re_sum]
      _ = (inner ℂ (∑ i, v i) (∑ j, v j)).re := by
        congr 1
        simp only [sum_inner, inner_sum]
        rw [Finset.sum_comm]
      _ = _ := (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have htwo : ∑ i, ∑ j, 2 * (inner ℂ (v i) (v j)).re
      = 2 * ‖∑ i, v i‖ ^ 2 := by
    simpa only [Finset.mul_sum] using congrArg (fun x : ℝ => 2 * x) hinner
  simp_rw [norm_sub_sq (𝕜 := ℂ)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hleft, hright]
  change (s : ℝ) * ∑ i, ‖v i‖ ^ 2
      - (∑ i, ∑ j, 2 * (inner ℂ (v i) (v j)).re)
      + (s : ℝ) * ∑ j, ‖v j‖ ^ 2
    = 2 * (s : ℝ) * ∑ i, ‖v i‖ ^ 2 - 2 * ‖∑ i, v i‖ ^ 2
  rw [htwo]
  ring

omit [InnerProductSpace ℂ E] in
/-- Summing squared differences over ordered pairs counts each complete-graph
edge twice. -/
theorem sum_sum_norm_sub_sq_eq_two_mul_edges (v : Fin s → E) :
    ∑ i, ∑ j, ‖v i - v j‖ ^ 2
      = 2 * ∑ p ∈ Edges, ‖v p.1 - v p.2‖ ^ 2 := by
  rw [← sum_split_lt (fun i j => ‖v i - v j‖ ^ 2), Edges_def]
  simp only [sub_self, norm_zero, zero_pow two_ne_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by
    rw [norm_sub_rev]
    ring

/-- The complete-graph variance identity. -/
theorem completeGraph_variance (v : Fin s → E) :
    (s : ℝ) * ∑ i, ‖v i‖ ^ 2 - ‖∑ i, v i‖ ^ 2
      = ∑ p ∈ Edges, ‖v p.1 - v p.2‖ ^ 2 := by
  have hordered := sum_sum_norm_sub_sq v
  have hedges := sum_sum_norm_sub_sq_eq_two_mul_edges v
  linarith

end Variance

section VertexVariance

variable {W : Type*} [Fintype W] {s : ℕ}

/-- Pairs of vertices different from `k`; these index the unordered pairs of
edges incident to `k`. -/
def OtherEdges (k : Fin s) : Finset (Fin s × Fin s) :=
  Edges.filter fun p => p.1 ≠ k ∧ p.2 ≠ k

@[simp] theorem mem_OtherEdges {k : Fin s} {p : Fin s × Fin s} :
    p ∈ OtherEdges k ↔ p.1 < p.2 ∧ p.1 ≠ k ∧ p.2 ≠ k := by
  simp [OtherEdges, mem_Edges]

/-- Splitting `Fin s \ {k}` into the labels below and above `k`. -/
theorem sum_lt_add_sum_gt_of_eq_zero (f : Fin s → ℝ) (k : Fin s) (hk : f k = 0) :
    (∑ i ∈ Finset.univ.filter (fun i => i < k), f i)
      + (∑ j ∈ Finset.univ.filter (fun j => k < j), f j) = ∑ m, f m := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  symm
  exact Finset.sum_congr rfl fun m _ => by
    rcases lt_trichotomy m k with h | h | h
    · simp [h, asymm h]
    · subst h
      simp [hk]
    · simp [h, asymm h]

/-- The squared differences on complete-graph edges incident to `k` contribute
exactly the squared mass of the nonzero vertex terms. -/
theorem sum_incident_norm_sub_sq {v : Fin s → EuclideanSpace ℂ W} (k : Fin s)
    (hk : v k = 0) :
    ∑ p ∈ Edges.filter (fun p => ¬(p.1 ≠ k ∧ p.2 ≠ k)), ‖v p.1 - v p.2‖ ^ 2
      = ∑ m, ‖v m‖ ^ 2 := by
  rw [Finset.sum_filter]
  have hpoint : ∀ p ∈ Edges,
      (if ¬(p.1 ≠ k ∧ p.2 ≠ k) then ‖v p.1 - v p.2‖ ^ 2 else 0)
        = (if k = p.2 then ‖v p.1 - v p.2‖ ^ 2 else 0)
          + (if k = p.1 then ‖v p.1 - v p.2‖ ^ 2 else 0) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (mem_Edges.mp hp).ne
    by_cases h2 : k = p.2
    · have h1 : k ≠ p.1 := by
        intro h1
        exact (mem_Edges.mp hp).ne (h1.symm.trans h2)
      simp [h2, eq_comm, hne]
    · by_cases h1 : k = p.1
      · simp [h1, eq_comm, hne]
      · simp [h2, h1, eq_comm]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib,
    sum_Edges_ite_snd k (fun i j => ‖v i - v j‖ ^ 2),
    sum_Edges_ite_fst k (fun i j => ‖v i - v j‖ ^ 2)]
  simp_rw [hk, sub_zero, zero_sub, norm_neg]
  exact sum_lt_add_sum_gt_of_eq_zero (fun m => ‖v m‖ ^ 2) k (by simp [hk])

/-- The exact vertex variance identity used in
`eq:sos-complete-graph`. -/
theorem vertex_variance (v : Fin s → EuclideanSpace ℂ W) (k : Fin s) (hk : v k = 0) :
    ((s : ℝ) - 1) * ∑ m, ‖v m‖ ^ 2 - ‖∑ m, v m‖ ^ 2
      = ∑ p ∈ OtherEdges k, ‖v p.1 - v p.2‖ ^ 2 := by
  have hall := completeGraph_variance v
  have hincident := sum_incident_norm_sub_sq k hk
  have hsplit :
      (∑ p ∈ OtherEdges k, ‖v p.1 - v p.2‖ ^ 2)
        + ∑ p ∈ Edges.filter (fun p => ¬(p.1 ≠ k ∧ p.2 ≠ k)),
            ‖v p.1 - v p.2‖ ^ 2
        = ∑ p ∈ Edges, ‖v p.1 - v p.2‖ ^ 2 := by
    exact Finset.sum_filter_add_sum_filter_not Edges
      (fun p => p.1 ≠ k ∧ p.2 ≠ k) (fun p => ‖v p.1 - v p.2‖ ^ 2)
  rw [hincident] at hsplit
  linarith

end VertexVariance

section SynthesisDefect

variable {W : Type*} [Fintype W] {s : ℕ}

/-- The vertex variance identity specialized to the signed edge contributions
of `Tsyn`. -/
theorem vtx_variance (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) (k : Fin s) :
    ((s : ℝ) - 1) * ∑ m, ‖vtxTerm e K k m‖ ^ 2 - ‖vtx e K k‖ ^ 2
      = ∑ p ∈ OtherEdges k,
          ‖vtxTerm e K k p.1 - vtxTerm e K k p.2‖ ^ 2 := by
  rw [vtx_eq_sum_vtxTerm]
  exact vertex_variance (vtxTerm e K k) k (vtxTerm_self e K k)

/-- Exact global variance defect for the complete-graph synthesis map. -/
theorem Tsyn_variance_defect (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) :
    ((s : ℝ) - 1) *
        ∑ p ∈ Edges, (‖mulVecE (K p.1 p.2) (ebar e p.1)‖ ^ 2
          + ‖mulVecE (K p.1 p.2) (ebar e p.2)‖ ^ 2)
      - ‖Tsyn e K‖ ^ 2
      = ∑ k, ∑ p ∈ OtherEdges k,
          ‖vtxTerm e K k p.1 - vtxTerm e K k p.2‖ ^ 2 := by
  rw [Tsyn_eq_delta_vtx, norm_delta, ← sum_sum_vtxTerm_sq,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => vtx_variance e K k

/-- **Complete-graph defect certificate** (`eq:sos-complete-graph`), expressed
directly in terms of the edge matrices `K`.

The manuscript substitutes `‖K_{ij}‖₂² = 4‖c^{(ij)}‖₂²` and uses a synthesis
map normalized by `1 / √2`; clearing those two conventions gives exactly this
identity. -/
theorem completeGraph_defect_certificate (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) :
    (((s : ℝ) - 1) / 4) * ∑ p ∈ Edges, hsNormSq (K p.1 p.2)
        - (1 / 2 : ℝ) * ‖Tsyn e K‖ ^ 2
      = (((s : ℝ) - 1) / 2) *
          ∑ p ∈ Edges,
            ((1 / 2 : ℝ) * hsNormSq (K p.1 p.2)
              - ‖mulVecE (K p.1 p.2) (ebar e p.1)‖ ^ 2
              - ‖mulVecE (K p.1 p.2) (ebar e p.2)‖ ^ 2)
        + (1 / 2 : ℝ) *
          ∑ k, ∑ p ∈ OtherEdges k,
            ‖vtxTerm e K k p.1 - vtxTerm e K k p.2‖ ^ 2 := by
  have h := Tsyn_variance_defect e K
  have hedge :
      (∑ p ∈ Edges,
          ((1 / 2 : ℝ) * hsNormSq (K p.1 p.2)
            - ‖mulVecE (K p.1 p.2) (ebar e p.1)‖ ^ 2
            - ‖mulVecE (K p.1 p.2) (ebar e p.2)‖ ^ 2))
        = (1 / 2 : ℝ) * ∑ p ∈ Edges, hsNormSq (K p.1 p.2)
          - ∑ p ∈ Edges, (‖mulVecE (K p.1 p.2) (ebar e p.1)‖ ^ 2
            + ‖mulVecE (K p.1 p.2) (ebar e p.2)‖ ^ 2) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_add_distrib]
    ring
  rw [hedge]
  nlinarith

/-- Parseval for a Kraus basis whose Hilbert--Schmidt squared norm is `4`.
This is the abstract normalization calculation in `eq:Kc-norm`. -/
theorem hsNormSq_sum_smul_of_hsInner_four
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Matrix W W ℂ) (c : ι → ℂ)
    (hA : ∀ i j, hsInner (A i) (A j) = if i = j then 4 else 0) :
    hsNormSq (∑ i, c i • A i) = 4 * ∑ i, Complex.normSq (c i) := by
  rw [← Complex.ofReal_inj, ← hsInner_self, hsInner_sum_sum]
  simp only [hsInner_smul_left, hsInner_smul_right, hA]
  push_cast
  simp only [mul_comm, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Complex.normSq_eq_conj_mul_self]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The certificate in the manuscript's coefficient notation.  The hypothesis
is precisely `eq:Kc-norm`; it is separated because the development's
`skewKraus` family is deliberately redundant, whereas the manuscript chooses a
nonredundant normalized basis of the double-skew space. -/
theorem completeGraph_defect_certificate_coeff
    {ι : Type*} [Fintype ι]
    (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ)
    (c : ι × (Fin s × Fin s) → ℂ)
    (hKnorm : ∀ p ∈ Edges,
      hsNormSq (K p.1 p.2) = 4 * ∑ f : ι, Complex.normSq (c (f, p))) :
    ((s : ℝ) - 1) * (∑ p ∈ Edges, ∑ f : ι, Complex.normSq (c (f, p)))
        - (1 / 2 : ℝ) * ‖Tsyn e K‖ ^ 2
      = (((s : ℝ) - 1) / 2) *
          ∑ p ∈ Edges,
            ((1 / 2 : ℝ) * hsNormSq (K p.1 p.2)
              - ‖mulVecE (K p.1 p.2) (ebar e p.1)‖ ^ 2
              - ‖mulVecE (K p.1 p.2) (ebar e p.2)‖ ^ 2)
        + (1 / 2 : ℝ) *
          ∑ k, ∑ p ∈ OtherEdges k,
            ‖vtxTerm e K k p.1 - vtxTerm e K k p.2‖ ^ 2 := by
  have hcert := completeGraph_defect_certificate e K
  have hnorm :
      (∑ p ∈ Edges, hsNormSq (K p.1 p.2))
        = 4 * ∑ p ∈ Edges, ∑ f : ι, Complex.normSq (c (f, p)) := by
    calc
      _ = ∑ p ∈ Edges, 4 * ∑ f : ι, Complex.normSq (c (f, p)) :=
        Finset.sum_congr rfl hKnorm
      _ = _ := by rw [Finset.mul_sum]
  rw [hnorm] at hcert
  nlinarith

end SynthesisDefect

section DoubleSkewDefect

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  {s : ℕ}

/-- Every edge matrix assembled from the double-skew Kraus family remains in
the double-skew subspace. -/
theorem Kof_skewKraus_mem_doubleSkew
    (c : KIdx U V × (Fin s × Fin s) → ℂ) (i j : Fin s) :
    Kof skewKraus c i j ∈ doubleSkew U V := by
  rw [Kof]
  exact Submodule.sum_mem _ fun f _ =>
    Submodule.smul_mem _ _ (skewKraus_mem_doubleSkew f)

/-- Each edge bracket in `eq:sos-complete-graph` is nonnegative by the
double-skew action bound. -/
theorem edge_doubleSkew_defect_nonneg
    (hDS : DoubleSkewBound U V)
    {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (K : Fin s → Fin s → Matrix (U × V) (U × V) ℂ)
    (hK : ∀ p ∈ Edges, K p.1 p.2 ∈ doubleSkew U V) {p : Fin s × Fin s}
    (hp : p ∈ Edges) :
    0 ≤ (1 / 2 : ℝ) * hsNormSq (K p.1 p.2)
      - ‖mulVecE (K p.1 p.2) (ebar e p.1)‖ ^ 2
      - ‖mulVecE (K p.1 p.2) (ebar e p.2)‖ ^ 2 := by
  have heb := orthonormal_ebar he
  have hpne : p.1 ≠ p.2 := (mem_Edges.mp hp).ne
  have h := hDS (K p.1 p.2) (hK p hp) (ebar e p.1) (ebar e p.2)
    (heb.1 p.1) (heb.1 p.2) (heb.2 hpne)
  rw [← mulVecE_eq_toEuclideanLin, ← mulVecE_eq_toEuclideanLin] at h
  linarith

/-- Nonnegativity of the complete-graph defect, with the double-skew action
bound retained as an explicit hypothesis. -/
theorem completeGraph_defect_nonneg
    (hDS : DoubleSkewBound U V)
    {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (K : Fin s → Fin s → Matrix (U × V) (U × V) ℂ)
    (hK : ∀ p ∈ Edges, K p.1 p.2 ∈ doubleSkew U V) :
    0 ≤ (((s : ℝ) - 1) / 4) * ∑ p ∈ Edges, hsNormSq (K p.1 p.2)
      - (1 / 2 : ℝ) * ‖Tsyn e K‖ ^ 2 := by
  rw [completeGraph_defect_certificate]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [Edges, OtherEdges]
  · have hs1 : (0 : ℝ) ≤ ((s : ℝ) - 1) / 2 := by
      have : (1 : ℝ) ≤ s := by exact_mod_cast hs
      positivity
    have hedge : 0 ≤ ∑ p ∈ Edges,
        ((1 / 2 : ℝ) * hsNormSq (K p.1 p.2)
          - ‖mulVecE (K p.1 p.2) (ebar e p.1)‖ ^ 2
          - ‖mulVecE (K p.1 p.2) (ebar e p.2)‖ ^ 2) :=
      Finset.sum_nonneg fun p hp => edge_doubleSkew_defect_nonneg hDS he K hK hp
    have hvariance : 0 ≤ ∑ k, ∑ p ∈ OtherEdges k,
        ‖vtxTerm e K k p.1 - vtxTerm e K k p.2‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun p _ => sq_nonneg _
    positivity

/-- The complete-graph defect is nonnegative with no mathematical hypothesis
left open. -/
theorem completeGraph_defect_nonneg_holds
    {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (K : Fin s → Fin s → Matrix (U × V) (U × V) ℂ)
    (hK : ∀ p ∈ Edges, K p.1 p.2 ∈ doubleSkew U V) :
    0 ≤ (((s : ℝ) - 1) / 4) * ∑ p ∈ Edges, hsNormSq (K p.1 p.2)
      - (1 / 2 : ℝ) * ‖Tsyn e K‖ ^ 2 :=
  completeGraph_defect_nonneg doubleSkewBound_holds he K hK

/-- Nonnegativity for the edge matrices actually assembled from the
double-skew Kraus coefficients in the lifting proof. -/
theorem completeGraph_Kof_skewKraus_defect_nonneg
    {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (c : KIdx U V × (Fin s × Fin s) → ℂ) :
    0 ≤ (((s : ℝ) - 1) / 4) *
        ∑ p ∈ Edges, hsNormSq (Kof skewKraus c p.1 p.2)
      - (1 / 2 : ℝ) * ‖Tsyn e (Kof skewKraus c)‖ ^ 2 :=
  completeGraph_defect_nonneg_holds he (Kof skewKraus c)
    (fun p _ => Kof_skewKraus_mem_doubleSkew c p.1 p.2)

end DoubleSkewDefect

end RankR
