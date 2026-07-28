/-
Exterior amplification: the hypergraph bound at arity `k`.

A completely positive map `Φ` with Kraus family `{A_f}` is amplified by the
identity on `⋀^{k-1}ℂ^r` and applied to the hypergraph operator
`P_H = ∑_{I ∈ H} |η_I⟩⟨η_I|` of a `k`-uniform hypergraph `H` on `Fin r`.  The
result is bounded by the largest number of hyperedges sharing a `(k-1)`-face,
times the level-`k` Choi constant:

  (A₀)  `⟪y, (Φ ⊗ id)(P_H) y⟫ ≤ d↑(H) β ‖y‖²`.

The argument is the pair argument of `Lifting.lean` one level up.  Synthesizing
the frame `{(A_f ⊗ id) η_I}` with coefficients `c` produces
`𝒯c = ∑_{I ∈ H} (K_I ⊗ id) η_I` for the edge data `K_I = ∑_f c_{f,I} A_f`.  The
map `(I, v) ↦ I ∖ v` sends the incidences of `H` onto the pairs `J ⊆ I`, so
collecting the coefficient of each face `J` exhibits `𝒯c` as a vector whose
`J`-block is a sum of `d_J = #\{I ∈ H : J ⊆ I\}` terms.  Cauchy-Schwarz on each
block contributes `d↑(H)`, and Lifting I at level `k` bounds the incidences of a
single hyperedge — the `k` orthonormal vectors `{ē_v}_{v ∈ I}` — by `kβ` times
the coefficient mass of that hyperedge.  The two factors of `k` cancel against
the normalization of `η_I`.  Bessel duality converts the synthesis bound into
the analysis bound.

Transpose symmetry of the Kraus operators then sharpens it on the span of the
modes `δ_L` indexed by `(k-2)`-faces:

  (A)   `⟪y, (Φ ⊗ id)(P_H) y⟫ ≤ d↑(H) β (‖y‖² − ∑_L |⟪δ_L, y⟫|²)`.

The orthogonality behind it is a Koszul cancellation.  A face `L` and a
hyperedge `I ⊇ L` with `I ∖ L = \{u, v\}` contribute two terms, one for each
choice of which of `u, v` is adjoined to `L` and which is removed from `I`; the
position signs of the two differ by exactly one transposition, and transpose
symmetry makes the two bilinear forms equal, so the pair cancels.

At `k = 2` the incidence modes are the antisymmetric combinations of the pair
sector, the single mode `δ_∅` is the normalized `δ_e`, and the complete graph has
`d↑ = r − 1`, which is pair amplification.
-/
import RankR.Bessel
import RankR.Choi
import RankR.Exterior
import RankR.Frame
import RankR.Restrict

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## Tools

Linearity of the matrix action in the vector, and of placement in the placed
vector. -/

section Tools

variable {W : Type*} {r m : ℕ}

/-- Placement is homogeneous in the placed vector. -/
theorem placeAt_smul (c : ℂ) (u : EuclideanSpace ℂ W) (t : Finset (Fin r)) :
    (placeAt (c • u) t : EuclideanSpace ℂ (W × Face r m)) = c • placeAt u t := by
  ext x
  simp only [placeAt_apply, PiLp.smul_apply, smul_eq_mul, mul_ite, mul_zero]

variable [Fintype W]

/-- The matrix action is homogeneous in the vector. -/
theorem mulVecE_smul_vec (A : Matrix W W ℂ) (c : ℂ) (x : EuclideanSpace ℂ W) :
    mulVecE A (c • x) = c • mulVecE A x := by
  ext p
  simp only [mulVecE_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- The matrix action is additive in the vector. -/
theorem mulVecE_sum_vec {M : Type*} (s : Finset M) (A : Matrix W W ℂ)
    (x : M → EuclideanSpace ℂ W) :
    mulVecE A (∑ i ∈ s, x i) = ∑ i ∈ s, mulVecE A (x i) := by
  ext p
  rw [mulVecE_apply, sum_apply_euclidean]
  have h : ∀ q : W, A p q * (∑ i ∈ s, x i) q = ∑ i ∈ s, A p q * x i q := fun q => by
    rw [sum_apply_euclidean, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun q _ => h q, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (mulVecE_apply _ _ _).symm

end Tools

/-! ## Blocks and the face regrouping

A vector on `W ⊗ ⋀^m` is the list of its blocks, one for each face, and its
squared norm is the total squared block norm.  A sum of placed vectors has, as
its `J`-block, the sum of the terms labelled `J`; Cauchy-Schwarz on each block
costs the size of the largest fibre. -/

section Blocks

variable {W : Type*} {r m : ℕ}

/-- The `J`-block of a vector on `W ⊗ ⋀^m`: its restriction to the coordinates
labelled by the face `J`. -/
def blockAt (y : EuclideanSpace ℂ (W × Face r m)) (J : Face r m) : EuclideanSpace ℂ W :=
  WithLp.toLp 2 fun p => y (p, J)

@[simp] theorem blockAt_apply (y : EuclideanSpace ℂ (W × Face r m)) (J : Face r m) (p : W) :
    blockAt y J p = y (p, J) := rfl

/-- The `J`-block of a sum of placed vectors is the sum of the terms labelled
`J`. -/
theorem blockAt_sum_placeAt {M : Type*} (s : Finset M) (u : M → EuclideanSpace ℂ W)
    (t : M → Finset (Fin r)) (J : Face r m) :
    blockAt (∑ x ∈ s, placeAt (u x) (t x)) J = ∑ x ∈ s.filter (fun x => J.val = t x), u x := by
  ext p
  rw [blockAt_apply, sum_apply_euclidean, sum_apply_euclidean, Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by rw [placeAt_apply]

variable [Fintype W]

/-- The squared norm is the total squared block norm. -/
theorem norm_sq_eq_sum_blockAt (y : EuclideanSpace ℂ (W × Face r m)) :
    ‖y‖ ^ 2 = ∑ J : Face r m, ‖blockAt y J‖ ^ 2 := by
  have h : ∀ J : Face r m, ‖blockAt y J‖ ^ 2 = ∑ p : W, Complex.normSq (y (p, J)) := fun J => by
    rw [norm_sq_eq_sum_normSq]
    exact Finset.sum_congr rfl fun p _ => rfl
  rw [Finset.sum_congr rfl fun J _ => h J, norm_sq_eq_sum_normSq, Fintype.sum_prod_type,
    Finset.sum_comm]

/-- **The face regrouping bound.**  A sum of placed vectors is bounded by the
largest fibre size of the labelling times the total squared mass of the placed
vectors: the blocks are orthogonal, each is a sum of at most `D` terms, and each
term is counted at most once because a face is determined by its underlying
set. -/
theorem norm_sq_sum_placeAt_le {M : Type*} (s : Finset M) (u : M → EuclideanSpace ℂ W)
    (t : M → Finset (Fin r)) {D : ℕ}
    (hD : ∀ J : Face r m, (s.filter (fun x => J.val = t x)).card ≤ D) :
    ‖∑ x ∈ s, (placeAt (u x) (t x) : EuclideanSpace ℂ (W × Face r m))‖ ^ 2
      ≤ (D : ℝ) * ∑ x ∈ s, ‖u x‖ ^ 2 := by
  rw [norm_sq_eq_sum_blockAt]
  have hblk : ∀ J : Face r m,
      ‖blockAt (∑ x ∈ s, (placeAt (u x) (t x) : EuclideanSpace ℂ (W × Face r m))) J‖ ^ 2
        ≤ (D : ℝ) * ∑ x ∈ s.filter (fun x => J.val = t x), ‖u x‖ ^ 2 := fun J => by
    rw [blockAt_sum_placeAt]
    set F := s.filter (fun x => J.val = t x) with hF
    have h1 : ‖∑ x ∈ F, u x‖ ≤ ∑ x ∈ F, ‖u x‖ := norm_sum_le _ _
    have h2 : (∑ x ∈ F, ‖u x‖) ^ 2 ≤ (F.card : ℝ) * ∑ x ∈ F, ‖u x‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := F) (f := fun x => ‖u x‖)
    have h3 : (F.card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD J
    have h4 : (0 : ℝ) ≤ ∑ x ∈ F, ‖u x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h5 : (0 : ℝ) ≤ ∑ x ∈ F, ‖u x‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    nlinarith [norm_nonneg (∑ x ∈ F, u x)]
  refine le_trans (Finset.sum_le_sum fun J _ => hblk J) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg D)
  have hswap : ∑ J : Face r m, ∑ x ∈ s.filter (fun x => J.val = t x), ‖u x‖ ^ 2
      = ∑ x ∈ s, ∑ J : Face r m, (if J.val = t x then ‖u x‖ ^ 2 else 0) := by
    simp only [Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_le_sum fun x _ => ?_
  have hcard : (Finset.univ.filter (fun J : Face r m => J.val = t x)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact Subtype.ext (ha.2.trans hb.2.symm)
  have hcardR : ((Finset.univ.filter (fun J : Face r m => J.val = t x)).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  nlinarith [sq_nonneg ‖u x‖]

end Blocks

/-! ## The amplified map and its frame -/

section Amplified

variable {W ι : Type*} [Fintype W] {r k : ℕ}

/-- `Φ_A ⊗ id`: the Kraus sum of a family on `W`, acting trivially on the
exterior factor. -/
noncomputable def krausF [Fintype ι] (A : ι → Matrix W W ℂ)
    (Y : Matrix (W × Face r (k - 1)) (W × Face r (k - 1)) ℂ) :
    Matrix (W × Face r (k - 1)) (W × Face r (k - 1)) ℂ :=
  krausSum (fun f => placeT (A f)) Y

/-- The hypergraph operator `P_H = ∑_{I ∈ H} |η_I⟩⟨η_I|`. -/
noncomputable def Phyp (e : Fin r → EuclideanSpace ℂ W) (H : Finset (Face r k)) :
    Matrix (W × Face r (k - 1)) (W × Face r (k - 1)) ℂ :=
  ∑ I ∈ H, rankOne (etaMode e I) (etaMode e I)

/-- `d↑_{k-1}(H)`: the largest number of hyperedges of `H` containing a common
`(k-1)`-face. -/
def upDeg (H : Finset (Face r k)) : ℕ :=
  Finset.univ.sup fun J : Face r (k - 1) => (H.filter fun I => J.val ⊆ I.val).card

/-- Each `(k-1)`-face lies in at most `d↑_{k-1}(H)` hyperedges. -/
theorem card_le_upDeg (H : Finset (Face r k)) (J : Face r (k - 1)) :
    (H.filter fun I => J.val ⊆ I.val).card ≤ upDeg H :=
  Finset.le_sup (f := fun J : Face r (k - 1) => (H.filter fun I => J.val ⊆ I.val).card)
    (Finset.mem_univ J)

/-- The frame vectors: the images of the incidence modes of `H` under the Kraus
operators, extended by zero off `H`. -/
noncomputable def wvecF (A : ι → Matrix W W ℂ) (e : Fin r → EuclideanSpace ℂ W)
    (H : Finset (Face r k)) (f : ι) (I : Face r k) : EuclideanSpace ℂ (W × Face r (k - 1)) :=
  if I ∈ H then mulVecE (placeT (A f)) (etaMode e I) else 0

variable [Fintype ι]

/-- The quadratic form of `(Φ_A ⊗ id)(P_H)` is the total squared overlap with the
frame. -/
theorem qform_krausF_Phyp (A : ι → Matrix W W ℂ) (e : Fin r → EuclideanSpace ℂ W)
    (H : Finset (Face r k)) (y : EuclideanSpace ℂ (W × Face r (k - 1))) :
    qform (krausF A (Phyp e H)) y
      = ∑ f : ι, ∑ I : Face r k,
          ((Complex.normSq (inner ℂ (wvecF A e H f I) y) : ℝ) : ℂ) := by
  rw [krausF, qform_krausSum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Phyp, qform_sum_finset,
    show ∑ I ∈ H, qform (rankOne (etaMode e I) (etaMode e I))
          (mulVecE (placeT (A f))ᴴ y)
        = ∑ I : Face r k, (if I ∈ H then qform (rankOne (etaMode e I) (etaMode e I))
            (mulVecE (placeT (A f))ᴴ y) else 0) from by
      rw [Finset.sum_ite_mem, Finset.univ_inter]]
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases h : I ∈ H
  · rw [if_pos h, qform_rankOne, wvecF, if_pos h, inner_mulVecE_left,
      Matrix.conjTranspose_conjTranspose]
  · rw [if_neg h, wvecF, if_neg h]
    simp

/-- The same Bessel sum with the two indices merged and the real part taken, which
is the form Bessel duality consumes. -/
theorem re_qform_krausF_Phyp (A : ι → Matrix W W ℂ) (e : Fin r → EuclideanSpace ℂ W)
    (H : Finset (Face r k)) (y : EuclideanSpace ℂ (W × Face r (k - 1))) :
    (qform (krausF A (Phyp e H)) y).re
      = ∑ z : ι × Face r k, Complex.normSq (inner ℂ (wvecF A e H z.1 z.2) y) := by
  rw [qform_krausF_Phyp, Complex.re_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun f _ => by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun I _ => Complex.ofReal_re _

end Amplified

/-! ## Synthesis -/

section Synthesis

variable {W ι : Type*} [Fintype W] [Fintype ι] {r k : ℕ}

/-- The member of the Kraus span carried by the hyperedge `I`. -/
noncomputable def Kface (A : ι → Matrix W W ℂ) (c : ι × Face r k → ℂ) (I : Face r k) :
    Matrix W W ℂ := ∑ f, c (f, I) • A f

/-- The vector deposited at the face `I ∖ v` by the incidence `(I, v)`. -/
noncomputable def uterm (A : ι → Matrix W W ℂ) (e : Fin r → EuclideanSpace ℂ W)
    (c : ι × Face r k → ℂ) (x : Face r k × Fin r) : EuclideanSpace ℂ W :=
  if x.2 ∈ x.1.val then
    ((Real.sqrt k : ℝ) : ℂ)⁻¹ • (esign x.1.val x.2 • mulVecE (Kface A c x.1) (ebar e x.2))
  else 0

/-- An operator acting trivially on the exterior factor moves the incidence mode
of `I` to the sum of its incidence contributions. -/
theorem mulVecE_placeT_etaMode (hk : 1 ≤ k) (N : Matrix W W ℂ)
    (e : Fin r → EuclideanSpace ℂ W) (I : Face r k) :
    mulVecE (placeT (T := Face r (k - 1)) N) (etaMode e I)
      = ∑ v : Fin r, placeAt (if v ∈ I.val then
          ((Real.sqrt k : ℝ) : ℂ)⁻¹ • (esign I.val v • mulVecE N (ebar e v)) else 0)
          (I.val.erase v) := by
  rw [etaMode, mulVecE_smul_vec, mulVecE_sum_vec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mulVecE_smul_vec, mulVecE_placeT_placeAt]
  by_cases hv : v ∈ I.val
  · rw [if_pos hv, placeAt_smul, placeAt_smul]
  · have hc : (I.val.erase v).card ≠ k - 1 := by
      rw [Finset.erase_eq_of_notMem hv, I.2]
      omega
    rw [if_neg hv, placeAt_eq_zero _ hc, placeAt_eq_zero _ hc, smul_zero, smul_zero]

/-- Synthesizing the frame with coefficients `c` deposits, at each incidence
`(I, v)` of the hypergraph, the vector `uterm` at the face `I ∖ v`. -/
theorem sum_smul_wvecF (hk : 1 ≤ k) (A : ι → Matrix W W ℂ) (e : Fin r → EuclideanSpace ℂ W)
    (H : Finset (Face r k)) (c : ι × Face r k → ℂ) :
    ∑ z : ι × Face r k, c z • wvecF A e H z.1 z.2
      = ∑ x ∈ H ×ˢ (Finset.univ : Finset (Fin r)),
          placeAt (uterm A e c x) (x.1.val.erase x.2) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_product]
  have hI : ∀ I : Face r k, ∑ f : ι, c (f, I) • wvecF A e H f I
      = if I ∈ H then ∑ v : Fin r, placeAt (uterm A e c (I, v)) (I.val.erase v) else 0 := by
    intro I
    by_cases h : I ∈ H
    · rw [if_pos h]
      have hstep : ∀ f : ι, c (f, I) • wvecF A e H f I
          = mulVecE (placeT (T := Face r (k - 1)) (c (f, I) • A f)) (etaMode e I) := fun f => by
        rw [wvecF, if_pos h, placeT_smul, mulVecE_smul]
      rw [Finset.sum_congr rfl fun f _ => hstep f, ← mulVecE_sum, ← placeT_sum,
        mulVecE_placeT_etaMode hk]
      exact Finset.sum_congr rfl fun v _ => rfl
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun f _ => by rw [wvecF, if_neg h, smul_zero]
  rw [Finset.sum_congr rfl fun I _ => hI I, Finset.sum_ite_mem, Finset.univ_inter]

/-! ## The synthesis bound -/

/-- A `(k-1)`-face is removed from a `k`-face only at one of its own vertices. -/
theorem mem_of_erase_eq (hk : 1 ≤ k) {I : Face r k} {J : Face r (k - 1)} {v : Fin r}
    (h : J.val = I.val.erase v) : v ∈ I.val := by
  by_contra hv
  rw [Finset.erase_eq_of_notMem hv] at h
  have hcc := congrArg Finset.card h
  rw [J.2, I.2] at hcc
  omega

/-- The incidences of `H` lying over a fixed `(k-1)`-face are at most
`d↑_{k-1}(H)` in number: the hyperedge determines the incidence, because the
removed vertex is the one missing from the face. -/
theorem card_fibre_le_upDeg (hk : 1 ≤ k) (H : Finset (Face r k)) (J : Face r (k - 1)) :
    (((H ×ˢ (Finset.univ : Finset (Fin r))).filter
        fun x : Face r k × Fin r => J.val = x.1.val.erase x.2).card) ≤ upDeg H := by
  refine le_trans (Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_) (card_le_upDeg H J)
  · intro x hx
    have hmem := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hmem.1).1, ?_⟩
    rw [hmem.2]
    exact Finset.erase_subset _ _
  · intro x hx y hy hxy
    have hxf := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    have hyf := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    have hx2 : x.2 ∈ x.1.val := mem_of_erase_eq hk hxf
    have hy2 : y.2 ∈ y.1.val := mem_of_erase_eq hk hyf
    have hxe : x.1.val = insert x.2 J.val := by rw [hxf, Finset.insert_erase hx2]
    have hye : y.1.val = insert y.2 J.val := by rw [hyf, Finset.insert_erase hy2]
    have hxJ : x.2 ∉ J.val := by rw [hxf]; exact Finset.notMem_erase _ _
    have hxy' : x.1 = y.1 := hxy
    have hmem : x.2 ∈ insert y.2 J.val := by
      rw [← hye, ← hxy', hxe]
      exact Finset.mem_insert_self _ _
    refine Prod.ext hxy' ?_
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exact absurd h hxJ

/-- The `k` conjugated frame vectors indexed by the vertices of a `k`-face are
orthonormal, so Lifting I at level `k` bounds their total action by `kβ` times
the coefficient mass. -/
theorem sum_face_norm_sq_le {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiKBound (choiOf A) k β) {e : Fin r → EuclideanSpace ℂ W} (he : Orthonormal ℂ e)
    (c : ι → ℂ) (I : Face r k) :
    ∑ v ∈ I.val, ‖mulVecE (∑ f, c f • A f) (ebar e v)‖ ^ 2
      ≤ k * β * ∑ f, Complex.normSq (c f) := by
  set g : Fin r → ℝ := fun v => ‖mulVecE (∑ f, c f • A f) (ebar e v)‖ ^ 2 with hg
  set σ : Fin k → Fin r := fun i => (I.val.orderIsoOfFin I.2 i : Fin r) with hσ
  have hinj : Function.Injective σ := fun i j h =>
    (I.val.orderIsoOfFin I.2).injective (Subtype.ext h)
  have hon : Orthonormal ℂ (fun i => ebar e (σ i)) := (orthonormal_ebar he).comp σ hinj
  have hre : ∑ v ∈ I.val, g v = ∑ i : Fin k, g (σ i) := by
    rw [← Finset.sum_coe_sort I.val g]
    exact (Fintype.sum_equiv (I.val.orderIsoOfFin I.2).toEquiv _ _ fun i => rfl).symm
  rw [hg] at hre
  rw [hre]
  exact norm_sq_le_of_choiKBound hβ hJ c hon

/-- The mass an incidence carries: the normalization contributes `1/k` and the
position sign contributes nothing. -/
theorem norm_sq_uterm (A : ι → Matrix W W ℂ) (e : Fin r → EuclideanSpace ℂ W)
    (c : ι × Face r k → ℂ) (I : Face r k) (v : Fin r) :
    ‖uterm A e c (I, v)‖ ^ 2
      = if v ∈ I.val then (k : ℝ)⁻¹ * ‖mulVecE (Kface A c I) (ebar e v)‖ ^ 2 else 0 := by
  have hs : ‖((Real.sqrt k : ℝ) : ℂ)⁻¹‖ ^ 2 = (k : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  rw [uterm]
  by_cases hv : v ∈ I.val
  · rw [if_pos hv, if_pos hv, norm_smul, norm_smul, norm_esign, one_mul, mul_pow, hs]
  · rw [if_neg hv, if_neg hv, norm_zero]
    exact zero_pow (by norm_num)

/-- **The uniform synthesis bound.**  The face regrouping costs `d↑_{k-1}(H)`;
Lifting I at level `k` bounds each hyperedge's contribution by `kβ` times the
coefficient mass it carries, and the `1/k` of the incidence modes cancels the
`k`. -/
theorem norm_sum_smul_wvecF_le {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiKBound (choiOf A) k β) (hk : 1 ≤ k) {e : Fin r → EuclideanSpace ℂ W}
    (he : Orthonormal ℂ e) (H : Finset (Face r k)) (c : ι × Face r k → ℂ) :
    ‖∑ z : ι × Face r k, c z • wvecF A e H z.1 z.2‖ ^ 2
      ≤ (upDeg H : ℝ) * β * ∑ z : ι × Face r k, Complex.normSq (c z) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  -- the mass carried by one hyperedge
  have hface : ∀ I : Face r k, ∑ v : Fin r, ‖uterm A e c (I, v)‖ ^ 2
      ≤ β * ∑ f : ι, Complex.normSq (c (f, I)) := fun I => by
    have hrestrict : ∑ v : Fin r, ‖uterm A e c (I, v)‖ ^ 2
        = (k : ℝ)⁻¹ * ∑ v ∈ I.val, ‖mulVecE (Kface A c I) (ebar e v)‖ ^ 2 := by
      rw [Finset.sum_congr rfl fun v _ => norm_sq_uterm A e c I v, ← Finset.sum_filter,
        Finset.mul_sum]
      exact Finset.sum_congr (by simp) fun v _ => rfl
    rw [hrestrict, Kface]
    calc (k : ℝ)⁻¹ * ∑ v ∈ I.val, ‖mulVecE (∑ f, c (f, I) • A f) (ebar e v)‖ ^ 2
        ≤ (k : ℝ)⁻¹ * ((k : ℝ) * β * ∑ f : ι, Complex.normSq (c (f, I))) :=
          mul_le_mul_of_nonneg_left
            (sum_face_norm_sq_le hβ hJ he (fun f => c (f, I)) I) (by positivity)
      _ = β * ∑ f : ι, Complex.normSq (c (f, I)) := by field_simp
  -- the total mass
  have htotal : ∑ x ∈ H ×ˢ (Finset.univ : Finset (Fin r)), ‖uterm A e c x‖ ^ 2
      ≤ β * ∑ z : ι × Face r k, Complex.normSq (c z) := by
    rw [Finset.sum_product]
    refine le_trans (Finset.sum_le_sum fun I _ => hface I) ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun I _ _ => ?_
    exact mul_nonneg hβ (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  -- the regrouping
  rw [sum_smul_wvecF hk]
  calc ‖∑ x ∈ H ×ˢ (Finset.univ : Finset (Fin r)),
          (placeAt (uterm A e c x) (x.1.val.erase x.2) :
            EuclideanSpace ℂ (W × Face r (k - 1)))‖ ^ 2
      ≤ (upDeg H : ℝ) * ∑ x ∈ H ×ˢ (Finset.univ : Finset (Fin r)), ‖uterm A e c x‖ ^ 2 :=
        norm_sq_sum_placeAt_le (m := k - 1) (H ×ˢ (Finset.univ : Finset (Fin r)))
          (uterm A e c) (fun x => x.1.val.erase x.2) (card_fibre_le_upDeg hk H)
    _ ≤ (upDeg H : ℝ) * (β * ∑ z : ι × Face r k, Complex.normSq (c z)) :=
        mul_le_mul_of_nonneg_left htotal (Nat.cast_nonneg _)
    _ = (upDeg H : ℝ) * β * ∑ z : ι × Face r k, Complex.normSq (c z) := by ring

/-- **Theorem A.**  `(Φ_A ⊗ id)(P_H) ⪯ d↑_{k-1}(H) β I`, for any Kraus family
whose Choi operator obeys `ChoiKBound _ k β`.

The synthesis bound is the whole input; Bessel duality converts it into the
analysis bound.  No hypothesis on the transposes of the Kraus operators. -/
theorem qform_krausF_Phyp_le_of_norm {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiKBound (choiOf A) k β) (hk : 1 ≤ k) {e : Fin r → EuclideanSpace ℂ W}
    (he : Orthonormal ℂ e) (H : Finset (Face r k))
    (y : EuclideanSpace ℂ (W × Face r (k - 1))) :
    (qform (krausF A (Phyp e H)) y).re ≤ (upDeg H : ℝ) * β * ‖y‖ ^ 2 := by
  rw [re_qform_krausF_Phyp]
  exact frame_le_of_synthesis_le (fun z : ι × Face r k => wvecF A e H z.1 z.2)
    (mul_nonneg (Nat.cast_nonneg _) hβ) (norm_sum_smul_wvecF_le hβ hJ hk he H) y

end Synthesis

/-! ## The Koszul cancellation -/

section Koszul

variable {W ι : Type*} [Fintype W] {r k : ℕ}

/-- Adjoining a vertex that is not below `b` leaves the position sign of `b`
unchanged. -/
theorem esign_insert_of_not_lt (L : Finset (Fin r)) {a b : Fin r} (hab : ¬a < b) :
    esign (insert a L) b = esign L b := by
  rw [esign, esign, Finset.filter_insert, if_neg hab]

/-- Adjoining a vertex below `b` reverses the position sign of `b`. -/
theorem esign_insert_of_lt {L : Finset (Fin r)} {a b : Fin r} (ha : a ∉ L) (hab : a < b) :
    esign (insert a L) b = -esign L b := by
  rw [esign, esign, Finset.filter_insert, if_pos hab,
    Finset.card_insert_of_notMem fun h => ha (Finset.mem_filter.mp h).1, pow_succ]
  ring

/-- **The sign lemma.**  For a face `L` and two vertices `u ≠ v` outside it, the
two ways of splitting `L ∪ \{u, v\}` into an adjoined vertex and a removed one
carry opposite signs.

Writing `a` for the number of elements of `L` below the smaller of `u, v` and `b`
for the number below the larger, the four signs are `(-1)^a`, `(-1)^b` for `L`,
and `(-1)^a`, `(-1)^{b+1}` for `L ∪ \{u, v\}`: the larger vertex acquires exactly
one extra element below it, namely the smaller one. -/
theorem esign_cancel {L : Finset (Fin r)} {j v : Fin r} (hj : j ∉ L) (hv : v ∉ L)
    (hjv : j ≠ v) :
    esign L j * esign (insert v (insert j L)) v
      + esign L v * esign (insert v (insert j L)) j = 0 := by
  rcases lt_or_gt_of_ne hjv with h | h
  · have h1 : esign (insert v (insert j L)) v = -esign L v := by
      rw [esign_insert_of_not_lt _ (lt_irrefl v), esign_insert_of_lt hj h]
    have h2 : esign (insert v (insert j L)) j = esign L j := by
      rw [esign_insert_of_not_lt _ (asymm h), esign_insert_of_not_lt _ (lt_irrefl j)]
    rw [h1, h2]
    ring
  · have hvS : v ∉ insert j L := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun hh => hjv hh.symm, hv⟩
    have h1 : esign (insert v (insert j L)) v = esign L v := by
      rw [esign_insert_of_not_lt _ (lt_irrefl v), esign_insert_of_not_lt _ (asymm h)]
    have h2 : esign (insert v (insert j L)) j = -esign L j := by
      rw [esign_insert_of_lt hvS h, esign_insert_of_not_lt _ (lt_irrefl j)]
    rw [h1, h2]
    ring

/-- The bilinear form of a symmetric operator on the conjugated frame is symmetric.
This is the mechanism of `inner_delta_placeQ_zetaV`, with the two `Q`-coordinates
replaced by the two vertices of `I ∖ L`. -/
theorem inner_mulVecE_ebar_symm {N : Matrix W W ℂ} (hN : Nᵀ = N)
    (e : Fin r → EuclideanSpace ℂ W) (a b : Fin r) :
    inner ℂ (e a) (mulVecE N (ebar e b)) = inner ℂ (e b) (mulVecE N (ebar e a)) := by
  rw [inner_mulVecE_ebar, inner_mulVecE_ebar, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hsym : N y x = N x y := by
    have hxy := congrFun (congrFun hN x) y
    rwa [Matrix.transpose_apply] at hxy
  rw [hsym]
  ring

/-- The incidence contributions of `I`, before the vanishing terms are discarded. -/
theorem mulVecE_placeT_etaMode_raw (N : Matrix W W ℂ) (e : Fin r → EuclideanSpace ℂ W)
    (I : Face r k) :
    mulVecE (placeT (T := Face r (k - 1)) N) (etaMode e I)
      = ((Real.sqrt k : ℝ) : ℂ)⁻¹ •
          ∑ v : Fin r, esign I.val v • placeAt (mulVecE N (ebar e v)) (I.val.erase v) := by
  rw [etaMode, mulVecE_smul_vec, mulVecE_sum_vec]
  refine congrArg _ (Finset.sum_congr rfl fun v _ => ?_)
  rw [mulVecE_smul_vec, mulVecE_placeT_placeAt]

/-- **Koszul cancellation.**  For a transpose-symmetric operator, every protected
mode is orthogonal to the image of every incidence mode.

A pair `(j, v)` contributes only when `L ∪ j = I ∖ v`, that is when `I ⊇ L` with
`I ∖ L = \{j, v\}`; the pairs then come in transposed couples `(j, v)`, `(v, j)`,
whose bilinear forms agree by symmetry of the operator and whose signs are
opposite by the sign lemma. -/
theorem inner_deltaMode_mulVecE_placeT_etaMode (hk : 2 ≤ k) {N : Matrix W W ℂ} (hN : Nᵀ = N)
    (e : Fin r → EuclideanSpace ℂ W) (L : Face r (k - 2)) (I : Face r k) :
    inner ℂ (deltaMode (k := k) e L)
      (mulVecE (placeT (T := Face r (k - 1)) N) (etaMode e I)) = 0 := by
  -- the summand vanishes unless `j ∉ L` and `L ∪ j = I ∖ v`
  have hP : ∀ j v : Fin r, ¬(j ∉ L.val ∧ insert j L.val = I.val.erase v) →
      inner ℂ (placeAt (e j) (insert j L.val) : EuclideanSpace ℂ (W × Face r (k - 1)))
        (placeAt (mulVecE N (ebar e v)) (I.val.erase v)) = 0 := by
    intro j v h
    by_cases hj : j ∈ L.val
    · have hc : (insert j L.val).card ≠ k - 1 := by
        rw [Finset.insert_eq_self.mpr hj, L.2]
        omega
      rw [placeAt_eq_zero _ hc, inner_zero_left]
    · have hc : (insert j L.val).card = k - 1 := by
        rw [Finset.card_insert_of_notMem hj, L.2]
        omega
      rw [inner_placeAt _ _ hc, if_neg fun hh => h ⟨hj, hh⟩]
  -- a contributing pair exhibits `I` as `L` with two vertices adjoined
  have hstruct : ∀ j v : Fin r, j ∉ L.val → insert j L.val = I.val.erase v →
      v ∉ L.val ∧ v ≠ j ∧ I.val = insert v (insert j L.val)
        ∧ insert v L.val = I.val.erase j := by
    intro j v hj h
    have hcins : (insert j L.val).card = k - 1 := by
      rw [Finset.card_insert_of_notMem hj, L.2]
      omega
    have hvI : v ∈ I.val := by
      by_contra hv
      rw [Finset.erase_eq_of_notMem hv] at h
      have hcc := congrArg Finset.card h
      rw [hcins, I.2] at hcc
      omega
    have hIeq : I.val = insert v (insert j L.val) := by rw [h, Finset.insert_erase hvI]
    have hvnot : v ∉ insert j L.val := by
      rw [h]
      exact Finset.notMem_erase v I.val
    have hvj : v ≠ j := fun hh => hvnot (by rw [hh]; exact Finset.mem_insert_self j L.val)
    have hvL : v ∉ L.val := fun hh => hvnot (Finset.mem_insert_of_mem hh)
    refine ⟨hvL, hvj, hIeq, ?_⟩
    rw [hIeq, Finset.erase_insert_of_ne hvj, Finset.erase_insert hj]
  -- the transposed pairs cancel
  have hcancel : ∀ j v : Fin r,
      esign L.val j * (esign I.val v *
          inner ℂ (placeAt (e j) (insert j L.val) : EuclideanSpace ℂ (W × Face r (k - 1)))
            (placeAt (mulVecE N (ebar e v)) (I.val.erase v)))
        + esign L.val v * (esign I.val j *
          inner ℂ (placeAt (e v) (insert v L.val) : EuclideanSpace ℂ (W × Face r (k - 1)))
            (placeAt (mulVecE N (ebar e j)) (I.val.erase j))) = 0 := by
    intro j v
    by_cases hc : j ∉ L.val ∧ insert j L.val = I.val.erase v
    · obtain ⟨hj, h⟩ := hc
      obtain ⟨hvL, hvj, hIeq, hj2⟩ := hstruct j v hj h
      have hcins : (insert j L.val).card = k - 1 := by
        rw [Finset.card_insert_of_notMem hj, L.2]
        omega
      have hcins2 : (insert v L.val).card = k - 1 := by
        rw [Finset.card_insert_of_notMem hvL, L.2]
        omega
      rw [inner_placeAt _ _ hcins, if_pos h, inner_placeAt _ _ hcins2, if_pos hj2,
        inner_mulVecE_ebar_symm hN e v j, hIeq]
      linear_combination
        (inner ℂ (e j) (mulVecE N (ebar e v)) : ℂ) * esign_cancel hj hvL (Ne.symm hvj)
    · have hc2 : ¬(v ∉ L.val ∧ insert v L.val = I.val.erase j) := by
        rintro ⟨hv, h2⟩
        obtain ⟨hjL, _, _, hj3⟩ := hstruct v j hv h2
        exact hc ⟨hjL, hj3⟩
      rw [hP j v hc, hP v j hc2]
      ring
  have key : ∑ j : Fin r, ∑ v : Fin r,
      esign L.val j * (esign I.val v *
        inner ℂ (placeAt (e j) (insert j L.val) : EuclideanSpace ℂ (W × Face r (k - 1)))
          (placeAt (mulVecE N (ebar e v)) (I.val.erase v))) = 0 := by
    have h2 : (∑ j : Fin r, ∑ v : Fin r, esign L.val j * (esign I.val v *
          inner ℂ (placeAt (e j) (insert j L.val) : EuclideanSpace ℂ (W × Face r (k - 1)))
            (placeAt (mulVecE N (ebar e v)) (I.val.erase v))))
        + (∑ j : Fin r, ∑ v : Fin r, esign L.val v * (esign I.val j *
          inner ℂ (placeAt (e v) (insert v L.val) : EuclideanSpace ℂ (W × Face r (k - 1)))
            (placeAt (mulVecE N (ebar e j)) (I.val.erase j)))) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun v _ => hcancel j v
    have hsw : (∑ j : Fin r, ∑ v : Fin r, esign L.val v * (esign I.val j *
          inner ℂ (placeAt (e v) (insert v L.val) : EuclideanSpace ℂ (W × Face r (k - 1)))
            (placeAt (mulVecE N (ebar e j)) (I.val.erase j))))
        = ∑ j : Fin r, ∑ v : Fin r, esign L.val j * (esign I.val v *
          inner ℂ (placeAt (e j) (insert j L.val) : EuclideanSpace ℂ (W × Face r (k - 1)))
            (placeAt (mulVecE N (ebar e v)) (I.val.erase v))) := Finset.sum_comm
    rw [hsw] at h2
    linear_combination h2 / 2
  rw [deltaMode, mulVecE_placeT_etaMode_raw, inner_smul_left, inner_smul_right, sum_inner]
  have hstep : ∀ j : Fin r,
      inner ℂ (esign L.val j • placeAt (e j) (insert j L.val)
          : EuclideanSpace ℂ (W × Face r (k - 1)))
        (∑ v : Fin r, esign I.val v • placeAt (mulVecE N (ebar e v)) (I.val.erase v))
      = ∑ v : Fin r, esign L.val j * (esign I.val v *
          inner ℂ (placeAt (e j) (insert j L.val) : EuclideanSpace ℂ (W × Face r (k - 1)))
            (placeAt (mulVecE N (ebar e v)) (I.val.erase v))) := fun j => by
    rw [inner_smul_left, conj_esign, inner_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [inner_smul_right]
  rw [Finset.sum_congr rfl fun j _ => hstep j, key, mul_zero, mul_zero]

/-- Transpose symmetry of the Kraus operators makes every frame vector orthogonal
to every protected mode. -/
theorem inner_deltaMode_wvecF (hk : 2 ≤ k) {A : ι → Matrix W W ℂ} (hsym : ∀ f, (A f)ᵀ = A f)
    (e : Fin r → EuclideanSpace ℂ W) (H : Finset (Face r k)) (L : Face r (k - 2))
    (f : ι) (I : Face r k) : inner ℂ (deltaMode (k := k) e L) (wvecF A e H f I) = 0 := by
  rw [wvecF]
  split
  · exact inner_deltaMode_mulVecE_placeT_etaMode hk (hsym f) e L I
  · exact inner_zero_right _

variable [Fintype ι]

/-- **Theorem B.**  `(Φ_A ⊗ id)(P_H) ⪯ d↑_{k-1}(H) β (I − Π)`, where `Π` is the
orthogonal projection onto the span of the protected modes.

This improves on Theorem A by the `binom(r, k-2)` dimensions of that span, and
transpose symmetry of the Kraus operators is what supplies them: the Koszul
cancellation makes every frame vector orthogonal to every `δ_L`, so the Bessel
sum sees only the component of `y` off their span. -/
theorem qform_krausF_Phyp_le {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiKBound (choiOf A) k β) (hsym : ∀ f, (A f)ᵀ = A f) (hk : 2 ≤ k) (hkr : k ≤ r)
    {e : Fin r → EuclideanSpace ℂ W} (he : Orthonormal ℂ e) (H : Finset (Face r k))
    (y : EuclideanSpace ℂ (W × Face r (k - 1))) :
    (qform (krausF A (Phyp e H)) y).re
      ≤ (upDeg H : ℝ) * β * (‖y‖ ^ 2
          - ∑ L : Face r (k - 2), Complex.normSq (inner ℂ (deltaMode (k := k) e L) y)) := by
  have hbess : ∀ z : EuclideanSpace ℂ (W × Face r (k - 1)),
      ∑ w : ι × Face r k, Complex.normSq (inner ℂ (wvecF A e H w.1 w.2) z)
        ≤ (upDeg H : ℝ) * β * ‖z‖ ^ 2 := fun z => by
    rw [← re_qform_krausF_Phyp]
    exact qform_krausF_Phyp_le_of_norm hβ hJ (by omega) he H z
  rw [re_qform_krausF_Phyp]
  exact frame_le_sub_proj_family (w := fun w : ι × Face r k => wvecF A e H w.1 w.2)
    (z := deltaMode (k := k) e) (M := (upDeg H : ℝ) * β) (orthonormal_deltaMode he hk hkr)
    (fun L w => inner_deltaMode_wvecF hk hsym e H L w.1 w.2) hbess y

end Koszul

/-! ## Pair amplification

The specialization to `k = 2`, where the incidence modes are the antisymmetric
combinations of the pair sector, the protected modes reduce to the single vector
`δ_e`, and the complete graph has `d↑₁ = r − 1`. -/

section PairLevel

variable {W ι : Type*} {r k : ℕ}

/-- At `k = 2` the incidence mode of the edge `{i, j}` is the normalized
antisymmetric combination `(ē_i ⊗ q_j − ē_j ⊗ q_i)/√2` of the pair sector. -/
theorem etaMode_two (e : Fin r → EuclideanSpace ℂ W) {i j : Fin r} (hij : i < j)
    (hc : ({i, j} : Finset (Fin r)).card = 2) :
    etaMode e (⟨{i, j}, hc⟩ : Face r 2)
      = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (placeAt (ebar e i) {j} - placeAt (ebar e j) {i}) := by
  have hne : i ≠ j := ne_of_lt hij
  have hsi : esign ({i, j} : Finset (Fin r)) i = 1 := by
    rw [esign, Finset.filter_insert, if_neg (lt_irrefl i), Finset.filter_singleton,
      if_neg (asymm hij), Finset.card_empty, pow_zero]
  have hsj : esign ({i, j} : Finset (Fin r)) j = -1 := by
    rw [esign, Finset.filter_insert, if_pos hij, Finset.filter_singleton, if_neg (lt_irrefl j),
      Finset.card_insert_of_notMem (Finset.notMem_empty i), Finset.card_empty]
    norm_num
  have hei : ({i, j} : Finset (Fin r)).erase i = {j} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.2.resolve_left h.1, fun h => ⟨h ▸ hne.symm, Or.inr h⟩⟩
  have hej : ({i, j} : Finset (Fin r)).erase j = {i} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.2.resolve_right h.1, fun h => ⟨h ▸ hne, Or.inl h⟩⟩
  have hsub : ({i, j} : Finset (Fin r)) ⊆ Finset.univ := Finset.subset_univ _
  have hzero : ∀ v ∈ (Finset.univ : Finset (Fin r)), v ∉ ({i, j} : Finset (Fin r)) →
      esign ({i, j} : Finset (Fin r)) v •
          (placeAt (ebar e v) (({i, j} : Finset (Fin r)).erase v)
            : EuclideanSpace ℂ (W × Face r 1)) = 0 := by
    intro v _ hv
    have hcz : ((({i, j} : Finset (Fin r))).erase v).card ≠ 1 := by
      rw [Finset.erase_eq_of_notMem hv, hc]
      omega
    rw [placeAt_eq_zero _ hcz, smul_zero]
  rw [etaMode, ← Finset.sum_subset hsub hzero, Finset.sum_pair hne, hsi, hsj, hei, hej,
    one_smul, neg_one_smul, ← sub_eq_add_neg]
  norm_num

/-- At `k = 2` the only protected mode is the normalized `δ_e`. -/
theorem deltaMode_two (hr : 2 ≤ r) (e : Fin r → EuclideanSpace ℂ W) (L : Face r 0) :
    deltaMode (k := 2) e L
      = ((Real.sqrt r : ℝ) : ℂ)⁻¹ • ∑ j : Fin r, placeAt (e j) {j} := by
  have hL : L.val = ∅ := Finset.card_eq_zero.mp L.2
  rw [deltaMode, show (r - 2 + 2 : ℕ) = r from by omega]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [hL, esign, Finset.filter_empty, Finset.card_empty, pow_zero, one_smul,
    Finset.insert_empty]

/-- Every `(k-1)`-face extends to a `k`-face in exactly `r − k + 1` ways: the
extension is the choice of one vertex outside the face. -/
theorem card_filter_subset_univ (hk : 1 ≤ k) (hkr : k ≤ r) (J : Face r (k - 1)) :
    ((Finset.univ : Finset (Face r k)).filter fun I => J.val ⊆ I.val).card = r - k + 1 := by
  have hcard : ∀ v : {v : Fin r // v ∈ J.valᶜ}, (insert v.1 J.val).card = k := fun v => by
    rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp v.2), J.2]
    omega
  set f : {v : Fin r // v ∈ J.valᶜ} → Face r k := fun v => ⟨insert v.1 J.val, hcard v⟩ with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have h : insert a.1 J.val = insert b.1 J.val := congrArg Subtype.val hab
    have hmem : a.1 ∈ insert b.1 J.val := by
      rw [← h]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hmem with h1 | h1
    · exact Subtype.ext h1
    · exact absurd h1 (Finset.mem_compl.mp a.2)
  have himg : (Finset.univ : Finset (Face r k)).filter (fun I => J.val ⊆ I.val)
      = J.valᶜ.attach.image f := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hsub
      have hlt : J.val ⊂ I.val := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun hh => ?_⟩
        have hcc := congrArg Finset.card hh
        rw [J.2, I.2] at hcc
        omega
      obtain ⟨v, hvI, hvJ⟩ := Finset.exists_of_ssubset hlt
      refine ⟨⟨v, Finset.mem_compl.mpr hvJ⟩, Finset.mem_attach _ _, Subtype.ext ?_⟩
      exact Finset.eq_of_subset_of_card_le (Finset.insert_subset hvI hsub)
        (by rw [hcard ⟨v, Finset.mem_compl.mpr hvJ⟩, I.2])
    · rintro ⟨v, _, rfl⟩
      exact Finset.subset_insert _ _
  rw [himg, Finset.card_image_of_injective _ hfinj, Finset.card_attach, Finset.card_compl, J.2,
    Fintype.card_fin]
  omega

/-- The complete `k`-uniform hypergraph has `d↑_{k-1} = r − k + 1`. -/
theorem upDeg_univ (hk : 1 ≤ k) (hkr : k ≤ r) :
    upDeg (Finset.univ : Finset (Face r k)) = r - k + 1 := by
  have hne : (Finset.univ : Finset (Face r (k - 1))).Nonempty := by
    obtain ⟨t, _, ht⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin r))) (n := k - 1) (by simp; omega)
    exact ⟨⟨t, ht⟩, Finset.mem_univ _⟩
  have hsup : (Finset.univ : Finset (Face r (k - 1))).sup
      (fun J => ((Finset.univ : Finset (Face r k)).filter fun I => J.val ⊆ I.val).card)
      = (Finset.univ : Finset (Face r (k - 1))).sup (fun _ => r - k + 1) :=
    Finset.sup_congr rfl fun J _ => card_filter_subset_univ hk hkr J
  rw [upDeg, hsup, Finset.sup_const hne]

variable [Fintype W] [Fintype ι]

/-- **Pair amplification.**  Theorem A at `k = 2` on the complete graph reads
`(Φ_A ⊗ id)(P₋) ⪯ (r−1)β I` for the normalized antisymmetric modes, which is the
`2β(r−1)` of `qform_krausQ_Pneg_le_of_norm` because `Pneg` carries the
unnormalized `ζ_{ij}`, of squared norm two. -/
theorem qform_krausF_Phyp_le_of_choiTwoBound {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β) (hr : 2 ≤ r) {e : Fin r → EuclideanSpace ℂ W}
    (he : Orthonormal ℂ e) (y : EuclideanSpace ℂ (W × Face r 1)) :
    (qform (krausF A (Phyp e (Finset.univ : Finset (Face r 2)))) y).re
      ≤ ((r : ℝ) - 1) * β * ‖y‖ ^ 2 := by
  have h := qform_krausF_Phyp_le_of_norm hβ (choiTwoBound_iff_choiKBound_two.mp hJ)
    (by omega) he (Finset.univ : Finset (Face r 2)) y
  rw [upDeg_univ (by omega) hr] at h
  have hc : ((r - 2 + 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [show r - 2 + 1 = r - 1 from by omega, Nat.cast_sub (by omega)]
    norm_num
  rwa [hc] at h

/-- **Pair amplification, protected form.**  Theorem B at `k = 2` on the complete
graph: transpose symmetry of the Kraus operators protects the single mode
`δ_∅ = δ_e/√r`, which is the `‖y‖² − |⟪δ_e, y⟫|²/r` of
`qform_krausQ_Pneg_le`. -/
theorem qform_krausF_Phyp_le_of_choiTwoBound_sub {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β) (hsym : ∀ f, (A f)ᵀ = A f) (hr : 2 ≤ r)
    {e : Fin r → EuclideanSpace ℂ W} (he : Orthonormal ℂ e)
    (y : EuclideanSpace ℂ (W × Face r 1)) :
    (qform (krausF A (Phyp e (Finset.univ : Finset (Face r 2)))) y).re
      ≤ ((r : ℝ) - 1) * β * (‖y‖ ^ 2
          - ∑ L : Face r 0, Complex.normSq (inner ℂ (deltaMode (k := 2) e L) y)) := by
  have h := qform_krausF_Phyp_le hβ (choiTwoBound_iff_choiKBound_two.mp hJ) hsym (by omega) hr
    he (Finset.univ : Finset (Face r 2)) y
  rw [upDeg_univ (by omega) hr] at h
  have hc : ((r - 2 + 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [show r - 2 + 1 = r - 1 from by omega, Nat.cast_sub (by omega)]
    norm_num
  rwa [hc] at h

end PairLevel

end RankR
