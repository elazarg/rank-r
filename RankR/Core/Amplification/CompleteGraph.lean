/-
Synthesis of the sum-of-squares vector `T` from edge data on the complete graph.

Each unordered pair `i < j` of indices carries a matrix `K_{ij}` on `W`; the
operator `K_{ij} ⊗ I_Q` is applied to the antisymmetric combination
`ζ_{ij} = ε_{ij} - ε_{ji}` and the results are summed over all edges.  Because
`ε_{jk}` is supported on the single `Q`-coordinate `k`, the edge `(i, j)`
deposits `+K_{ij} ēᵢ` at coordinate `j` and `-K_{ij} ēⱼ` at coordinate `i`.
Regrouping by `Q`-coordinate therefore turns the edge sum into a vector of the
form `δ` whose `k`-th block is a signed sum over the `s - 1` edges incident to
`k`.  Cauchy-Schwarz on each such block bounds `‖T‖²` by `(s - 1)` times the
total edge weight.

The combinatorics is that of the complete graph on the `s` ancilla coordinates,
and the edge data is a family of operators on one space `W`.  Section 3 reads it
at `W = U ⊗ V`.
-/
import RankR.Core.Amplification.Sectors
import RankR.Library.Matrix.Conjugate
import RankR.Library.Matrix.Placement

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

/-! ## Generic tools -/

section Tools

variable {W : Type*} [Fintype W]

/-! The two lemmas below push an operation through the *matrix* slot of
`mulVecE`; the vector-slot family lives in `Kraus.lean`, at the definition. -/

/-- Matrix-vector multiplication is additive in the matrix. -/
theorem sum_mulVecE {ι : Type*} [Fintype ι] (A : ι → Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    mulVecE (∑ i, A i) x = ∑ i, mulVecE (A i) x := by
  ext p
  rw [mulVecE_apply, sum_apply_euclidean]
  simp only [mulVecE_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Matrix-vector multiplication is homogeneous in the matrix. -/
theorem smul_mulVecE (c : ℂ) (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    mulVecE (c • A) x = c • mulVecE A x := by
  ext p
  rw [mulVecE_apply]
  simp only [PiLp.smul_apply, mulVecE_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc]

end Tools

/-! ## Edges of the complete graph -/

section EdgeSet

variable {s : ℕ}

/-- The edge set of the complete graph on `Fin s`, realized as the ordered pairs
`(i, j)` with `i < j`. -/
def Edges : Finset (Fin s × Fin s) := Finset.univ.filter (fun p => p.1 < p.2)

/-- Unfolding lemma for the edge set. -/
theorem Edges_def : (Edges : Finset (Fin s × Fin s)) = Finset.univ.filter (fun p => p.1 < p.2) :=
  rfl

/-- Membership in the edge set is the strict inequality between the two components. -/
theorem mem_Edges {p : Fin s × Fin s} : p ∈ (Edges : Finset (Fin s × Fin s)) ↔ p.1 < p.2 := by
  simp [Edges]

/-- Selecting, inside an edge sum, the edges whose head is `k` leaves a sum over
the indices below `k`. -/
theorem sum_Edges_ite_snd {M : Type*} [AddCommMonoid M] (k : Fin s) (F : Fin s → Fin s → M) :
    ∑ q ∈ Edges, (if k = q.2 then F q.1 q.2 else 0)
      = ∑ i ∈ Finset.univ.filter (fun i => i < k), F i k := by
  rw [Edges, Finset.sum_filter, Fintype.sum_prod_type]
  have h : ∀ i : Fin s, (∑ j, if i < j then (if k = j then F i j else 0) else 0)
      = if i < k then F i k else 0 := by
    intro i
    have h' : ∀ j : Fin s, (if i < j then (if k = j then F i j else 0) else 0)
        = if k = j then (if i < k then F i k else 0) else 0 := by
      intro j
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [hkj]
    rw [Finset.sum_congr rfl fun j _ => h' j, Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_filter]

/-- Selecting, inside an edge sum, the edges whose tail is `k` leaves a sum over
the indices above `k`. -/
theorem sum_Edges_ite_fst {M : Type*} [AddCommMonoid M] (k : Fin s) (F : Fin s → Fin s → M) :
    ∑ q ∈ Edges, (if k = q.1 then F q.1 q.2 else 0)
      = ∑ j ∈ Finset.univ.filter (fun j => k < j), F k j := by
  rw [Edges, Finset.sum_filter, Fintype.sum_prod_type]
  have h : ∀ i : Fin s, (∑ j, if i < j then (if k = i then F i j else 0) else 0)
      = if k = i then ∑ j ∈ Finset.univ.filter (fun j => i < j), F i j else 0 := by
    intro i
    by_cases hki : k = i
    · subst hki; simp [Finset.sum_filter]
    · simp [hki]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_ite_eq]
  simp

end EdgeSet

/-! ## Conjugate vectors and `Q`-placed elementary vectors -/

section Placed

variable {W : Type*} {s : ℕ}

/-- The entrywise complex conjugate `ēᵢ` of the vector `eᵢ`. -/
def ebar (e : Fin s → EuclideanSpace ℂ W) (i : Fin s) : EuclideanSpace ℂ W :=
  WithLp.toLp 2 (fun p => conj (e i p))

@[simp] theorem ebar_apply (e : Fin s → EuclideanSpace ℂ W) (i : Fin s) (p : W) :
    ebar e i p = conj (e i p) := rfl

/-- `v ⊗ q_k`: the vector `v` on `W` placed at the `k`-th `Q`-coordinate. -/
def epsOf (v : EuclideanSpace ℂ W) (k : Fin s) : EuclideanSpace ℂ (W × Fin s) :=
  WithLp.toLp 2 (fun x => if x.2 = k then v x.1 else 0)

@[simp] theorem epsOf_apply (v : EuclideanSpace ℂ W) (k : Fin s) (x : W × Fin s) :
    epsOf v k x = if x.2 = k then v x.1 else 0 := rfl

/-- `ε_{jk}` is the `k`-th placement of the conjugate vector `ē_j`. -/
theorem eps_eq_epsOf (e : Fin s → EuclideanSpace ℂ W) (j k : Fin s) :
    eps e j k = epsOf (ebar e j) k := rfl

end Placed

section Synth

variable {W : Type*} [Fintype W] {s : ℕ}

/-- `(N ⊗ I_Q)(v ⊗ q_k) = (N v) ⊗ q_k`: an operator acting trivially on `Q`
preserves the `Q`-coordinate of a placed vector. -/
theorem mulVecE_placeT_epsOf (N : Matrix W W ℂ) (v : EuclideanSpace ℂ W) (k : Fin s) :
    mulVecE (placeT N) (epsOf v k) = epsOf (mulVecE N v) k := by
  ext x
  rw [mulVecE_apply, epsOf_apply, mulVecE_apply, Fintype.sum_prod_type]
  have h : ∀ q : W, (∑ m, placeT N x (q, m) * epsOf v k (q, m))
      = if x.2 = k then N x.1 q * v q else 0 := by
    intro q
    have h' : ∀ m : Fin s, placeT N x (q, m) * epsOf v k (q, m)
        = if m = k then (if x.2 = k then N x.1 q * v q else 0) else 0 := by
      intro m
      by_cases hmk : m = k
      · subst hmk; by_cases hx : x.2 = m <;> simp [hx]
      · simp [hmk]
    rw [Finset.sum_congr rfl fun m _ => h' m, Finset.sum_ite_eq']
    simp
  rw [Finset.sum_congr rfl fun q _ => h q]
  by_cases hx : x.2 = k
  · simp [hx]
  · simp [hx]

/-! ## The synthesized vector and its vertex blocks -/

/-- `T = ∑_{i < j} (K_{ij} ⊗ I_Q) ζ_{ij}`, the vector synthesized from the edge
data `K`. -/
noncomputable def Tsyn (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) : EuclideanSpace ℂ (W × Fin s) :=
  ∑ p ∈ Edges, mulVecE (placeT (K p.1 p.2)) (zetaV e p.1 p.2)

/-- The edge `(i, j)` contributes `+K_{ij} ēᵢ` at `Q`-coordinate `j` and
`-K_{ij} ēⱼ` at `Q`-coordinate `i`. -/
theorem mulVecE_placeT_zetaV (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) (i j : Fin s) :
    mulVecE (placeT (K i j)) (zetaV e i j)
      = epsOf (mulVecE (K i j) (ebar e i)) j - epsOf (mulVecE (K i j) (ebar e j)) i := by
  rw [zetaV, eps_eq_epsOf, eps_eq_epsOf, mulVecE_sub, mulVecE_placeT_epsOf,
    mulVecE_placeT_epsOf]

/-- The `k`-th vertex block of `T`: the signed sum of the edge contributions of
all edges incident to `k`. -/
noncomputable def vtx (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) (k : Fin s) : EuclideanSpace ℂ W :=
  (∑ i ∈ Finset.univ.filter (fun i => i < k), mulVecE (K i k) (ebar e i))
    - (∑ j ∈ Finset.univ.filter (fun j => k < j), mulVecE (K k j) (ebar e j))

/-- `eq:T-by-vertices`: regrouping the edge sum by `Q`-coordinate exhibits `T` as
the vector `δ` assembled from the vertex blocks. -/
theorem Tsyn_eq_delta_vtx (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) : Tsyn e K = delta (vtx e K) := by
  ext x
  rw [Tsyn, sum_apply_euclidean, delta_apply, vtx, PiLp.sub_apply, sum_apply_euclidean,
    sum_apply_euclidean]
  have h : ∀ q : Fin s × Fin s, mulVecE (placeT (K q.1 q.2)) (zetaV e q.1 q.2) x
      = (if x.2 = q.2 then mulVecE (K q.1 q.2) (ebar e q.1) x.1 else 0)
        - (if x.2 = q.1 then mulVecE (K q.1 q.2) (ebar e q.2) x.1 else 0) := by
    intro q
    rw [mulVecE_placeT_zetaV, PiLp.sub_apply, epsOf_apply, epsOf_apply]
  rw [Finset.sum_congr rfl fun q _ => h q, Finset.sum_sub_distrib,
    sum_Edges_ite_snd x.2 (fun i j => mulVecE (K i j) (ebar e i) x.1),
    sum_Edges_ite_fst x.2 (fun i j => mulVecE (K i j) (ebar e j) x.1)]

/-! ## The norm bound -/

/-- The contribution of the edge `{k, m}` to the vertex block at `k`, with its
sign; it vanishes when `m = k`. -/
noncomputable def vtxTerm (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) (k m : Fin s) : EuclideanSpace ℂ W :=
  if m < k then mulVecE (K m k) (ebar e m)
  else if k < m then -(mulVecE (K k m) (ebar e m)) else 0

@[simp] theorem vtxTerm_self (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) (k : Fin s) : vtxTerm e K k k = 0 := by
  simp [vtxTerm]

/-- The vertex block at `k` is the sum of the `s - 1` incident edge terms. -/
theorem vtx_eq_sum_vtxTerm (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) (k : Fin s) :
    vtx e K k = ∑ m, vtxTerm e K k m := by
  have h : ∀ m : Fin s, vtxTerm e K k m
      = (if m < k then mulVecE (K m k) (ebar e m) else 0)
        + (if k < m then -(mulVecE (K k m) (ebar e m)) else 0) := by
    intro m
    rcases lt_trichotomy m k with hm | hm | hm
    · simp [vtxTerm, hm, asymm hm]
    · simp [vtxTerm, hm]
    · simp [vtxTerm, hm, asymm hm]
  rw [Finset.sum_congr rfl fun m _ => h m, Finset.sum_add_distrib, ← Finset.sum_filter,
    ← Finset.sum_filter, vtx, sub_eq_add_neg, Finset.sum_neg_distrib]

/-- Cauchy-Schwarz on the `s - 1` incident edge terms of a single vertex block. -/
theorem norm_vtx_sq_le (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) (k : Fin s) :
    ‖vtx e K k‖ ^ 2 ≤ ((s : ℝ) - 1) * ∑ m, ‖vtxTerm e K k m‖ ^ 2 := by
  have hs : 1 ≤ s := k.pos
  set T : Finset (Fin s) := Finset.univ.filter (fun m => m ≠ k) with hT
  have hsub : T ⊆ Finset.univ := Finset.filter_subset _ _
  have hzero : ∀ m ∈ Finset.univ, m ∉ T → vtxTerm e K k m = 0 := by
    intro m _ hm
    have : m = k := by simpa [hT] using hm
    simp [this]
  have hcard : (T.card : ℝ) = (s : ℝ) - 1 := by
    have h1 : T = Finset.univ.erase k := by rw [hT]; exact Finset.filter_ne' _ _
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub hs, Nat.cast_one]
  have hsum : ∑ m ∈ T, ‖vtxTerm e K k m‖ ^ 2 = ∑ m, ‖vtxTerm e K k m‖ ^ 2 :=
    Finset.sum_subset hsub fun m hm hm' => by rw [hzero m hm hm', norm_zero, zero_pow two_ne_zero]
  have h1 : ‖vtx e K k‖ ≤ ∑ m ∈ T, ‖vtxTerm e K k m‖ := by
    rw [vtx_eq_sum_vtxTerm, ← Finset.sum_subset hsub hzero]
    exact norm_sum_le _ _
  have h2 : (∑ m ∈ T, ‖vtxTerm e K k m‖) ^ 2 ≤ (T.card : ℝ) * ∑ m ∈ T, ‖vtxTerm e K k m‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := T) (f := fun m => ‖vtxTerm e K k m‖)
  have h3 : (0 : ℝ) ≤ ∑ m ∈ T, ‖vtxTerm e K k m‖ :=
    Finset.sum_nonneg fun m _ => norm_nonneg _
  rw [← hsum, ← hcard]
  nlinarith [norm_nonneg (vtx e K k)]

/-- Summing the squared edge terms over all vertices counts each edge twice, once
through each of its endpoints. -/
theorem sum_sum_vtxTerm_sq (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) :
    ∑ k, ∑ m, ‖vtxTerm e K k m‖ ^ 2
      = ∑ p ∈ Edges, (‖mulVecE (K p.1 p.2) (ebar e p.1)‖ ^ 2
          + ‖mulVecE (K p.1 p.2) (ebar e p.2)‖ ^ 2) := by
  rw [← sum_split_lt (fun k m => ‖vtxTerm e K k m‖ ^ 2), Edges_def]
  have hdiag : ∀ k : Fin s, ‖vtxTerm e K k k‖ ^ 2 = 0 := by
    intro k; simp
  have hoff : ∀ p ∈ Finset.univ.filter (fun p : Fin s × Fin s => p.1 < p.2),
      ‖vtxTerm e K p.1 p.2‖ ^ 2 + ‖vtxTerm e K p.2 p.1‖ ^ 2
        = ‖mulVecE (K p.1 p.2) (ebar e p.1)‖ ^ 2
          + ‖mulVecE (K p.1 p.2) (ebar e p.2)‖ ^ 2 := by
    intro p hp
    have hlt : p.1 < p.2 := by simpa using hp
    rw [show vtxTerm e K p.1 p.2 = -(mulVecE (K p.1 p.2) (ebar e p.2)) by
        simp [vtxTerm, hlt, asymm hlt],
      show vtxTerm e K p.2 p.1 = mulVecE (K p.1 p.2) (ebar e p.1) by simp [vtxTerm, hlt],
      norm_neg]
    exact add_comm _ _
  rw [Finset.sum_congr rfl fun k _ => hdiag k, Finset.sum_const_zero, zero_add,
    Finset.sum_congr rfl hoff]

/-- The sum-of-squares bound: `‖T‖²` is at most `s - 1` times the total edge
weight, the vertex-variance terms of the exact identity being dropped. -/
theorem norm_Tsyn_sq_le (e : Fin s → EuclideanSpace ℂ W)
    (K : Fin s → Fin s → Matrix W W ℂ) :
    ‖Tsyn e K‖ ^ 2
      ≤ ((s : ℝ) - 1) * ∑ p ∈ Edges, (‖mulVecE (K p.1 p.2) (ebar e p.1)‖ ^ 2
          + ‖mulVecE (K p.1 p.2) (ebar e p.2)‖ ^ 2) := by
  rw [Tsyn_eq_delta_vtx, norm_delta, ← sum_sum_vtxTerm_sq, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => norm_vtx_sq_le e K k

end Synth

end RankR
