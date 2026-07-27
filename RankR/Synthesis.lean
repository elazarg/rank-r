/-
The synthesis bound for the frame `w` of `Assemble.lean`.

A coefficient vector `c` indexed by pairs (Kraus index, ordered pair of frame
indices) synthesizes the vector `∑_k c_k w_k`.  Because the Kraus operators of
`Phi4` are the elementary double-skew tensors placed trivially on `Q`, collecting
the Kraus index first turns the synthesized vector into `T` for the edge data
`K_{ij} = ∑_{abuv} c_{abuv,ij} (E_{ab} - E_{ba}) ⊗ (E_{uv} - E_{vu})`, an element
of `so(U) ⊗ so(V)`.  The edgewise double-skew bound and the Hilbert-Schmidt
coefficient bound then combine with the `s - 1` factor of the vertex regrouping
into the uniform estimate `‖∑_k c_k w_k‖² ≤ 8 (s - 1) ∑_k |c_k|²`, which is the
hypothesis of `frame_le_of_synthesis_le`.
-/
import RankR.Bessel
import RankR.Assemble

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

/-! ## Linearity of the two elementary constructions -/

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
/-- Placing an operator on `Q` is additive: it commutes with finite sums. -/
theorem placeQ_sum {ι : Type*} [Fintype ι] (A : ι → Matrix (U × V) (U × V) ℂ) :
    placeQ (s := s) (∑ i, A i) = ∑ i, placeQ (s := s) (A i) := by
  ext x y
  simp only [placeQ_apply, Matrix.sum_apply]
  split_ifs with h
  · rfl
  · exact Finset.sum_const_zero.symm

omit [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] in
/-- Placing an operator on `Q` is homogeneous: it commutes with scalar multiples. -/
theorem placeQ_smul (c : ℂ) (A : Matrix (U × V) (U × V) ℂ) :
    placeQ (s := s) (c • A) = c • placeQ (s := s) A := by
  ext x y
  simp only [placeQ_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_zero]

/-- Matrix-vector multiplication is additive in the matrix. -/
theorem mulVecE_sum {W : Type*} [Fintype W] {ι : Type*} [Fintype ι] (A : ι → Matrix W W ℂ)
    (x : EuclideanSpace ℂ W) : mulVecE (∑ i, A i) x = ∑ i, mulVecE (A i) x := by
  ext p
  rw [mulVecE_apply, sum_apply_euclidean]
  simp only [mulVecE_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Matrix-vector multiplication is homogeneous in the matrix. -/
theorem mulVecE_smul {W : Type*} [Fintype W] (c : ℂ) (A : Matrix W W ℂ)
    (x : EuclideanSpace ℂ W) : mulVecE (c • A) x = c • mulVecE A x := by
  ext p
  rw [mulVecE_apply]
  simp only [PiLp.smul_apply, mulVecE_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc]

/-! ## The edge data attached to a coefficient vector -/

/-- The edge matrix synthesized from the coefficients carried by the ordered pair
`(i, j)`: the double-skew combination whose coefficients are `c` restricted to
that pair. -/
noncomputable def Kof (c : KIdx U V × (Fin s × Fin s) → ℂ) (i j : Fin s) :
    Matrix (U × V) (U × V) ℂ :=
  skewCombo (fun a b u v => c (((a, b), (u, v)), (i, j)))

/-- Every edge matrix `Kof c i j` lies in the double-skew subspace, being a linear
combination of tensors of elementary skew matrices. -/
theorem Kof_mem_doubleSkew (c : KIdx U V × (Fin s × Fin s) → ℂ) (i j : Fin s) :
    Kof c i j ∈ doubleSkew U V := by
  have h := sum_smul_kron_mem_doubleSkew (U := U) (V := V) (ι := U × U) (κ := V × V)
    (fun q r => c (((q.1, q.2), (r.1, r.2)), (i, j)))
    (fun q => skewUnit q.1 q.2) (fun r => skewUnit r.1 r.2)
    (fun q => skewUnit_isSkew q.1 q.2) (fun r => skewUnit_isSkew r.1 r.2)
  simpa [Kof, skewCombo, Fintype.sum_prod_type] using h

/-- Contracting the Kraus operators against the coefficients of a single ordered
pair produces the placed edge matrix. -/
theorem sum_smul_kop (c : KIdx U V × (Fin s × Fin s) → ℂ) (p : Fin s × Fin s) :
    ∑ f : KIdx U V, c (f, p) • kop (s := s) f = placeQ (Kof c p.1 p.2) := by
  simp only [kop, Kof, skewCombo, placeQ_sum, placeQ_smul, Fintype.sum_prod_type, Prod.mk.eta]

/-! ## The synthesis identity -/

/-- Synthesizing the frame `w` with coefficients `c` produces exactly the vector
`T` of the edge data `Kof c`: summing over the Kraus index first assembles the
double-skew combination, and the vanishing of `w` off the edge set restricts the
remaining sum to the edges. -/
theorem sum_smul_wvec (e : Fin s → EuclideanSpace ℂ (U × V))
    (c : KIdx U V × (Fin s × Fin s) → ℂ) :
    ∑ k : KIdx U V × (Fin s × Fin s), c k • wvec e k.1 k.2 = Tsyn e (Kof c) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Tsyn, Edges_def, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p.1 < p.2
  · simp only [wvec, h, if_true]
    rw [← sum_smul_kop c p, mulVecE_sum]
    exact Finset.sum_congr rfl fun f _ => (mulVecE_smul _ _ _).symm
  · simp [wvec, h]

/-! ## The synthesis bound -/

/-- The uniform synthesis bound for the frame `w`.

The synthesized vector is `T` for edge data lying in `so(U) ⊗ so(V)`, so the
vertex regrouping contributes a factor `s - 1`, the double-skew bound halves each
edge weight, and the Hilbert-Schmidt coefficient bound costs a factor `16`; the
product of the three constants is `8 (s - 1)`.  When `s < 2` there are no edges
and both sides vanish. -/
theorem norm_sum_smul_wvec_le (hFGP : DoubleSkewBound U V)
    {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (c : KIdx U V × (Fin s × Fin s) → ℂ) :
    ‖∑ k : KIdx U V × (Fin s × Fin s), c k • wvec e k.1 k.2‖ ^ 2
      ≤ 8 * ((s : ℝ) - 1) * ∑ k : KIdx U V × (Fin s × Fin s), Complex.normSq (c k) := by
  rw [sum_smul_wvec]
  rcases Nat.lt_or_ge s 2 with hs | hs
  · have hE : (Edges : Finset (Fin s × Fin s)) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      have h1 : (p.1 : ℕ) < (p.2 : ℕ) := mem_Edges.1 hp
      have h2 : (p.2 : ℕ) < s := p.2.isLt
      omega
    have hT : Tsyn e (Kof c) = 0 := by rw [Tsyn, hE, Finset.sum_empty]
    rw [hT, norm_zero]
    have hz : s = 0 ∨ s = 1 := by omega
    rcases hz with rfl | rfl
    · simp
    · norm_num
  · have hs1 : (0 : ℝ) ≤ (s : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      linarith
    have hsum : ∑ k : KIdx U V × (Fin s × Fin s), Complex.normSq (c k)
        = ∑ p : Fin s × Fin s, ∑ a, ∑ b, ∑ u, ∑ v,
            Complex.normSq (c (((a, b), (u, v)), p)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => by simp only [Fintype.sum_prod_type]
    calc ‖Tsyn e (Kof c)‖ ^ 2
        ≤ ((s : ℝ) - 1) * ∑ p ∈ Edges, (‖mulVecE (Kof c p.1 p.2) (ebar e p.1)‖ ^ 2
            + ‖mulVecE (Kof c p.1 p.2) (ebar e p.2)‖ ^ 2) := norm_Tsyn_sq_le e (Kof c)
      _ ≤ ((s : ℝ) - 1) * ∑ p ∈ Edges, hsNormSq (Kof c p.1 p.2) / 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp => ?_) hs1
          exact edge_double_skew hFGP he (Kof_mem_doubleSkew c p.1 p.2)
            (ne_of_lt (mem_Edges.1 hp))
      _ ≤ ((s : ℝ) - 1) * ∑ p ∈ Edges, 8 * ∑ a, ∑ b, ∑ u, ∑ v,
            Complex.normSq (c (((a, b), (u, v)), p)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => ?_) hs1
          have h := hsNormSq_skewCombo_le (fun a b u v => c (((a, b), (u, v)), p))
          have hK : Kof c p.1 p.2 = skewCombo (fun a b u v => c (((a, b), (u, v)), p)) := rfl
          rw [hK]
          linarith
      _ ≤ ((s : ℝ) - 1) * ∑ p : Fin s × Fin s, 8 * ∑ a, ∑ b, ∑ u, ∑ v,
            Complex.normSq (c (((a, b), (u, v)), p)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) fun p _ _ => ?_) hs1
          have hnn : (0 : ℝ) ≤ ∑ a, ∑ b, ∑ u, ∑ v,
              Complex.normSq (c (((a, b), (u, v)), p)) :=
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
              Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
                Complex.normSq_nonneg _
          linarith
      _ = 8 * ((s : ℝ) - 1) * ∑ k : KIdx U V × (Fin s × Fin s), Complex.normSq (c k) := by
          rw [hsum, ← Finset.mul_sum]
          ring

end RankR
