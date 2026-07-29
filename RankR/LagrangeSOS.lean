/-
The polynomial sum-of-squares certificate for the trace--rank residual.

The manuscript writes this as the squared norm of `δ_e ∧ δ_d`.  The literal
polynomial content is the coordinate Lagrange identity: the residual is the
sum of the squared moduli of all two-by-two minors.  We first prove a
choice-free ordered-pair form on any finite coordinate type, then recover the
usual `α < β` form when the coordinates carry a linear order.
-/
import RankR.Sectors
import Mathlib.Data.Prod.Lex

namespace RankR

open Matrix Finset ComplexConjugate

section CoordinateIdentity

variable {ι : Type*} [Fintype ι]

/-- The two-by-two minor of a pair of complex coordinate vectors. -/
def lagrangeMinor (u v : ι → ℂ) (a b : ι) : ℂ :=
  u a * v b - u b * v a

/-- The cross term in the complex Lagrange identity, before taking real
parts. -/
private theorem sum_lagrange_cross (u v : ι → ℂ) :
    ∑ a, ∑ b, u a * v b * conj (u b * v a)
      = ((Complex.normSq (∑ a, conj (u a) * v a) : ℝ) : ℂ) := by
  calc
    ∑ a, ∑ b, u a * v b * conj (u b * v a)
        = ∑ a, ∑ b, (u a * conj (v a)) * (conj (u b) * v b) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            simp only [map_mul]
            ring
    _ = (∑ a, u a * conj (v a)) * ∑ b, conj (u b) * v b := by
          rw [Finset.sum_mul_sum]
    _ = conj (∑ a, conj (u a) * v a) * ∑ b, conj (u b) * v b := by
          congr 1
          rw [map_sum]
          exact Finset.sum_congr rfl fun a _ => by
            simp only [map_mul, Complex.conj_conj]
    _ = ((Complex.normSq (∑ a, conj (u a) * v a) : ℝ) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm

/-- The complex Lagrange identity in an order-free form.  Every unordered
minor appears twice in the double sum, so the factor `1/2` gives the usual
sum over pairs. -/
theorem complex_lagrange_sos_ordered (u v : ι → ℂ) :
    (∑ a, Complex.normSq (u a)) * (∑ a, Complex.normSq (v a))
        - Complex.normSq (∑ a, conj (u a) * v a)
      = (1 / 2 : ℝ) * ∑ a, ∑ b, Complex.normSq (lagrangeMinor u v a b) := by
  let U : ℝ := ∑ a, Complex.normSq (u a)
  let V : ℝ := ∑ a, Complex.normSq (v a)
  let I : ℂ := ∑ a, conj (u a) * v a
  have huu : ∑ a, ∑ b, Complex.normSq (u a * v b) = U * V := by
    simp only [Complex.normSq_mul, U, V]
    rw [Finset.sum_mul_sum]
  have hvv : ∑ a, ∑ b, Complex.normSq (u b * v a) = U * V := by
    rw [Finset.sum_comm]
    simpa only [Complex.normSq_mul, mul_comm] using huu
  have hcross : ∑ a, ∑ b, (u a * v b * conj (u b * v a)).re = Complex.normSq I := by
    have h := congrArg Complex.re (sum_lagrange_cross u v)
    simpa only [Complex.re_sum, Complex.ofReal_re, I] using h
  have hcross2 : ∑ a, ∑ b, 2 * (u a * v b * conj (u b * v a)).re
      = 2 * Complex.normSq I := by
    calc
      _ = ∑ a, 2 * ∑ b, (u a * v b * conj (u b * v a)).re := by
            refine Finset.sum_congr rfl fun a _ => ?_
            exact (Finset.mul_sum Finset.univ
              (fun b => (u a * v b * conj (u b * v a)).re) 2).symm
      _ = 2 * ∑ a, ∑ b, (u a * v b * conj (u b * v a)).re := by
            exact (Finset.mul_sum Finset.univ
              (fun a => ∑ b, (u a * v b * conj (u b * v a)).re) 2).symm
      _ = 2 * Complex.normSq I := by rw [hcross]
  have hexpand :
      ∑ a, ∑ b, Complex.normSq (lagrangeMinor u v a b)
        = 2 * U * V - 2 * Complex.normSq I := by
    simp only [lagrangeMinor, Complex.normSq_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [huu, hvv, hcross2]
    ring
  rw [hexpand]
  dsimp only [U, V, I]
  ring

/-- The order-free coordinate identity expressed intrinsically on a finite
complex Euclidean space. -/
theorem euclidean_lagrange_sos_ordered (u v : EuclideanSpace ℂ ι) :
    ‖u‖ ^ 2 * ‖v‖ ^ 2 - Complex.normSq (inner ℂ u v)
      = (1 / 2 : ℝ) * ∑ a, ∑ b,
          Complex.normSq (lagrangeMinor u v a b) := by
  simpa only [EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq,
    PiLp.inner_apply, RCLike.inner_apply, mul_comm] using
      complex_lagrange_sos_ordered (fun a => u a) (fun a => v a)

end CoordinateIdentity

section UnorderedCoordinates

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The unordered coordinate pairs used by the usual minor formula. -/
def lagrangePairs (ι : Type*) [Fintype ι] [LinearOrder ι] : Finset (ι × ι) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- Split a finite double sum into its diagonal and its two orientations of
each unordered pair. -/
theorem sum_split_lt_linearOrder {M : Type*} [AddCommMonoid M] (G : ι → ι → M) :
    (∑ i, G i i)
        + ∑ p ∈ lagrangePairs ι, (G p.1 p.2 + G p.2 p.1)
      = ∑ i, ∑ j, G i j := by
  have hd : (∑ i, G i i) = ∑ i, ∑ j, (if i = j then G i j else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hf : ∑ p ∈ lagrangePairs ι, (G p.1 p.2 + G p.2 p.1)
      = (∑ i, ∑ j, (if i < j then G i j else 0))
        + ∑ i, ∑ j, (if i < j then G j i else 0) := by
    rw [lagrangePairs, Finset.sum_filter, Fintype.sum_prod_type,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hswap : (∑ i, ∑ j, (if i < j then G j i else 0))
      = ∑ i, ∑ j, (if j < i then G i j else 0) := Finset.sum_comm
  rw [hd, hf, hswap, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, asymm h]
  · simp [h]
  · simp [h, h.ne', asymm h]

/-- The literal polynomial SOS form of the complex Lagrange identity: one
squared modulus for each unordered pair of coordinates. -/
theorem complex_lagrange_sos (u v : ι → ℂ) :
    (∑ a, Complex.normSq (u a)) * (∑ a, Complex.normSq (v a))
        - Complex.normSq (∑ a, conj (u a) * v a)
      = ∑ p ∈ lagrangePairs ι,
          Complex.normSq (lagrangeMinor u v p.1 p.2) := by
  have hrev : ∀ a b, Complex.normSq (lagrangeMinor u v b a)
      = Complex.normSq (lagrangeMinor u v a b) := by
    intro a b
    rw [show lagrangeMinor u v b a = -lagrangeMinor u v a b by
      simp only [lagrangeMinor]; ring, Complex.normSq_neg]
  have hdiag : ∀ a, Complex.normSq (lagrangeMinor u v a a) = 0 := by
    intro a
    simp [lagrangeMinor]
  have hsplit :
      ∑ a, ∑ b, Complex.normSq (lagrangeMinor u v a b)
        = 2 * ∑ p ∈ lagrangePairs ι,
            Complex.normSq (lagrangeMinor u v p.1 p.2) := by
    rw [← sum_split_lt_linearOrder
      (fun a b => Complex.normSq (lagrangeMinor u v a b))]
    simp only [hdiag, Finset.sum_const_zero, zero_add, hrev]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [complex_lagrange_sos_ordered, hsplit]
  ring

/-- The squared norm of the decomposable exterior two-vector `u ∧ v`, in the
orthonormal coordinate convention of `eq:sos-lagrange`.  Defining only its
squared norm keeps this polynomial certificate independent of an exterior
algebra API. -/
def lagrangeWedgeNormSq (u v : ι → ℂ) : ℝ :=
  ∑ p ∈ lagrangePairs ι, Complex.normSq (lagrangeMinor u v p.1 p.2)

/-- The complex Lagrange identity in the manuscript's exterior-norm
rendering. -/
theorem complex_lagrange_wedge_normSq (u v : ι → ℂ) :
    (∑ a, Complex.normSq (u a)) * (∑ a, Complex.normSq (v a))
        - Complex.normSq (∑ a, conj (u a) * v a)
      = lagrangeWedgeNormSq u v := by
  exact complex_lagrange_sos u v

/-- The familiar `α < β` form of the Lagrange identity on a finite complex
Euclidean space. -/
theorem euclidean_lagrange_sos (u v : EuclideanSpace ℂ ι) :
    ‖u‖ ^ 2 * ‖v‖ ^ 2 - Complex.normSq (inner ℂ u v)
      = ∑ p ∈ lagrangePairs ι,
          Complex.normSq (lagrangeMinor u v p.1 p.2) := by
  simpa only [EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq,
    PiLp.inner_apply, RCLike.inner_apply, mul_comm] using
      complex_lagrange_sos (fun a => u a) (fun a => v a)

end UnorderedCoordinates

section TraceRankResidual

variable {W : Type*} [Fintype W] {s : ℕ}

/-- `eq:sos-lagrange-coordinates` in a choice-free ordered-pair rendering.
For an orthonormal range factorization, the trace--rank residual is exactly
half the sum of the squared coordinate minors of `δ_e` and `δ_d`. -/
theorem rankFactor_traceRankResidual_eq_lagrangeSOS_ordered
    (e d : Fin s → EuclideanSpace ℂ W) (he : Orthonormal ℂ e) :
    (s : ℝ) * hsNormSq (rankFactor e d)
        - Complex.normSq (rankFactor e d).trace
      = (1 / 2 : ℝ) * ∑ a : W × Fin s, ∑ b : W × Fin s,
          Complex.normSq (lagrangeMinor (delta e) (delta d) a b) := by
  have h := euclidean_lagrange_sos_ordered (delta e) (delta d)
  have heNorm : ‖delta e‖ ^ 2 = (s : ℝ) := by
    rw [norm_delta]
    simp [he.1]
  rw [heNorm, ← contraction_norm e d he, inner_delta_delta,
    Complex.normSq_conj] at h
  exact h

end TraceRankResidual

section OrderedTraceRankResidual

variable {W : Type*} [Fintype W] [LinearOrder W] {s : ℕ}

/-- The coordinates of `δ_e`, equipped with the lexicographic order on
`W × Fin s`. -/
def deltaLex (e : Fin s → EuclideanSpace ℂ W) : W ×ₗ Fin s → ℂ :=
  fun a => delta e (ofLex a)

/-- `eq:sos-lagrange-coordinates` literally: one squared two-by-two minor for
each coordinate pair `α < β`. -/
theorem rankFactor_traceRankResidual_eq_lagrangeSOS
    (e d : Fin s → EuclideanSpace ℂ W) (he : Orthonormal ℂ e) :
    (s : ℝ) * hsNormSq (rankFactor e d)
        - Complex.normSq (rankFactor e d).trace
      = ∑ p ∈ lagrangePairs (W ×ₗ Fin s),
          Complex.normSq (lagrangeMinor (deltaLex e) (deltaLex d) p.1 p.2) := by
  have h := complex_lagrange_sos (deltaLex e) (deltaLex d)
  have hnorm (f : Fin s → EuclideanSpace ℂ W) :
      ∑ a : W ×ₗ Fin s, Complex.normSq (deltaLex f a) = ‖delta f‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.normSq_eq_norm_sq]
    exact Fintype.sum_equiv ofLex _ _ fun _ => rfl
  have hinner :
      ∑ a : W ×ₗ Fin s, conj (deltaLex e a) * deltaLex d a
        = inner ℂ (delta e) (delta d) := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, mul_comm]
    exact Fintype.sum_equiv ofLex _ _ fun _ => rfl
  have heNorm : ‖delta e‖ ^ 2 = (s : ℝ) := by
    rw [norm_delta]
    simp [he.1]
  rw [hnorm e, hnorm d, hinner, heNorm, ← contraction_norm e d he, inner_delta_delta,
    Complex.normSq_conj] at h
  exact h

/-- `eq:sos-lagrange`, with the exterior squared norm represented by its
orthonormal-coordinate definition. -/
theorem rankFactor_traceRankResidual_eq_wedgeNormSq
    (e d : Fin s → EuclideanSpace ℂ W) (he : Orthonormal ℂ e) :
    (s : ℝ) * hsNormSq (rankFactor e d)
        - Complex.normSq (rankFactor e d).trace
      = lagrangeWedgeNormSq (deltaLex e) (deltaLex d) := by
  simpa only [lagrangeWedgeNormSq] using
    rankFactor_traceRankResidual_eq_lagrangeSOS e d he

end OrderedTraceRankResidual

end RankR
