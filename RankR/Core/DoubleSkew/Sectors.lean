/-
The symmetric/antisymmetric sector decomposition of the partial transpose.

On the doubled space `W ⊗ Q` the partially transposed operator `ρ₀^{T_W}` splits
into a positive part supported on the symmetric combinations
`σ_{ij} = ε_{ij} + ε_{ji}` and a negative part supported on the antisymmetric
combinations `ζ_{ij} = ε_{ij} - ε_{ji}`, where `ε_{jk} = ē_j ⊗ q_k`.  Both sector
operators are recorded here in doubled, denominator-free form: `Ppos = 2P₊` and
`Pneg = 2P₋`, which clears the `1/√2` normalization of the individual `σ` and
`ζ` vectors.

The `W` index is carried whole throughout: the partial transpose exchanges `W`
indices and keeps `Q` indices, and each sector vector is a `W`-vector placed at a
single `Q`-coordinate.  Section 3 reads the whole layer at `W = U ⊗ V`.
-/
import RankR.Library.Quantum.Kraus

namespace RankR

open Matrix Finset ComplexConjugate

section Sectors

variable {W : Type*} {s : ℕ}

/-- Partial transposition on the `W` factor of `W ⊗ Q`, defined entrywise: the
`W` indices are exchanged and the `Q` indices are kept.  At `W = U ⊗ V` this is
the `T_{UV}` of section 3. -/
def ptransposeUV (R : Matrix (W × Fin s) (W × Fin s) ℂ) : Matrix (W × Fin s) (W × Fin s) ℂ :=
  Matrix.of fun x y => R (y.1, x.2) (x.1, y.2)

@[simp] theorem ptransposeUV_apply (R : Matrix (W × Fin s) (W × Fin s) ℂ)
    (x y : W × Fin s) : ptransposeUV R x y = R (y.1, x.2) (x.1, y.2) := rfl

/-- `ε_{jk} = ē_j ⊗ q_k`: the entrywise conjugate of `e j` on `W`, tensored with
the `k`-th standard basis vector of `Q`. -/
def eps (e : Fin s → EuclideanSpace ℂ W) (j k : Fin s) : EuclideanSpace ℂ (W × Fin s) :=
  WithLp.toLp 2 (fun x => if x.2 = k then conj (e j x.1) else 0)

@[simp] theorem eps_apply (e : Fin s → EuclideanSpace ℂ W) (j k : Fin s) (x : W × Fin s) :
    eps e j k x = if x.2 = k then conj (e j x.1) else 0 := rfl

/-- The symmetric combination `σ_{ij} = ε_{ij} + ε_{ji}`. -/
def sigmaV (e : Fin s → EuclideanSpace ℂ W) (i j : Fin s) : EuclideanSpace ℂ (W × Fin s) :=
  eps e i j + eps e j i

/-- The antisymmetric combination `ζ_{ij} = ε_{ij} - ε_{ji}`. -/
def zetaV (e : Fin s → EuclideanSpace ℂ W) (i j : Fin s) : EuclideanSpace ℂ (W × Fin s) :=
  eps e i j - eps e j i

@[simp] theorem sigmaV_apply (e : Fin s → EuclideanSpace ℂ W) (i j : Fin s) (x : W × Fin s) :
    sigmaV e i j x = eps e i j x + eps e j i x := rfl

@[simp] theorem zetaV_apply (e : Fin s → EuclideanSpace ℂ W) (i j : Fin s) (x : W × Fin s) :
    zetaV e i j x = eps e i j x - eps e j i x := rfl

/-- `Ppos = 2P₊`: twice the symmetric sector of the partially transposed
doubled state. -/
noncomputable def Ppos (e : Fin s → EuclideanSpace ℂ W) : Matrix (W × Fin s) (W × Fin s) ℂ :=
  (2 : ℂ) • (∑ i, rankOne (eps e i i) (eps e i i))
    + ∑ p ∈ Finset.univ.filter (fun p : Fin s × Fin s => p.1 < p.2),
        rankOne (sigmaV e p.1 p.2) (sigmaV e p.1 p.2)

/-- `Pneg = 2P₋`: twice the antisymmetric sector of the partially transposed
doubled state. -/
noncomputable def Pneg (e : Fin s → EuclideanSpace ℂ W) : Matrix (W × Fin s) (W × Fin s) ℂ :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin s × Fin s => p.1 < p.2),
    rankOne (zetaV e p.1 p.2) (zetaV e p.1 p.2)

end Sectors

section Positivity

variable {W : Type*} [Fintype W]

/-- Doubling a complex number doubles its real part. -/
theorem two_mul_re (z : ℂ) : ((2 : ℂ) * z).re = 2 * z.re := by
  simp [Complex.mul_re]

variable {s : ℕ}

/-- The symmetric sector is positive semidefinite, being a sum of rank-one
projectors with nonnegative weights. -/
theorem qform_Ppos_nonneg (e : Fin s → EuclideanSpace ℂ W) (x : EuclideanSpace ℂ (W × Fin s)) :
    0 ≤ (qform (Ppos e) x).re := by
  rw [Ppos, qform_add, Complex.add_re, qform_smul, qform_sum_finset, two_mul_re,
    Complex.re_sum, qform_sum_finset, Complex.re_sum]
  have h1 : 0 ≤ ∑ i, (qform (rankOne (eps e i i) (eps e i i)) x).re :=
    Finset.sum_nonneg fun i _ => qform_rankOne_nonneg _ _
  have h2 : 0 ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin s × Fin s => p.1 < p.2),
      (qform (rankOne (sigmaV e p.1 p.2) (sigmaV e p.1 p.2)) x).re :=
    Finset.sum_nonneg fun p _ => qform_rankOne_nonneg _ _
  linarith

end Positivity

section Identity

variable {W : Type*} {s : ℕ}

/-- The double sum `∑ᵢ ∑ⱼ |ε_{ij}⟩⟨ε_{ji}|` is the partial transpose of the
rank-one operator built from `δ = ∑ᵢ eᵢ ⊗ qᵢ`.  No orthonormality of `e` is
used. -/
theorem sum_rankOne_eps_eq (e : Fin s → EuclideanSpace ℂ W) :
    ∑ i, ∑ j, rankOne (eps e i j) (eps e j i)
      = ptransposeUV (rankOne (delta e) (delta e)) := by
  ext x y
  have hterm : ∀ i j : Fin s, rankOne (eps e i j) (eps e j i) x y
      = (if x.2 = j then conj (e i x.1) else 0) * (if y.2 = i then e j y.1 else 0) := by
    intro i j
    simp [rankOne, apply_ite conj]
  have hj : ∀ i : Fin s,
      ∑ j, ((if x.2 = j then conj (e i x.1) else 0) * (if y.2 = i then e j y.1 else 0))
        = conj (e i x.1) * (if y.2 = i then e x.2 y.1 else 0) := by
    intro i
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  have hi : ∑ i, conj (e i x.1) * (if y.2 = i then e x.2 y.1 else 0)
      = conj (e y.2 x.1) * e x.2 y.1 := by
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  calc (∑ i, ∑ j, rankOne (eps e i j) (eps e j i)) x y
      = ∑ i, ∑ j,
          ((if x.2 = j then conj (e i x.1) else 0) * (if y.2 = i then e j y.1 else 0)) := by
        simp only [Matrix.sum_apply]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
    _ = ∑ i, conj (e i x.1) * (if y.2 = i then e x.2 y.1 else 0) :=
        Finset.sum_congr rfl fun i _ => hj i
    _ = conj (e y.2 x.1) * e x.2 y.1 := hi
    _ = ptransposeUV (rankOne (delta e) (delta e)) x y := by
        simp only [ptransposeUV_apply, rankOne, Matrix.of_apply, delta_apply]
        ring

/-- The difference of the symmetric and antisymmetric rank-one projectors. -/
theorem rankOne_sigmaV_sub_rankOne_zetaV (e : Fin s → EuclideanSpace ℂ W) (i j : Fin s) :
    rankOne (sigmaV e i j) (sigmaV e i j) - rankOne (zetaV e i j) (zetaV e i j)
      = (2 : ℂ) • (rankOne (eps e i j) (eps e j i) + rankOne (eps e j i) (eps e i j)) := by
  ext x y
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, rankOne, Matrix.of_apply,
    sigmaV_apply, zetaV_apply, map_add, map_sub, smul_eq_mul]
  ring

/-- Splitting a double sum over `Fin s × Fin s` into its diagonal and the
unordered off-diagonal pairs. -/
theorem sum_split_lt {M : Type*} [AddCommMonoid M] (G : Fin s → Fin s → M) :
    (∑ i, G i i)
        + ∑ p ∈ Finset.univ.filter (fun p : Fin s × Fin s => p.1 < p.2),
            (G p.1 p.2 + G p.2 p.1)
      = ∑ i, ∑ j, G i j := by
  have hd : (∑ i, G i i) = ∑ i, ∑ j, (if i = j then G i j else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hf : ∑ p ∈ Finset.univ.filter (fun p : Fin s × Fin s => p.1 < p.2),
        (G p.1 p.2 + G p.2 p.1)
      = (∑ i, ∑ j, (if i < j then G i j else 0))
        + ∑ i, ∑ j, (if i < j then G j i else 0) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
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

/-- `eq:rho-partial-transpose` in doubled, denominator-free form: the difference
of the two sector operators is twice the partial transpose of the rank-one
operator built from `δ`. -/
theorem Ppos_sub_Pneg (e : Fin s → EuclideanSpace ℂ W) :
    Ppos e - Pneg e = (2 : ℂ) • ptransposeUV (rankOne (delta e) (delta e)) := by
  rw [← sum_rankOne_eps_eq, ← sum_split_lt (fun i j => rankOne (eps e i j) (eps e j i)),
    Ppos, Pneg, add_sub_assoc, ← Finset.sum_sub_distrib, smul_add]
  refine congrArg₂ (· + ·) rfl ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun (p : Fin s × Fin s) _ =>
    rankOne_sigmaV_sub_rankOne_zetaV e p.1 p.2

end Identity

end RankR
