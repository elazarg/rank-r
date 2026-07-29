/-
The map identity: `Ψ_r` is a tensor square.

Write `Δ(X) = Tr(X) I` for discard-and-reprepare, `τ` for the transpose, and
`R_{−a} = Δ − a·id`.  The single-factor map of `sec:double-skew` is
`Λ(Y) = Tr(Y)I − Yᵀ`, so `Λ ∘ τ = Δ − id = R_{−1}`.

Two structural facts drive everything.  `Δ` is monoidal — `Δ_{U⊗V} = Δ_U ⊗ Δ_V`,
because discarding a composite and repreparing it is discarding and repreparing
each factor (`RU_zero_RV_zero`) — and so is `τ`.  Hence

  `(Λ_U ⊗ Λ_V) ∘ τ = (Λ_U ∘ τ_U) ⊗ (Λ_V ∘ τ_V) = S_U ⊗ S_V`,   `S := Δ − id`.

The maps `{id, Δ}` span a two-dimensional commutative algebra — the commutant of
`U(d)` acting on `𝓛(H)`, since `𝓛(H) = ℂI ⊕ traceless` is a sum of two
inequivalent irreducibles — and `R_{−a} = S + (1−a)·id` lives in it.  With
`t := (r−1)/r`, so that `R_{−1/r} = S + t·id`, the identity

  `(Λ_U ⊗ Λ_V)∘τ + (r−1)(Δ − (1/r)id) = r · R^U_{−1/r} ⊗ R^V_{−1/r}`

is the binomial expansion of `(S + t·id)^{⊗2}`:

  `S⊗S + (r−1)(S+id)⊗(S+id) − t·id
     = r·S⊗S + (r−1)(S⊗id + id⊗S) + ((r−1)²/r)·id
     = r·[S⊗S + t(S⊗id + id⊗S) + t²·id]`,

using `r·t = r−1` and `r·t² = (r−1)²/r`.  So `prop:operator_ineq` is the
`r`-positivity of `R_{−1/r} ⊗ R_{−1/r}`, and the `1/r` in it is the only free
coefficient a `U(d)`-covariant correction to `Φ∘τ` can have.

The collapse is bipartite.  For `n` factors `Δ = ∑_{T ⊆ [n]} ⊗_{i∈T} S_i`, and
matching `⊗_{i∈T} S_i` against `c · ⊗(S + t·id)` needs `r−1 = r t^{n−|T|}` for
every `T` with `|T| < n`.  The `|T| = n−1` equation is `r−1 = rt`, which holds,
and for `n = 2` the `−t·id` term repairs `|T| = 0`; but for `n ≥ 3` the
`|T| = n−2` equation reads `r−1 = (r−1)²/r`, i.e. `r = 1`.  So the even-partite
family of higher copies is genuinely an inequality and not a map identity of this
shape.

Everything is scaled by `4`, matching `Phi4 = 4 (Λ_U ⊗ Λ_V)`.
-/
import RankR.Core.DoubleSkew.Choi

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

/-! ## The covariant pencil

`R_{−a} = Δ − a·id`, applied to one factor with the identity on the other.  Each
of the two needs only the instances of the factor it acts on. -/

section PencilU

variable {U V : Type*} [Fintype U] [DecidableEq U]

/-- `R^U_{−a} ⊗ id_V`: the pencil `Δ − a·id` applied to the `U` factor. -/
def RU (a : ℂ) (X : Matrix (U × V) (U × V) ℂ) : Matrix (U × V) (U × V) ℂ :=
  Matrix.of fun x y => (if x.1 = y.1 then (1 : ℂ) else 0) * ptraceU X x.2 y.2 - a * X x y

@[simp] theorem RU_apply (a : ℂ) (X : Matrix (U × V) (U × V) ℂ) (x y : U × V) :
    RU a X x y = (if x.1 = y.1 then (1 : ℂ) else 0) * ptraceU X x.2 y.2 - a * X x y := rfl

/-- The pencil is affine in its parameter: `R_{−a} = S + (1−a)·id` for
`S = R_{−1} = Δ − id`.  Together with `RU_zero_RV_zero` this exhibits the maps in
play as elements of `span {id, Δ}`. -/
theorem RU_eq_pencil (a : ℂ) (X : Matrix (U × V) (U × V) ℂ) :
    RU a X = RU 1 X + (1 - a) • X := by
  ext x y
  simp only [RU_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_mul]
  ring

end PencilU

section PencilV

variable {U V : Type*} [Fintype V] [DecidableEq V]

/-- `id_U ⊗ R^V_{−b}`: the pencil applied to the `V` factor. -/
def RV (b : ℂ) (X : Matrix (U × V) (U × V) ℂ) : Matrix (U × V) (U × V) ℂ :=
  Matrix.of fun x y => (if x.2 = y.2 then (1 : ℂ) else 0) * ptraceV X x.1 y.1 - b * X x y

@[simp] theorem RV_apply (b : ℂ) (X : Matrix (U × V) (U × V) ℂ) (x y : U × V) :
    RV b X x y = (if x.2 = y.2 then (1 : ℂ) else 0) * ptraceV X x.1 y.1 - b * X x y := rfl

end PencilV

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- `Δ(X) = Tr(X) I`: discard, then reprepare the maximally mixed state. -/
noncomputable def Dl (X : Matrix (U × V) (U × V) ℂ) : Matrix (U × V) (U × V) ℂ :=
  X.trace • (1 : Matrix (U × V) (U × V) ℂ)

omit [DecidableEq V] in
/-- Tracing out `V` after `R^U_{−a} ⊗ id` leaves `Δ_U − a·Tr_V` on `U`: the
`U`-marginal of the pencil is the pencil of the `U`-marginal. -/
theorem ptraceV_RU (a : ℂ) (X : Matrix (U × V) (U × V) ℂ) (u u' : U) :
    ptraceV (RU a X) u u'
      = (if u = u' then (1 : ℂ) else 0) * X.trace - a * ptraceV X u u' := by
  have htr : X.trace = ∑ d : V, ptraceU X d d := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [ptraceV_apply, ptraceV_apply, htr, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ => rfl

/-- **The four-term entry formula for `R^U_{−a} ⊗ R^V_{−b}`.**

The `Tr(X)` term is `Δ_U ⊗ Δ_V` and is symmetric in the two factors: that is the
monoidality of `Δ`.  The two middle terms carry one factor of the pencil each,
and the last is `ab · id`. -/
theorem RV_RU_apply (a b : ℂ) (X : Matrix (U × V) (U × V) ℂ) (x y : U × V) :
    RV b (RU a X) x y
      = (if x.1 = y.1 then (1 : ℂ) else 0) * (if x.2 = y.2 then (1 : ℂ) else 0) * X.trace
        - a * (if x.2 = y.2 then (1 : ℂ) else 0) * ptraceV X x.1 y.1
        - b * (if x.1 = y.1 then (1 : ℂ) else 0) * ptraceU X x.2 y.2
        + a * b * X x y := by
  rw [RV_apply, ptraceV_RU, RU_apply]
  ring

/-- The two pencils commute, acting on disjoint factors. -/
theorem RU_comm_RV (a b : ℂ) (X : Matrix (U × V) (U × V) ℂ) :
    RU a (RV b X) = RV b (RU a X) := by
  ext x y
  rw [RV_RU_apply, RU_apply, ptraceU_apply]
  have htr : X.trace = ∑ c : U, ptraceV X c c := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    rfl
  have h : ∑ c : U, RV b X (c, x.2) (c, y.2)
      = (if x.2 = y.2 then (1 : ℂ) else 0) * X.trace - b * ptraceU X x.2 y.2 := by
    rw [htr, ptraceU_apply, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => rfl
  rw [h, RV_apply]
  ring

/-- **`Δ` is monoidal**: discarding and repreparing the composite is discarding
and repreparing each factor.  This is the `a = b = 0` corner of the pencil. -/
theorem RU_zero_RV_zero (X : Matrix (U × V) (U × V) ℂ) : RV 0 (RU 0 X) = Dl X := by
  ext x y
  rw [RV_RU_apply, Dl, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    simp [Prod.ext_iff, h1, h2]

/-! ## The double-skew map without the ancilla -/

/-- `4 (Λ_U ⊗ Λ_V)`: the Kraus sum of the double-skew family on `𝓛(U ⊗ V)`. -/
noncomputable def Lam4 (X : Matrix (U × V) (U × V) ℂ) : Matrix (U × V) (U × V) ℂ :=
  krausSum skewKraus X

/-- Entries of `Lam4 X` before the Kronecker deltas are collapsed. -/
theorem Lam4_apply_aux (X : Matrix (U × V) (U × V) ℂ) (x y : U × V) :
    Lam4 X x y = ∑ q : U × V, ∑ q' : U × V,
      ((2 * ((if x.1 = y.1 then (1 : ℂ) else 0) * (if q.1 = q'.1 then 1 else 0)
           - (if x.1 = q'.1 then (1 : ℂ) else 0) * (if q.1 = y.1 then 1 else 0)))
        * (2 * ((if x.2 = y.2 then (1 : ℂ) else 0) * (if q.2 = q'.2 then 1 else 0)
           - (if x.2 = q'.2 then (1 : ℂ) else 0) * (if q.2 = y.2 then 1 else 0))))
        * X q q' := by
  have h1 : Lam4 X x y = ∑ p : KIdx U V, ∑ q : U × V, ∑ q' : U × V,
      skewKraus p x q * X q q' * conj (skewKraus p y q') := by
    simp only [Lam4, krausSum, Matrix.sum_apply, mul_mul_conjTranspose_apply]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q' _ => ?_
  rw [← sum_kron_coeff x q y q', Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => by simp only [skewKraus]; ring

/-- **The kernel of `Lam4`**: four terms, the first three carried by Kronecker
deltas on the `U` and `V` labels and the last one unrestricted. -/
theorem Lam4_apply (X : Matrix (U × V) (U × V) ℂ) (x y : U × V) :
    Lam4 X x y
      = 4 * ((if x.1 = y.1 ∧ x.2 = y.2 then X.trace else 0)
           - (if x.1 = y.1 then ptraceU X y.2 x.2 else 0)
           - (if x.2 = y.2 then ptraceV X y.1 x.1 else 0)
           + X (y.1, y.2) (x.1, x.2)) := by
  rw [Lam4_apply_aux]
  simp only [Fintype.sum_prod_type]
  have hre : ∀ (γ : U) (δ : V) (γ' : U) (δ' : V),
      ((2 * ((if x.1 = y.1 then (1 : ℂ) else 0) * (if γ = γ' then 1 else 0)
           - (if x.1 = γ' then (1 : ℂ) else 0) * (if γ = y.1 then 1 else 0)))
        * (2 * ((if x.2 = y.2 then (1 : ℂ) else 0) * (if δ = δ' then 1 else 0)
           - (if x.2 = δ' then (1 : ℂ) else 0) * (if δ = y.2 then 1 else 0))))
        * X (γ, δ) (γ', δ')
      = ((4 * ((if x.1 = y.1 then (1 : ℂ) else 0) * (if γ = γ' then 1 else 0)
             - (if x.1 = γ' then (1 : ℂ) else 0) * (if γ = y.1 then 1 else 0)))
          * ((if x.2 = y.2 then (1 : ℂ) else 0) * (if δ = δ' then 1 else 0)
             - (if x.2 = δ' then (1 : ℂ) else 0) * (if δ = y.2 then 1 else 0)))
        * X (γ, δ) (γ', δ') := fun γ δ γ' δ' => by ring
  simp only [hre]
  have hinner : ∀ (γ : U) (δ : V), ∑ γ' : U, ∑ δ' : V,
      ((4 * ((if x.1 = y.1 then (1 : ℂ) else 0) * (if γ = γ' then 1 else 0)
           - (if x.1 = γ' then (1 : ℂ) else 0) * (if γ = y.1 then 1 else 0)))
        * ((if x.2 = y.2 then (1 : ℂ) else 0) * (if δ = δ' then 1 else 0)
           - (if x.2 = δ' then (1 : ℂ) else 0) * (if δ = y.2 then 1 else 0)))
        * X (γ, δ) (γ', δ')
      = 4 * ((if x.1 = y.1 then (1 : ℂ) else 0)
              * ((if x.2 = y.2 then (1 : ℂ) else 0) * X (γ, δ) (γ, δ)
                 - (if δ = y.2 then (1 : ℂ) else 0) * X (γ, δ) (γ, x.2))
            - (if γ = y.1 then (1 : ℂ) else 0)
              * ((if x.2 = y.2 then (1 : ℂ) else 0) * X (γ, δ) (x.1, δ)
                 - (if δ = y.2 then (1 : ℂ) else 0) * X (γ, δ) (x.1, x.2))) :=
    fun γ δ => sum_antisym_collapse 4 x.1 y.1 γ x.2 y.2 δ (fun γ' δ' => X (γ, δ) (γ', δ'))
  simp only [hinner, ← Finset.mul_sum]
  rw [sum_outer_collapse x.1 y.1 x.2 y.2 (fun γ δ γ' δ' => X (γ, δ) (γ', δ'))]
  have hS : (∑ γ : U, ∑ δ : V, X (γ, δ) (γ, δ)) = X.trace := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    rfl
  rw [hS]
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    simp only [h1, h2, if_false, and_true, and_false, one_mul, zero_mul, mul_one, mul_zero,
      sub_zero, zero_sub, if_pos, ptraceU_apply, ptraceV_apply]

/-- **`(Λ_U ⊗ Λ_V) ∘ τ = S_U ⊗ S_V`**, at `S = Δ − id`.

Both `Λ` and `τ` are monoidal, and on a single factor `Λ ∘ τ = Δ − id`; the
identity is those two facts and nothing else. -/
theorem Lam4_transpose (X : Matrix (U × V) (U × V) ℂ) :
    Lam4 Xᵀ = (4 : ℂ) • RV 1 (RU 1 X) := by
  ext x y
  have htr : (Xᵀ).trace = X.trace := Matrix.trace_transpose X
  have hU : ∀ b c : V, ptraceU (Xᵀ) b c = ptraceU X c b := by
    intro b c
    simp only [ptraceU_apply, Matrix.transpose_apply]
  have hV : ∀ u u' : U, ptraceV (Xᵀ) u u' = ptraceV X u' u := by
    intro u u'
    simp only [ptraceV_apply, Matrix.transpose_apply]
  rw [Lam4_apply, htr, hU, hV, Matrix.smul_apply, smul_eq_mul, RV_RU_apply]
  have hx : (Xᵀ) (y.1, y.2) (x.1, x.2) = X x y := by
    simp only [Matrix.transpose_apply]
  rw [hx]
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    simp only [h1, h2, if_false, if_true, and_true, and_false, one_mul, zero_mul, mul_one,
      mul_zero, sub_zero, zero_sub]
  ring

/-! ## The map identity -/

/-- `Ψ_r = (Λ_U ⊗ Λ_V)∘τ + (r−1)(Δ − (1/r)id)`, scaled by `4`.

`prop:operator_ineq` is the assertion that this map is `r`-positive. -/
noncomputable def Psi (r : ℕ) (X : Matrix (U × V) (U × V) ℂ) : Matrix (U × V) (U × V) ℂ :=
  Lam4 Xᵀ + (4 * ((r : ℂ) - 1)) • (Dl X - ((r : ℂ))⁻¹ • X)

/-- **The map identity.**

`Ψ_r = r · R^U_{−1/r} ⊗ R^V_{−1/r}`, the binomial expansion of `(S + t·id)^{⊗2}`
at `t = (r−1)/r`.  Both `r−1` and the `1/r` acquire meanings: the first is the
degree of the frame, the second the single coefficient a `U(d)`-covariant
correction to `Φ∘τ` is free to have.

On one factor `R_{−1/r}` is the boundary of the `r`-positive cone along the
pencil from `id` to `Δ`: `Δ − t·id` is `k`-positive exactly for `t ≤ 1/k`, by
Tomiyama, *On the geometry of positive maps in matrix algebras II*, Linear
Algebra Appl. 69:169--177 (1985), Thm. 2(i), where it appears as `τ_k`.  That
the tensor square keeps the same level is not implied by it. -/
theorem Psi_eq_tensor_square {r : ℕ} (hr : 0 < r) (X : Matrix (U × V) (U × V) ℂ) :
    Psi r X = (4 * (r : ℂ)) • RV ((r : ℂ))⁻¹ (RU ((r : ℂ))⁻¹ X) := by
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  ext x y
  rw [Psi, Matrix.add_apply, Lam4_transpose, Matrix.smul_apply, smul_eq_mul, RV_RU_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Dl, Matrix.smul_apply, smul_eq_mul,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    RV_RU_apply]
  have hone : (if x = y then (1 : ℂ) else 0)
      = (if x.1 = y.1 then (1 : ℂ) else 0) * (if x.2 = y.2 then (1 : ℂ) else 0) := by
    by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
      simp [Prod.ext_iff, h1, h2]
  rw [hone]
  field_simp
  ring

end RankR
