/-
Pair amplification, read in Choi form.

`Lifting.lean` proves the operator forms of pair amplification for an arbitrary
Kraus family, and `Theorem.lean` converts them into the partial-trace inequality
--- but only for `Λ_U ⊗ Λ_V`, through the contraction identity `eq:Phi-rhoT` that
is special to that map.  This file supplies the general conversion: from Lifting
II form (B) to the `R`-positivity of `Θ^Φ_{R,λ}` at `λ = (R-1)β`, which is
`thm:pair-amplification` in the normalization of `Theta.lean`.

The bridge is a choice of frame and test vector.  Factor `C = ∑ᵢ |eᵢ⟩⟨dᵢ|` with
`eᵢ` orthonormal, and run form (B) at the *conjugated* frame `ē` and the test
vector `δ_{d̄}`.  Then

* `‖δ_{d̄}‖² = ∑ᵢ‖dᵢ‖² = ‖C‖₂²`, since conjugation is an isometry;
* `⟪δ_ē, δ_{d̄}⟫ = Tr C`, by `eq:contraction-trace`;
* the negative-sector term becomes exactly `∑ₐ⟪A_a C, (A_a C)ᵀ⟫`.

The last is the computation of the file.  Both quantities are double sums over
the frame indices of products of the *bilinear* pairing `B(x, y) = ∑_w x_w y_w`
--- the partial transpose is what turns the sesquilinear inner product into a
bilinear one --- and the two match term by term through

    B(Aᴴ x̄, ȳ) = conj B(A y, x),

which is the one place the conjugated frame earns its keep.

Since the frame has `rank C` elements and the statement wants `R`, the last step
is `rank_mono`: the coefficient `(r-1)β(‖C‖₂² - |Tr C|²/r)` increases with `r`,
by the trace-rank bound.
-/
import RankR.Core.Amplification.OperatorForms
import RankR.Core.Amplification.Theta

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## The bilinear pairing -/

section Bil

variable {W : Type*} [Fintype W]

/-- The **bilinear** pairing `∑_w x_w y_w`, with no conjugation.  This, and not
the inner product, is what the partial transpose pairs vectors with. -/
def bil (x y : EuclideanSpace ℂ W) : ℂ := ∑ w, x w * y w

omit [Fintype W] in
theorem ebar_eq_bar {s : ℕ} (e : Fin s → EuclideanSpace ℂ W) (i : Fin s) :
    ebar e i = bar (e i) := rfl

/-- The pairing is symmetric, having no conjugation to break it. -/
theorem bil_comm (x y : EuclideanSpace ℂ W) : bil x y = bil y x :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **Moving the adjoint across the bilinear pairing.**  With both arguments
conjugated, `Aᴴ` on the left becomes `A` on the right and the whole pairing
conjugates.  This is what makes the conjugated frame the right one. -/
theorem bil_bar_mulVecE (A : Matrix W W ℂ) (x y : EuclideanSpace ℂ W) :
    bil (mulVecE Aᴴ (bar x)) (bar y) = conj (bil (mulVecE A y) x) := by
  rw [bil, bil, map_sum]
  have hL : ∀ w : W, mulVecE Aᴴ (bar x) w * bar y w
      = ∑ w', conj (A w' w * y w * x w') := by
    intro w
    rw [mulVecE_apply, bar_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [Matrix.conjTranspose_apply, bar_apply, RCLike.star_def]
    simp only [map_mul]
    ring
  have hR : ∀ w' : W, conj (mulVecE A y w' * x w') = ∑ w, conj (A w' w * y w * x w') := by
    intro w'
    rw [mulVecE_apply, Finset.sum_mul, map_sum]
  rw [Finset.sum_congr rfl fun w _ => hL w, Finset.sum_congr rfl fun w' _ => hR w']
  exact Finset.sum_comm

end Bil

/-! ## The two double sums -/

section DoubleSums

variable {W : Type*} [Fintype W] {s : ℕ}

/-- An operator acting on a `δ`-assembled vector acts blockwise. -/
theorem mulVecE_placeT_delta (N : Matrix W W ℂ) (v : Fin s → EuclideanSpace ℂ W) :
    mulVecE (placeT N) (delta v) = delta fun i => mulVecE N (v i) := by
  ext x
  simp only [mulVecE_apply, delta_apply, placeT_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_eq_single x.2 (fun m _ hm => by simp [Ne.symm hm])
    (fun h => absurd (Finset.mem_univ x.2) h)]
  simp

/-- Reordering a fourfold sum from `(w, i, w', j)` to `(i, j, w, w')`. -/
private theorem swap4 (G : W → Fin s → W → Fin s → ℂ) :
    (∑ w, ∑ i, ∑ w', ∑ j, G w i w' j) = ∑ i, ∑ j, ∑ w, ∑ w', G w i w' j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun w (_ : w ∈ Finset.univ) => Finset.sum_comm]
  exact Finset.sum_comm

/-- **The negative-sector quadratic form as a double sum of bilinear pairings.**

The partial transpose exchanges the two `W`-slots, which is what replaces the
inner product by the bilinear pairing `bil`. -/
theorem qform_ptransposeUV_rankOne_delta (f v : Fin s → EuclideanSpace ℂ W) :
    qform (ptransposeUV (rankOne (delta f) (delta f))) (delta v)
      = ∑ i, ∑ j, conj (bil (v i) (f j)) * bil (f i) (v j) := by
  have hR : (∑ i, ∑ j, conj (bil (v i) (f j)) * bil (f i) (v j))
      = ∑ i, ∑ j, ∑ w, ∑ w', conj (v i w) * conj (f j w) * (f i w' * v j w') := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [bil, bil, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => by
      rw [map_mul]
  have hL : qform (ptransposeUV (rankOne (delta f) (delta f))) (delta v)
      = ∑ w, ∑ i, ∑ w', ∑ j, conj (v i w) * conj (f j w) * (f i w' * v j w') := by
    rw [qform, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun w' _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ptransposeUV_apply, rankOne, Matrix.of_apply, delta_apply, delta_apply,
      delta_apply, delta_apply]
    ring
  rw [hL, hR]
  exact swap4 (fun w i w' j => conj (v i w) * conj (f j w) * (f i w' * v j w'))

/-- Left multiplication passes through the range factorization. -/
theorem mul_rankFactor (A : Matrix W W ℂ) (e d : Fin s → EuclideanSpace ℂ W) :
    A * rankFactor e d = rankFactor (fun i => mulVecE A (e i)) d := by
  ext p q
  rw [Matrix.mul_apply, rankFactor_apply]
  have h : ∀ r : W, A p r * rankFactor e d r q = ∑ i, A p r * e i r * conj (d i q) := by
    intro r
    rw [rankFactor_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun r _ => h r, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVecE_apply, Finset.sum_mul]

/-- **The Choi pairing of a single Kraus term as a double sum.**  The same shape
as `qform_ptransposeUV_rankOne_delta`, which is what lets the two be matched. -/
theorem hsInner_rankFactor_transpose (u d : Fin s → EuclideanSpace ℂ W) :
    hsInner (rankFactor u d) ((rankFactor u d)ᵀ)
      = ∑ i, ∑ j, conj (bil (u i) (d j)) * bil (d i) (u j) := by
  rw [hsInner_eq_sum_vec, Fintype.sum_prod_type]
  have hL : ∀ p q : W, conj (vec (rankFactor u d) (p, q)) * vec ((rankFactor u d)ᵀ) (p, q)
      = ∑ i, ∑ j, conj (u i p) * d i q * (u j q * conj (d j p)) := by
    intro p q
    rw [vec_apply, vec_apply, Matrix.transpose_apply, rankFactor_apply, rankFactor_apply,
      map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, Complex.conj_conj]
  have hR : (∑ i, ∑ j, conj (bil (u i) (d j)) * bil (d i) (u j))
      = ∑ i, ∑ j, ∑ p, ∑ q, conj (u i p) * d i q * (u j q * conj (d j p)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [bil, bil, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hL p q, hR]
  exact sum4_swap fun i j p q => conj (u i p) * d i q * (u j q * conj (d j p))

end DoubleSums

/-! ## The two sides agree -/

section Match

variable {W : Type*} [Fintype W] {s : ℕ}

/-- **The negative-sector form at the conjugated frame is the Choi pairing.**

Both are double sums over the frame indices of products of bilinear pairings, and
`bil_bar_mulVecE` matches them term by term.  The transposition of the index
pair is absorbed by a relabelling: the two factors of each summand
exchange roles. -/
theorem qform_ptransposeUV_conj_frame (A : Matrix W W ℂ) (e d : Fin s → EuclideanSpace ℂ W) :
    qform (ptransposeUV (rankOne (delta (ebar e)) (delta (ebar e))))
        (mulVecE (placeT Aᴴ) (delta (ebar d)))
      = hsInner (A * rankFactor e d) ((A * rankFactor e d)ᵀ) := by
  rw [mulVecE_placeT_delta, qform_ptransposeUV_rankOne_delta, mul_rankFactor,
    hsInner_rankFactor_transpose]
  have hfac : ∀ i j : Fin s,
      conj (bil (mulVecE Aᴴ (ebar d i)) (ebar e j)) * bil (ebar e i) (mulVecE Aᴴ (ebar d j))
        = conj (bil (mulVecE A (e i)) (d j)) * bil (d i) (mulVecE A (e j)) := by
    intro i j
    rw [ebar_eq_bar, ebar_eq_bar, ebar_eq_bar, ebar_eq_bar,
      bil_bar_mulVecE, Complex.conj_conj,
      bil_comm (bar (e i)) (mulVecE Aᴴ (bar (d j))),
      bil_bar_mulVecE, bil_comm (d i) (mulVecE A (e j))]
    ring
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hfac i j

end Match


/-! ## From Lifting II to `R`-positivity -/

section Assembly

variable {W : Type*} [Fintype W] [DecidableEq W] {ι : Type*} [Fintype ι] {s : ℕ}

omit [DecidableEq W] in
/-- The Choi pairing of `Φ_A ∘ τ` is the negative-sector quadratic form at the
conjugated frame, summed over the Kraus index. -/
theorem thetaPair_eq_qform_krausQ (A : ι → Matrix W W ℂ)
    (e d : Fin s → EuclideanSpace ℂ W) :
    thetaPair A (rankFactor e d)
      = qform (krausQ A (ptransposeUV (rankOne (delta (ebar e)) (delta (ebar e)))))
          (delta (ebar d)) := by
  rw [krausQ, qform_krausSum, thetaPair]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← qform_ptransposeUV_conj_frame (A a) e d]
  congr 2
  ext x y
  simp only [placeT_apply, Matrix.conjTranspose_apply, eq_comm]
  split_ifs with h
  · rfl
  · exact (map_zero (starRingEnd ℂ)).symm

omit [DecidableEq W] in
/-- `‖δ_{d̄}‖² = ‖C‖₂²` for the range factorization: conjugation is an isometry
and `eᵢ` is orthonormal. -/
theorem norm_delta_ebar_eq (e d : Fin s → EuclideanSpace ℂ W) (he : Orthonormal ℂ e) :
    ‖delta (ebar d)‖ ^ 2 = hsNormSq (rankFactor e d) := by
  rw [norm_delta, hsNormSq_rankFactor_eq e d he]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 2
  exact Finset.sum_congr rfl fun p _ => by simp [ebar_apply]

omit [DecidableEq W] in
/-- `⟪δ_ē, δ_{d̄}⟫ = Tr C`, by `eq:contraction-trace`. -/
theorem inner_delta_ebar_eq_trace (e d : Fin s → EuclideanSpace ℂ W) :
    inner ℂ (delta (ebar e)) (delta (ebar d)) = (rankFactor e d).trace := by
  rw [contraction_trace, PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun p _ => by
    simp only [RCLike.inner_apply', delta_apply, ebar_apply, Complex.conj_conj]
    ring

omit [DecidableEq W] in
/-- **Pair amplification in Choi form, at the exact rank.**

Lifting II form (B), run at the conjugated frame `ē` of the range factorization
and the test vector `δ_{d̄}`. -/
theorem thetaPositive_at_rank {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β) {e d : Fin s → EuclideanSpace ℂ W}
    (hsym : ∀ f, IsFrameSymmetric (ebar e) (A f)) (hs : 0 < s) (he : Orthonormal ℂ e) :
    0 ≤ (thetaPair A (rankFactor e d)).re
        + β * ((s : ℝ) - 1) * (hsNormSq (rankFactor e d)
            - Complex.normSq (rankFactor e d).trace / s) := by
  have hb := orthonormal_ebar he
  have hkey := qform_krausQ_ptransposeUV_ge (A := A) (β := β) (e := ebar e) hβ hJ
    hsym hs hb (delta (ebar d))
  rw [← thetaPair_eq_qform_krausQ, norm_delta_ebar_eq e d he,
    inner_delta_ebar_eq_trace e d] at hkey
  exact hkey

omit [DecidableEq W] in
/-- The unprotected pair lift at the exact rank. -/
theorem thetaUnprotectedPositive_at_rank
    {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β)
    {e d : Fin s → EuclideanSpace ℂ W}
    (hs : 0 < s) (he : Orthonormal ℂ e) :
    0 ≤ (thetaPair A (rankFactor e d)).re
        + β * ((s : ℝ) - 1) * hsNormSq (rankFactor e d) := by
  have hkey := qform_krausQ_ptransposeUV_ge_of_norm
    (A := A) (β := β) (e := ebar e) hβ hJ hs
    (orthonormal_ebar he) (delta (ebar d))
  rw [← thetaPair_eq_qform_krausQ, norm_delta_ebar_eq e d he] at hkey
  exact hkey

/-- The coefficient `(r-1)β(‖C‖₂² - |Tr C|²/r)` increases with `r`, by the
trace-rank bound.  Clearing denominators, the difference is
`(R - r₀)(r₀R‖C‖₂² - |Tr C|²)/(r₀R)`, and both factors are nonnegative. -/
private theorem coeff_mono {a t β : ℝ} (hβ : 0 ≤ β) (ha : 0 ≤ a) {r₀ R : ℕ}
    (hr₀ : 0 < r₀) (hle : r₀ ≤ R) (htr : t ≤ r₀ * a) :
    β * ((r₀ : ℝ) - 1) * (a - t / r₀) ≤ ((R : ℝ) - 1) * β * (a - t / R) := by
  have h1 : (1 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
  have h2 : (r₀ : ℝ) ≤ (R : ℝ) := by exact_mod_cast hle
  have hr0 : (0 : ℝ) < (r₀ : ℝ) := by linarith
  have hRp : (0 : ℝ) < (R : ℝ) := by linarith
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := le_trans h1 h2
  have hnum : 0 ≤ ((R : ℝ) - r₀) * ((r₀ : ℝ) * R * a - t) := by
    have hhint : 0 ≤ (r₀ : ℝ) * a * ((R : ℝ) - 1) :=
      mul_nonneg (mul_nonneg (le_of_lt hr0) ha) (by linarith)
    have hkey : 0 ≤ (r₀ : ℝ) * R * a - t := by nlinarith
    exact mul_nonneg (by linarith) hkey
  have hdiff : ((R : ℝ) - 1) * (a - t / R) - ((r₀ : ℝ) - 1) * (a - t / r₀)
      = ((R : ℝ) - r₀) * ((r₀ : ℝ) * R * a - t) / ((r₀ : ℝ) * R) := by
    field_simp
    ring
  have hge : 0 ≤ ((R : ℝ) - 1) * (a - t / R) - ((r₀ : ℝ) - 1) * (a - t / r₀) := by
    rw [hdiff]
    positivity
  nlinarith [mul_nonneg hβ hge]

/-- **Pair amplification in Choi form** (`thm:pair-amplification`).

`Θ^Φ_{R,λ}` is `R`-positive at `λ = (R-1)β₂(Φ)`, for any completely positive `Φ`
with transpose-symmetric Kraus operators.  This is the general statement that
`Theorem.lean` proves only for `Λ_U ⊗ Λ_V`, and it needs no contraction identity:
the range factorization supplies the frame, and Lifting II does the rest. -/
theorem thetaPositive_of_choiTwoBound {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β) (hsym : ∀ f, (A f)ᵀ = A f) (R : ℕ) :
    ThetaPositive A R (((R : ℝ) - 1) * β) := by
  intro C hrank
  rcases eq_or_ne C 0 with rfl | hC
  · simp [thetaPair, hsInner, hsNormSq]
  · have hr₀ : 0 < C.rank := rank_pos_of_ne_zero hC
    obtain ⟨e, d, he, hCeq⟩ := exists_rankFactor_rank C
    have hat := thetaPositive_at_rank (A := A) hβ hJ (d := d)
      (fun f => isFrameSymmetric_of_transpose_eq (hsym f) _) hr₀ he
    rw [← hCeq] at hat
    have hmono := coeff_mono (a := hsNormSq C) (t := Complex.normSq C.trace) hβ
      (hsNormSq_nonneg C) hr₀ hrank (normSq_trace_le_rank C)
    linarith

/-- **Unprotected pair amplification in Choi form.**

No transpose-parity hypothesis is needed when the trace direction is not
removed from the correction. -/
theorem thetaUnprotectedPositive_of_choiTwoBound
    {A : ι → Matrix W W ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β) (R : ℕ) :
    ThetaUnprotectedPositive A R (((R : ℝ) - 1) * β) := by
  intro C hrank
  rcases eq_or_ne C 0 with rfl | hC
  · simp [thetaPair, hsInner, hsNormSq]
  · have hr₀ : 0 < C.rank := rank_pos_of_ne_zero hC
    obtain ⟨e, d, he, hCeq⟩ := exists_rankFactor_rank C
    have hat := thetaUnprotectedPositive_at_rank
      (A := A) hβ hJ (d := d) hr₀ he
    rw [← hCeq] at hat
    have hcoeff :
        β * ((C.rank : ℝ) - 1) * hsNormSq C
          ≤ ((R : ℝ) - 1) * β * hsNormSq C := by
      have hrank' : (C.rank : ℝ) ≤ R := by exact_mod_cast hrank
      calc
        β * ((C.rank : ℝ) - 1) * hsNormSq C =
            ((C.rank : ℝ) - 1) * β * hsNormSq C := by ring
        _ ≤ ((R : ℝ) - 1) * β * hsNormSq C :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (sub_le_sub_right hrank' 1) hβ)
            (hsNormSq_nonneg C)
    linarith

/-- The protected lift remains valid when its local Choi constant is replaced
by a larger upper bound. -/
theorem thetaPositive_of_choiTwoBound_le
    {A : ι → Matrix W W ℂ} {β γ : ℝ} (hβ : 0 ≤ β)
    (hJ : ChoiTwoBound (choiOf A) β)
    (hsym : ∀ f, (A f)ᵀ = A f)
    {R : ℕ} (hR : 0 < R) (hβγ : β ≤ γ) :
    ThetaPositive A R (((R : ℝ) - 1) * γ) := by
  apply thetaPositive_mono hR
    (thetaPositive_of_choiTwoBound hβ hJ hsym R)
  have hR1 : (0 : ℝ) ≤ (R : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hR)
  exact mul_le_mul_of_nonneg_left hβγ hR1

end Assembly

end RankR
