/-
Constant diagonals under unitary similarity.

The proof first constructs one trace-average diagonal entry by diagonalizing
the Hermitian part, averaging over Boolean sign vectors, and interpolating
their phases.  A finite-dimensional compression induction then produces the
full constant diagonal.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import RankR.Library.Matrix.Action

namespace RankR

open Matrix Finset ComplexConjugate

/-- A matrix has a constant diagonal up to unitary similarity. -/
def HasConstantDiagonal {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) : Prop :=
  ∃ U : Matrix (Fin q) (Fin q) ℂ,
    U ∈ Matrix.unitaryGroup (Fin q) ℂ
      ∧ ∀ i, (Uᴴ * A * U) i i = A.trace / (q : ℂ)

/-- The Parker--Fillmore property in a fixed dimension. -/
def HasConstantDiagonals (q : ℕ) : Prop :=
  ∀ A : Matrix (Fin q) (Fin q) ℂ, HasConstantDiagonal A

/-- A positive dimension has the trace-entry property if every matrix has a
unitary conjugate whose first diagonal entry is the trace average. -/
def HasTraceEntry (q : ℕ) : Prop :=
  ∀ A : Matrix (Fin q.succ) (Fin q.succ) ℂ,
    ∃ U : Matrix (Fin q.succ) (Fin q.succ) ℂ,
      U ∈ Matrix.unitaryGroup (Fin q.succ) ℂ
        ∧ (Uᴴ * A * U) 0 0 = A.trace / (q.succ : ℂ)

/-- Put a scalar in the first block and a matrix in the successor block. -/
def succBlock {q : ℕ} (a : ℂ) (V : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin q.succ) (Fin q.succ) ℂ :=
  fun i => Fin.cases
    (fun j => Fin.cases a (fun _ => 0) j)
    (fun i j => Fin.cases 0 (fun j => V i j) j)
    i

@[simp]
theorem succBlock_zero_zero {q : ℕ} (a : ℂ) (V : Matrix (Fin q) (Fin q) ℂ) :
    succBlock a V 0 0 = a :=
  rfl

@[simp]
theorem succBlock_zero_succ {q : ℕ} (a : ℂ) (V : Matrix (Fin q) (Fin q) ℂ)
    (j : Fin q) :
    succBlock a V 0 j.succ = 0 :=
  rfl

@[simp]
theorem succBlock_succ_zero {q : ℕ} (a : ℂ) (V : Matrix (Fin q) (Fin q) ℂ)
    (i : Fin q) :
    succBlock a V i.succ 0 = 0 :=
  rfl

@[simp]
theorem succBlock_succ_succ {q : ℕ} (a : ℂ) (V : Matrix (Fin q) (Fin q) ℂ)
    (i j : Fin q) :
    succBlock a V i.succ j.succ = V i j :=
  rfl

@[simp]
theorem succBlock_conjTranspose {q : ℕ} (a : ℂ)
    (V : Matrix (Fin q) (Fin q) ℂ) :
    (succBlock a V)ᴴ = succBlock (conj a) Vᴴ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [Matrix.conjTranspose_apply]

@[simp]
theorem succBlock_mul {q : ℕ} (a b : ℂ)
    (V W : Matrix (Fin q) (Fin q) ℂ) :
    succBlock a V * succBlock b W = succBlock (a * b) (V * W) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ]

@[simp]
theorem succBlock_one {q : ℕ} :
    succBlock 1 (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [(Fin.succ_ne_zero j).symm]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Fin.succ_ne_zero i]
    · simp [Matrix.one_apply]

/-- Adjoining a one-dimensional identity block preserves unitarity. -/
theorem succBlock_mem_unitary {q : ℕ} {V : Matrix (Fin q) (Fin q) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin q) ℂ) :
    succBlock 1 V ∈ Matrix.unitaryGroup (Fin q.succ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    succBlock_conjTranspose, map_one, succBlock_mul]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hV
  rw [hV]
  simpa only [one_mul] using (succBlock_one (q := q))

/-- The scalar corner is unchanged by conjugation with a successor block. -/
@[simp]
theorem succBlock_conjugate_zero_zero {q : ℕ}
    (V : Matrix (Fin q) (Fin q) ℂ)
    (B : Matrix (Fin q.succ) (Fin q.succ) ℂ) :
    ((succBlock 1 V)ᴴ * B * succBlock 1 V) 0 0 = B 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The successor principal submatrix is conjugated by the successor block. -/
theorem succBlock_conjugate_succ_succ {q : ℕ}
    (V : Matrix (Fin q) (Fin q) ℂ)
    (B : Matrix (Fin q.succ) (Fin q.succ) ℂ) (i j : Fin q) :
    ((succBlock 1 V)ᴴ * B * succBlock 1 V) i.succ j.succ =
      (Vᴴ * B.submatrix Fin.succ Fin.succ * V) i j := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Unitary conjugation preserves the trace. -/
theorem trace_unitary_conjugate {q : ℕ}
    {U : Matrix (Fin q) (Fin q) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin q) ℂ)
    (A : Matrix (Fin q) (Fin q) ℂ) :
    (Uᴴ * A * U).trace = A.trace := by
  rw [Matrix.trace_mul_cycle]
  have hrow : U * Uᴴ = (1 : Matrix (Fin q) (Fin q) ℂ) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  rw [hrow, Matrix.one_mul]

/-- The constant-diagonal property in dimension zero. -/
theorem hasConstantDiagonals_zero : HasConstantDiagonals 0 := by
  intro A
  refine ⟨1, by simp, ?_⟩
  intro i
  exact Fin.elim0 i

/-- The constant-diagonal property in dimension one. -/
theorem hasConstantDiagonals_one : HasConstantDiagonals 1 := by
  intro A
  refine ⟨1, by simp, ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [Matrix.trace]

/-- A trace-average first entry in every positive dimension yields the full
Parker--Fillmore constant-diagonal property by compression and induction. -/
theorem hasConstantDiagonals_of_traceEntry
    (hentry : ∀ q, HasTraceEntry q) :
    ∀ q, HasConstantDiagonals q := by
  intro q
  induction q with
  | zero => exact hasConstantDiagonals_zero
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        exact hasConstantDiagonals_one
      · intro A
        obtain ⟨U, hU, hfirst⟩ := hentry n A
        let B := Uᴴ * A * U
        let C := B.submatrix Fin.succ Fin.succ
        have htraceB : B.trace = A.trace := by
          exact trace_unitary_conjugate hU A
        have hfirstB : B 0 0 = A.trace / (n.succ : ℂ) :=
          hfirst
        have hsplit : B 0 0 + C.trace = B.trace := by
          simpa only [C] using Matrix.trace_submatrix_succ B
        have htraceC :
            C.trace = (n : ℂ) * (A.trace / (n.succ : ℂ)) := by
          have hdiff :
              C.trace = A.trace - A.trace / (n.succ : ℂ) := by
            rw [hfirstB, htraceB] at hsplit
            exact eq_sub_of_add_eq (by simpa only [add_comm] using hsplit)
          rw [hdiff]
          have hsucc : (n.succ : ℂ) ≠ 0 := by
            exact_mod_cast Nat.succ_ne_zero n
          field_simp
          rw [Nat.cast_succ]
          ring
        have hratio : C.trace / (n : ℂ) = A.trace / (n.succ : ℂ) := by
          have hncast : (n : ℂ) ≠ 0 := by
            exact_mod_cast hn
          apply (div_eq_iff hncast).2
          simpa only [mul_comm] using htraceC
        obtain ⟨V, hV, hdiagV⟩ := ih C
        let Q := succBlock 1 V
        let W := U * Q
        have hQ : Q ∈ Matrix.unitaryGroup (Fin n.succ) ℂ :=
          succBlock_mem_unitary hV
        have hW : W ∈ Matrix.unitaryGroup (Fin n.succ) ℂ :=
          (Matrix.unitaryGroup (Fin n.succ) ℂ).mul_mem hU hQ
        have hconj : Wᴴ * A * W = Qᴴ * B * Q := by
          simp only [W, Q, B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        refine ⟨W, hW, ?_⟩
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [hconj]
          simpa only [Q, succBlock_conjugate_zero_zero] using hfirstB
        · rw [hconj, succBlock_conjugate_succ_succ]
          exact (hdiagV i).trans hratio

section TraceEntry

variable {q : ℕ}

/-- The two real signs, regarded as complex scalars. -/
def boolSign (b : Bool) : ℂ :=
  if b then -1 else 1

@[simp]
theorem boolSign_false : boolSign false = 1 :=
  rfl

@[simp]
theorem boolSign_true : boolSign true = -1 :=
  rfl

@[simp]
theorem boolSign_not (b : Bool) : boolSign (!b) = -boolSign b := by
  cases b <;> simp

@[simp]
theorem conj_boolSign (b : Bool) : conj (boolSign b) = boolSign b := by
  cases b <;> simp

@[simp]
theorem boolSign_sq (b : Bool) : boolSign b * boolSign b = 1 := by
  cases b <;> simp

/-- The unnormalized sign vector associated with a Boolean labeling. -/
def boolSignVector (s : Fin q → Bool) : EuclideanSpace ℂ (Fin q) :=
  WithLp.toLp 2 fun i => boolSign (s i)

@[simp]
theorem boolSignVector_apply (s : Fin q → Bool) (i : Fin q) :
    boolSignVector s i = boolSign (s i) :=
  rfl

/-- Flip one coordinate of a Boolean labeling. -/
def flipBool (i : Fin q) (s : Fin q → Bool) : Fin q → Bool :=
  fun k => if k = i then !(s k) else s k

@[simp]
theorem flipBool_same (i : Fin q) (s : Fin q → Bool) :
    flipBool i s i = !(s i) := by
  simp [flipBool]

theorem flipBool_ne {i j : Fin q} (hij : j ≠ i) (s : Fin q → Bool) :
    flipBool i s j = s j := by
  simp [flipBool, hij]

@[simp]
theorem flipBool_involutive (i : Fin q) (s : Fin q → Bool) :
    flipBool i (flipBool i s) = s := by
  funext k
  by_cases hki : k = i
  · subst k
    simp
  · simp [flipBool, hki]

theorem flipBool_ne_self (i : Fin q) (s : Fin q → Bool) :
    flipBool i s ≠ s := by
  intro h
  have hi := congrFun h i
  simp only [flipBool_same] at hi
  exact Bool.not_ne_self (s i) hi

/-- Distinct Boolean sign coordinates are orthogonal after summing over all
labelings. -/
theorem sum_conj_boolSign_mul_boolSign (i j : Fin q) :
    ∑ s : Fin q → Bool, conj (boolSign (s i)) * boolSign (s j) =
      if i = j then (Fintype.card (Fin q → Bool) : ℂ) else 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · rw [if_neg hij]
    apply Finset.sum_involution
        (s := (Finset.univ : Finset (Fin q → Bool)))
        (fun s _ => flipBool i s)
    · intro s _
      rw [flipBool_same, flipBool_ne (Ne.symm hij), boolSign_not,
        map_neg, conj_boolSign]
      ring
    · intro s _ _
      exact flipBool_ne_self i s
    · intro s _
      exact Finset.mem_univ _
    · intro s _
      exact flipBool_involutive i s

/-- Summing the quadratic form over all Boolean sign vectors keeps only the
diagonal of the matrix. -/
theorem sum_qform_boolSignVector (A : Matrix (Fin q) (Fin q) ℂ) :
    ∑ s : Fin q → Bool, qform A (boolSignVector s) =
      (Fintype.card (Fin q → Bool) : ℂ) * A.trace := by
  classical
  simp only [qform, boolSignVector_apply]
  calc
    (∑ s : Fin q → Bool,
        ∑ i, ∑ j, conj (boolSign (s i)) * A i j * boolSign (s j)) =
        ∑ i, ∑ j, A i j *
          (∑ s : Fin q → Bool,
            conj (boolSign (s i)) * boolSign (s j)) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              ring
    _ = ∑ i, (Fintype.card (Fin q → Bool) : ℂ) * A i i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_eq_single i]
          · rw [sum_conj_boolSign_mul_boolSign, if_pos rfl]
            ring
          · intro j _ hji
            rw [sum_conj_boolSign_mul_boolSign, if_neg (Ne.symm hji)]
            simp
          · simp
    _ = (Fintype.card (Fin q → Bool) : ℂ) * A.trace := by
          rw [Matrix.trace, Finset.mul_sum]
          rfl

/-- Taking the adjoint conjugates a matrix quadratic form. -/
theorem qform_conjTranspose (A : Matrix (Fin q) (Fin q) ℂ)
    (z : EuclideanSpace ℂ (Fin q)) :
    qform Aᴴ z = conj (qform A z) := by
  simp only [qform, Matrix.conjTranspose_apply, map_sum, map_mul,
    RCLike.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [starRingEnd_self_apply]
  ring

/-- A diagonal quadratic form on a coordinatewise unit-modulus vector is its
trace. -/
theorem qform_diagonal_of_normSq_one
    (d : Fin q → ℂ) (z : EuclideanSpace ℂ (Fin q))
    (hz : ∀ i, Complex.normSq (z i) = 1) :
    qform (Matrix.diagonal d) z = (Matrix.diagonal d).trace := by
  classical
  rw [qform]
  calc
    (∑ i, ∑ j, conj (z i) * Matrix.diagonal d i j * z j) =
        ∑ i, conj (z i) * d i * z i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            simp [Ne.symm hji]
          · simp
    _ = ∑ i, d i := by
          apply Finset.sum_congr rfl
          intro i _
          calc
            conj (z i) * d i * z i =
                (conj (z i) * z i) * d i := by ring
            _ = d i := by
              rw [← Complex.normSq_eq_conj_mul_self, hz]
              simp
    _ = (Matrix.diagonal d).trace := by
          simp [Matrix.trace]

/-- If the Hermitian part of a traceless matrix is diagonal, then its
quadratic form is purely imaginary on every coordinatewise unit-modulus
vector. -/
theorem re_qform_eq_zero_of_hermitianPart_diagonal
    (A : Matrix (Fin q) (Fin q) ℂ) (d : Fin q → ℂ)
    (hdiag : A + Aᴴ = Matrix.diagonal d)
    (htrace : A.trace = 0)
    (z : EuclideanSpace ℂ (Fin q))
    (hz : ∀ i, Complex.normSq (z i) = 1) :
    (qform A z).re = 0 := by
  have htraceH : (A + Aᴴ).trace = 0 := by
    rw [Matrix.trace_add, Matrix.trace_conjTranspose, htrace]
    simp
  have hqH : qform (A + Aᴴ) z = 0 := by
    rw [hdiag, qform_diagonal_of_normSq_one d z hz, ← hdiag, htraceH]
  rw [qform_add, qform_conjTranspose, Complex.add_conj] at hqH
  have hre := congrArg Complex.re hqH
  simp only [Complex.ofReal_re, Complex.zero_re] at hre
  exact (mul_eq_zero.mp hre).resolve_left (by norm_num)

/-- Interpolate between two Boolean signs along the unit circle. -/
noncomputable def boolPhasePath (a b : Bool) (t : ℝ) : ℂ :=
  if a = b then boolSign a
  else boolSign a * Complex.exp ((Real.pi * t : ℂ) * Complex.I)

@[simp]
theorem boolPhasePath_zero (a b : Bool) :
    boolPhasePath a b 0 = boolSign a := by
  by_cases hab : a = b <;>
    simp [boolPhasePath, hab]

@[simp]
theorem boolPhasePath_one (a b : Bool) :
    boolPhasePath a b 1 = boolSign b := by
  cases a <;> cases b <;>
    simp [boolPhasePath, Complex.exp_pi_mul_I]

theorem normSq_boolPhasePath (a b : Bool) (t : ℝ) :
    Complex.normSq (boolPhasePath a b t) = 1 := by
  by_cases hab : a = b
  · subst b
    cases a <;> simp [boolPhasePath]
  · rw [boolPhasePath, if_neg hab, Complex.normSq_eq_norm_sq, norm_mul,
      Complex.norm_exp]
    have him :
        (((Real.pi * t : ℂ) * Complex.I).re) = 0 := by simp
    rw [him, Real.exp_zero]
    cases a <;> norm_num

theorem continuous_boolPhasePath (a b : Bool) :
    Continuous (boolPhasePath a b) := by
  by_cases hab : a = b
  · unfold boolPhasePath
    simp only [if_pos hab]
    exact continuous_const
  · unfold boolPhasePath
    simp only [if_neg hab]
    fun_prop

/-- Coordinatewise phase interpolation between Boolean sign vectors. -/
noncomputable def boolPhaseVector
    (a b : Fin q → Bool) (t : ℝ) : EuclideanSpace ℂ (Fin q) :=
  WithLp.toLp 2 fun i => boolPhasePath (a i) (b i) t

@[simp]
theorem boolPhaseVector_apply
    (a b : Fin q → Bool) (t : ℝ) (i : Fin q) :
    boolPhaseVector a b t i = boolPhasePath (a i) (b i) t :=
  rfl

@[simp]
theorem boolPhaseVector_zero (a b : Fin q → Bool) :
    boolPhaseVector a b 0 = boolSignVector a := by
  ext i
  simp

@[simp]
theorem boolPhaseVector_one (a b : Fin q → Bool) :
    boolPhaseVector a b 1 = boolSignVector b := by
  ext i
  simp

theorem normSq_boolPhaseVector
    (a b : Fin q → Bool) (t : ℝ) (i : Fin q) :
    Complex.normSq (boolPhaseVector a b t i) = 1 :=
  normSq_boolPhasePath (a i) (b i) t

/-- A quadratic form is continuous along a coordinatewise Boolean phase
interpolation. -/
theorem continuous_qform_boolPhaseVector
    (A : Matrix (Fin q) (Fin q) ℂ) (a b : Fin q → Bool) :
    Continuous fun t : ℝ => qform A (boolPhaseVector a b t) := by
  simp only [qform, boolPhaseVector_apply]
  apply continuous_finsetSum Finset.univ
  intro i _
  apply continuous_finsetSum Finset.univ
  intro j _
  exact ((continuous_boolPhasePath (a i) (b i)).star.mul_const (A i j)).mul
    (continuous_boolPhasePath (a j) (b j))

/-- A traceless matrix with diagonal Hermitian part has a coordinatewise
unit-modulus vector on which its quadratic form vanishes. -/
theorem exists_unimodular_qform_eq_zero_of_hermitianPart_diagonal
    (A : Matrix (Fin q) (Fin q) ℂ) (d : Fin q → ℂ)
    (hdiag : A + Aᴴ = Matrix.diagonal d)
    (htrace : A.trace = 0) :
    ∃ z : EuclideanSpace ℂ (Fin q),
      (∀ i, Complex.normSq (z i) = 1) ∧ qform A z = 0 := by
  have hsum :
      ∑ s : Fin q → Bool, qform A (boolSignVector s) = 0 := by
    rw [sum_qform_boolSignVector, htrace, mul_zero]
  have hsumIm :
      ∑ s : Fin q → Bool, (qform A (boolSignVector s)).im = 0 := by
    have h := congrArg Complex.im hsum
    simpa only [Complex.im_sum, Complex.zero_im] using h
  have huniv :
      (Finset.univ : Finset (Fin q → Bool)).Nonempty :=
    ⟨fun _ => false, Finset.mem_univ _⟩
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le
    (f := fun s : Fin q → Bool => (qform A (boolSignVector s)).im)
    (g := fun _ => 0) huniv (by simp [hsumIm])
  obtain ⟨b, _, hb⟩ := Finset.exists_le_of_sum_le
    (f := fun _ : Fin q → Bool => 0)
    (g := fun s => (qform A (boolSignVector s)).im)
    huniv (by simp [hsumIm])
  let f : ℝ → ℝ :=
    fun t => (qform A (boolPhaseVector a b t)).im
  have hf : Continuous f :=
    Complex.continuous_im.comp (continuous_qform_boolPhaseVector A a b)
  have hzero : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
    constructor
    · simpa only [f, boolPhaseVector_zero] using ha
    · simpa only [f, boolPhaseVector_one] using hb
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : ℝ) 1 hf hzero
  refine ⟨boolPhaseVector a b t, normSq_boolPhaseVector a b t, ?_⟩
  apply Complex.ext
  · simpa only [Complex.zero_re] using
      re_qform_eq_zero_of_hermitianPart_diagonal A d hdiag htrace
        (boolPhaseVector a b t) (normSq_boolPhaseVector a b t)
  · simpa only [f, Complex.zero_im] using ht

/-- A unit vector can be chosen as the first column of a unitary matrix. -/
theorem exists_unitary_firstColumn
    (x : EuclideanSpace ℂ (Fin q.succ)) (hx : ‖x‖ = 1) :
    ∃ U : Matrix (Fin q.succ) (Fin q.succ) ℂ,
      U ∈ Matrix.unitaryGroup (Fin q.succ) ℂ ∧ ∀ i, U i 0 = x i := by
  let v : Fin q.succ → EuclideanSpace ℂ (Fin q.succ) := fun _ => x
  have hv : Orthonormal ℂ
      (({0} : Set (Fin q.succ)).restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    rw [if_pos rfl]
    change inner ℂ x x = 1
    rw [inner_self_eq_norm_sq_to_K, hx]
    norm_num
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq
      (by simp :
        Module.finrank ℂ (EuclideanSpace ℂ (Fin q.succ)) =
          Fintype.card (Fin q.succ))
  let U : Matrix (Fin q.succ) (Fin q.succ) ℂ :=
    (EuclideanSpace.basisFun (Fin q.succ) ℂ).toBasis.toMatrix ⇑b
  have hU : U ∈ Matrix.unitaryGroup (Fin q.succ) ℂ :=
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
      (EuclideanSpace.basisFun (Fin q.succ) ℂ) b
  have hb0 : b 0 = x := hb 0 (by simp)
  refine ⟨U, hU, ?_⟩
  intro i
  change ((EuclideanSpace.basisFun (Fin q.succ) ℂ).repr (b 0)) i = x i
  rw [EuclideanSpace.basisFun_repr, hb0]

/-- The first diagonal entry of a conjugate is the quadratic form at the
first column of the conjugating matrix. -/
theorem conjugate_zero_zero_eq_qform_of_firstColumn
    (A U : Matrix (Fin q.succ) (Fin q.succ) ℂ)
    (x : EuclideanSpace ℂ (Fin q.succ))
    (hU0 : ∀ i, U i 0 = x i) :
    (Uᴴ * A * U) 0 0 = qform A x := by
  simp only [Matrix.mul_apply]
  simp_rw [Matrix.conjTranspose_apply, hU0]
  calc
    (∑ j, (∑ i, conj (x i) * A i j) * x j) =
        ∑ j, ∑ i, conj (x i) * A i j * x j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, conj (x i) * A i j * x j :=
      Finset.sum_comm
    _ = qform A x := rfl

/-- A zero of the quadratic form at a unit vector becomes the first diagonal
entry of a unitary conjugate. -/
theorem exists_unitary_zeroEntry_of_unit_qform_eq_zero
    (A : Matrix (Fin q.succ) (Fin q.succ) ℂ)
    (x : EuclideanSpace ℂ (Fin q.succ))
    (hx : ‖x‖ = 1) (hxA : qform A x = 0) :
    ∃ U : Matrix (Fin q.succ) (Fin q.succ) ℂ,
      U ∈ Matrix.unitaryGroup (Fin q.succ) ℂ
        ∧ (Uᴴ * A * U) 0 0 = 0 := by
  obtain ⟨U, hU, hU0⟩ := exists_unitary_firstColumn x hx
  refine ⟨U, hU, ?_⟩
  rw [conjugate_zero_zero_eq_qform_of_firstColumn A U x hU0, hxA]

/-- Every traceless complex matrix has a unit vector at which its quadratic
form vanishes. -/
theorem exists_unit_qform_eq_zero_of_trace_eq_zero
    (A : Matrix (Fin q.succ) (Fin q.succ) ℂ)
    (htrace : A.trace = 0) :
    ∃ x : EuclideanSpace ℂ (Fin q.succ), ‖x‖ = 1 ∧ qform A x = 0 := by
  let H := A + Aᴴ
  have hH : H.IsHermitian := by
    change (A + Aᴴ)ᴴ = A + Aᴴ
    rw [Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
  let V : Matrix (Fin q.succ) (Fin q.succ) ℂ := hH.eigenvectorUnitary
  let d : Fin q.succ → ℂ := RCLike.ofReal ∘ hH.eigenvalues
  let B := Vᴴ * A * V
  have hV : V ∈ Matrix.unitaryGroup (Fin q.succ) ℂ :=
    SetLike.coe_mem hH.eigenvectorUnitary
  have htraceB : B.trace = 0 := by
    rw [trace_unitary_conjugate hV A, htrace]
  have hdiag : B + Bᴴ = Matrix.diagonal d := by
    have hspectral := hH.conjStarAlgAut_star_eigenvectorUnitary
    have hVB : B + Bᴴ = Vᴴ * H * V := by
      simp only [B, H, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      noncomm_ring
    rw [hVB]
    simpa only [V, d, Unitary.conjStarAlgAut_star_apply,
      Matrix.star_eq_conjTranspose] using hspectral
  obtain ⟨z, hzmod, hzB⟩ :=
    exists_unimodular_qform_eq_zero_of_hermitianPart_diagonal
      B d hdiag htraceB
  have hz0 : z 0 ≠ 0 := by
    intro hz
    have h := hzmod 0
    simp [hz] at h
  have hzne : z ≠ 0 := by
    intro hz
    apply hz0
    rw [hz]
    rfl
  have hnormz : ‖z‖ ≠ 0 := (norm_ne_zero_iff.mpr hzne)
  let x : EuclideanSpace ℂ (Fin q.succ) := ((‖z‖ : ℂ)⁻¹) • z
  have hxnorm : ‖x‖ = 1 := by
    simp [x, norm_smul, hnormz]
  have hxB : qform B x = 0 := by
    simp only [x]
    rw [qform_smul_vec, hzB, mul_zero]
  refine ⟨mulVecE V x, ?_, ?_⟩
  · have hVnorm : ‖mulVecE V x‖ = ‖x‖ := by
      have hone : mulVecE (1 : Matrix (Fin q.succ) (Fin q.succ) ℂ) x = x := by
        ext i
        simp only [mulVecE_apply, Matrix.one_apply, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
        inner_mulVecE_left, mulVecE_mul,
        show Vᴴ * V = 1 by
          simpa only [Matrix.star_eq_conjTranspose] using
            (Matrix.mem_unitaryGroup_iff'.mp hV),
        hone]
    rw [hVnorm, hxnorm]
  · have hq :
        qform A (mulVecE V x) = qform B x := by
      have h := qform_conj Vᴴ A x
      simpa only [B, Matrix.conjTranspose_conjTranspose] using h.symm
    rw [hq, hxB]

/-- Every positive dimension has the trace-entry property. -/
theorem hasTraceEntry (q : ℕ) : HasTraceEntry q := by
  intro A
  let c : ℂ := A.trace / (q.succ : ℂ)
  let A₀ : Matrix (Fin q.succ) (Fin q.succ) ℂ :=
    A - c • 1
  have htrace₀ : A₀.trace = 0 := by
    simp only [A₀, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp only [c]
    have hq : (q.succ : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero q
    simp only [smul_eq_mul, Fintype.card_fin]
    field_simp
    ring
  obtain ⟨x, hxnorm, hxzero⟩ :=
    exists_unit_qform_eq_zero_of_trace_eq_zero A₀ htrace₀
  have hxA : qform A x = c := by
    simp only [A₀, qform_sub, qform_smul, qform_one, hxnorm] at hxzero
    norm_num at hxzero
    exact sub_eq_zero.mp hxzero
  obtain ⟨U, hU, hU0⟩ := exists_unitary_firstColumn x hxnorm
  refine ⟨U, hU, ?_⟩
  rw [conjugate_zero_zero_eq_qform_of_firstColumn A U x hU0, hxA]

/-- **Parker--Fillmore constant-diagonal theorem.**  Every square complex
matrix is unitarily similar to a matrix with constant diagonal equal to its
trace average. -/
theorem hasConstantDiagonals (q : ℕ) : HasConstantDiagonals q :=
  hasConstantDiagonals_of_traceEntry hasTraceEntry q

end TraceEntry

end RankR
