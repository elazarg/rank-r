/-
The singular-value form of the Kronecker-sum application.
-/
import RankR.Applications.Kronecker.Inequality
import RankR.Library.Matrix.KyFan

namespace RankR

section KroneckerKyFan

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The literal singular-value form of the Kronecker-sum bound. -/
theorem kyFanSq_kroneckerSum_le {k : ℕ} (hk : 0 < k)
    (A B : Matrix D D ℂ) (hA : A.trace = 0) (hB : B.trace = 0)
    (hd : 0 < Fintype.card D) :
    kyFanSq k (kroneckerSum A B) ≤
      kroneckerKyFanCoeff k (Fintype.card D)
        * (hsNormSq A + hsNormSq B) :=
  kyFanSq_kroneckerSum_le_of_duality hk A B hA hB hd
    (kyFanFrobeniusDuality k (kroneckerSum A B))

/-- When `d ≤ 2k`, the Kronecker-sum Ky Fan coefficient simplifies to `k`. -/
theorem kyFanSq_kroneckerSum_le_of_card_le_two_mul {k : ℕ} (hk : 0 < k)
    (A B : Matrix D D ℂ) (hA : A.trace = 0) (hB : B.trace = 0)
    (hd : 0 < Fintype.card D) (hdk : Fintype.card D ≤ 2 * k) :
    kyFanSq k (kroneckerSum A B) ≤
      (k : ℝ) * (hsNormSq A + hsNormSq B) :=
  kyFanSq_kroneckerSum_le_of_card_le_two_mul_of_duality
    hk A B hA hB hd hdk
    (kyFanFrobeniusDuality k (kroneckerSum A B))

end KroneckerKyFan

end RankR
