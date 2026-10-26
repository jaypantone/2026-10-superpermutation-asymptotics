import Quantitative.CandidateFactorization

/-!
# Size conditions at the prescribed construction threshold

The single inequality m >= 4E supplies every elementary size condition
needed for the grid, packing, finite congruence counts and batch repairs.
-/

namespace CoefficientTwoPrecision.ConstructionSize

open CandidateFactorization

theorem monomial_bound (r W c a b : Nat) (hr : 1 ≤ r) (hW : 1 ≤ W)
    (hc : c ≤ 10 ^ 12) (ha : a ≤ 22) (hb : b ≤ 4) :
    c * r ^ a * W ^ b ≤ errorNumerator r W := by
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (pow_le_pow_right₀ hr ha))
    (pow_le_pow_right₀ hW hb)

theorem width_positive (r : Nat) (hr : 6 ≤ r) : 1 ≤ sourceWidth r := by
  have h := sourceWidth_lower r hr
  nlinarith

theorem width_linear (r : Nat) (hr : 6 ≤ r) : r ≤ sourceWidth r := by
  have h := sourceWidth_lower r hr
  nlinarith

theorem width_square (r : Nat) (hr : 6 ≤ r) :
    sourceWidth r ^ 2 ≤ errorNumerator r (sourceWidth r) := by
  simpa using monomial_bound r (sourceWidth r) 1 0 2 (by omega)
    (width_positive r hr) (by norm_num) (by decide) (by decide)

theorem threshold_conditions (r m : Nat) (hr : 6 ≤ r)
    (hm : 4 * errorNumerator r (sourceWidth r) ≤ m) :
    0 < m ∧ guardCount r < m ∧ backgroundSize r m < 2 * m ∧
      38 * r ^ 4 ≤ backgroundSize r m ∧ sourceWidth r ^ 2 ≤ m ∧
      2 * r * guardCount r ≤ m ∧
      (4 * r + 3) * (52 * r ^ 4 * sourceWidth r ^ 2) < backgroundSize r m := by
  have hW := width_positive r hr
  have hrW := width_linear r hr
  have hW2 := width_square r hr
  have hWsq : sourceWidth r ≤ sourceWidth r ^ 2 := by nlinarith
  have hG : guardCount r ≤ sourceWidth r := Nat.sub_le _ _
  have h0 : 0 < m := by omega
  have hGm : guardCount r < m := by omega
  have hM2 : backgroundSize r m < 2 * m := by unfold backgroundSize; omega
  have h38 : 38 * r ^ 4 ≤ errorNumerator r (sourceWidth r) := by
    simpa using monomial_bound r (sourceWidth r) 38 4 0 (by omega) hW
      (by norm_num) (by decide) (by decide)
  have hM : m ≤ backgroundSize r m := by unfold backgroundSize; omega
  have hrG : r * guardCount r ≤ sourceWidth r ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hrW hG
  have htworG : 2 * r * guardCount r ≤ m := by
    calc
      2 * r * guardCount r = 2 * (r * guardCount r) := by ring
      _ ≤ 2 * sourceWidth r ^ 2 := Nat.mul_le_mul_left 2 hrG
      _ ≤ m := by omega
  have hmon : r ^ 5 * sourceWidth r ^ 2 ≤ r ^ 22 * sourceWidth r ^ 4 :=
    Nat.mul_le_mul (pow_le_pow_right₀ (show 1 ≤ r by omega) (by decide : 5 ≤ 22))
      (pow_le_pow_right₀ hW (by decide : 2 ≤ 4))
  have hp : 0 < r ^ 22 * sourceWidth r ^ 4 := by positivity
  have hstrict : 260 * r ^ 5 * sourceWidth r ^ 2 <
      errorNumerator r (sourceWidth r) := by
    unfold errorNumerator
    nlinarith
  have hcover : (4 * r + 3) * (52 * r ^ 4 * sourceWidth r ^ 2) ≤
      260 * r ^ 5 * sourceWidth r ^ 2 := by
    calc
      (4 * r + 3) * (52 * r ^ 4 * sourceWidth r ^ 2) ≤
          (5 * r) * (52 * r ^ 4 * sourceWidth r ^ 2) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 260 * r ^ 5 * sourceWidth r ^ 2 := by ring
  exact ⟨h0, hGm, hM2, by omega, by omega, htworG, by omega⟩

end CoefficientTwoPrecision.ConstructionSize

#print axioms CoefficientTwoPrecision.ConstructionSize.threshold_conditions
