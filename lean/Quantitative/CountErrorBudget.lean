import Quantitative.RelativeProducts
import Quantitative.ConstructionParameters

/-!
# The explicit error budget for the global source counts

The terms below are the errors from rounding, guard positions, the two
deletions, contour lengths, connectors, background powers, and insertion
counts. Their sum fits inside one quarter of the prescribed numerator E.
-/

namespace CoefficientTwoPrecision.CountErrorBudget

def numerator (r W : ℚ) : ℚ :=
  W + W ^ 2 / 2 + 18 * r ^ 2 * W ^ 3 + 7118280 * r ^ 22 * W ^ 4 +
    (2 * r + 1040 * r ^ 5 * W ^ 2) + r + 2 * W ^ 2 + W ^ 2

theorem monomial_le (r W : ℚ) (hr : 1 ≤ r) (hW : 1 ≤ W)
    (a b : Nat) (ha : a ≤ 22) (hb : b ≤ 4) :
    r ^ a * W ^ b ≤ r ^ 22 * W ^ 4 := by
  exact mul_le_mul (pow_le_pow_right₀ hr ha) (pow_le_pow_right₀ hW hb)
    (by positivity) (by positivity)

theorem numerator_nonneg (r W : ℚ) (hr : 0 ≤ r) (hW : 0 ≤ W) :
    0 ≤ numerator r W := by
  unfold numerator
  positivity

theorem numerator_bound (r W : ℚ) (hr : 1 ≤ r) (hW : 1 ≤ W) :
    numerator r W ≤ 9000000 * r ^ 22 * W ^ 4 := by
  have h01 := monomial_le r W hr hW 0 1 (by decide) (by decide)
  have h02 := monomial_le r W hr hW 0 2 (by decide) (by decide)
  have h23 := monomial_le r W hr hW 2 3 (by decide) (by decide)
  have h10 := monomial_le r W hr hW 1 0 (by decide) (by decide)
  have h52 := monomial_le r W hr hW 5 2 (by decide) (by decide)
  simp only [pow_zero, pow_one, one_mul, mul_one] at h01 h02 h10
  have hp : 0 ≤ r ^ 22 * W ^ 4 := by positivity
  unfold numerator
  nlinarith

theorem budget_four (r W : Nat) (hr : 1 ≤ r) (hW : 1 ≤ W) :
    4 * numerator r W ≤ (errorNumerator r W : ℚ) := by
  have h := numerator_bound (r : ℚ) (W : ℚ)
    (by exact_mod_cast hr) (by exact_mod_cast hW)
  have hp : 0 ≤ (r : ℚ) ^ 22 * (W : ℚ) ^ 4 := by positivity
  simp only [errorNumerator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

theorem source_ratio_error {ι : Type} [DecidableEq ι]
    (S : Finset ι) (factor error : ι → ℚ) (denominator denError : ℚ)
    (r W m : Nat) (hr : 1 ≤ r) (hW : 1 ≤ W) (hm : 0 < m)
    (hsize : 4 * errorNumerator r W ≤ m)
    (he : ∀ i ∈ S, 0 ≤ error i)
    (hf : ∀ i ∈ S, |factor i - 1| ≤ error i)
    (hde : 0 ≤ denError) (hd : |denominator - 1| ≤ denError)
    (htotal : (∑ i ∈ S, error i) + denError ≤ numerator r W / m) :
    |(∏ i ∈ S, factor i) / denominator - 1| ≤
      (errorNumerator r W : ℚ) / m := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hfour := budget_four r W hr hW
  have hsizeQ : 4 * (errorNumerator r W : ℚ) ≤ m := by exact_mod_cast hsize
  have hsmall : numerator r W / m ≤ 1 / 4 := by
    apply (div_le_iff₀ hmQ).mpr
    nlinarith [numerator_nonneg (r : ℚ) (W : ℚ) (by positivity) (by positivity)]
  have h := RelativeProducts.ratio_error S factor error denominator denError
    he hf hde hd (htotal.trans hsmall)
  calc
    |(∏ i ∈ S, factor i) / denominator - 1| ≤
        4 * ((∑ i ∈ S, error i) + denError) := h
    _ ≤ 4 * (numerator r W / m) := mul_le_mul_of_nonneg_left htotal (by norm_num)
    _ = (4 * numerator r W) / m := by ring
    _ ≤ (errorNumerator r W : ℚ) / m := div_le_div_of_nonneg_right hfour (le_of_lt hmQ)

end CoefficientTwoPrecision.CountErrorBudget

#print axioms CoefficientTwoPrecision.CountErrorBudget.budget_four
#print axioms CoefficientTwoPrecision.CountErrorBudget.source_ratio_error
