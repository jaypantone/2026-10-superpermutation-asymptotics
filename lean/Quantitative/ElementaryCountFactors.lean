import Quantitative.RationalProducts
import Quantitative.ConstructionParameters

/-!
# Rounding and background-size factors in the source counts

These estimates apply to the actual floor size of the packed family and
to the powers of (m+G)/m in its row and charge counts.
-/

namespace CoefficientTwoPrecision.ElementaryCountFactors

theorem floor_ratio (x : ℚ) (hx : 0 < x) :
    1 - 1 / x ≤ (⌊x⌋₊ : ℚ) / x ∧ (⌊x⌋₊ : ℚ) / x ≤ 1 := by
  have hlo := Nat.lt_floor_add_one x
  have hhi := Nat.floor_le (le_of_lt hx)
  constructor
  · apply (le_div_iff₀ hx).mpr
    have hid : (1 - 1 / x) * x = x - 1 := by field_simp
    rw [hid]
    linarith
  · exact (div_le_one hx).mpr hhi

theorem sourceEta_width (r : Nat) (hr : 6 ≤ r) :
    1 ≤ (sourceWidth r : ℚ) * sourceEta r := by
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℚ) < r := by linarith
  have heta : 0 ≤ sourceEta r := by unfold sourceEta; positivity
  have hA : (0 : ℚ) ≤ sourceA r := Nat.cast_nonneg _
  have hprod : 0 ≤ (sourceA r : ℚ) * sourceEta r := mul_nonneg hA heta
  have hbase := (sourceRho_bounds r hr).1
  unfold sourceRho sourceBeta at hbase
  have hscaled := (le_div_iff₀ hr0).mp hbase
  have hpower : (1 : ℚ) ≤ (r : ℚ) ^ 2 := by nlinarith
  have hAR : 1 ≤ (sourceA r : ℚ) * sourceEta r := by
    have hlarge := mul_le_mul_of_nonneg_right hpower (le_of_lt hr0)
    by_contra hsmall
    have hstrict := mul_lt_mul_of_pos_right (lt_of_not_ge hsmall)
      (show (0 : ℚ) < (r : ℚ) - 2 by linarith)
    nlinarith
  have h := mul_le_mul hpower hAR (by norm_num : (0 : ℚ) ≤ 1) (sq_nonneg (r : ℚ))
  simpa only [sourceWidth, Nat.cast_mul, Nat.cast_pow, mul_assoc, one_mul] using h

theorem rounded_factor (eta X m W : ℚ) (heta : 0 < eta) (hm : 0 < m)
    (hW : 0 < W) (hX : m ≤ X) (hscale : 1 ≤ W * eta) :
    1 - W / m ≤ (⌊eta * X⌋₊ : ℚ) / (eta * X) ∧
      (⌊eta * X⌋₊ : ℚ) / (eta * X) ≤ 1 := by
  have hx : 0 < X := lt_of_lt_of_le hm hX
  have hp : 0 < eta * X := mul_pos heta hx
  have h := floor_ratio (eta * X) hp
  have hmult := mul_le_mul_of_nonneg_right hscale (le_of_lt hx)
  have hinv : 1 / (eta * X) ≤ W / m := by
    apply (div_le_div_iff₀ hp hm).mpr
    nlinarith [hmult]
  exact ⟨by linarith [h.1], h.2⟩

theorem background_power (m G exponent : Nat) (hm : 0 < m)
    (hsmall : 2 * exponent * G ≤ m) :
    1 ≤ (((m : ℚ) + G) / m) ^ exponent ∧
      (((m : ℚ) + G) / m) ^ exponent ≤ 1 + 2 * exponent * G / m := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hs : (exponent : ℚ) * G / m ≤ 1 / 2 := by
    apply (div_le_iff₀ hmQ).mpr
    have h := (show (2 : ℚ) * exponent * G ≤ m by exact_mod_cast hsmall)
    linarith
  have hsum : (∑ _i ∈ Finset.range exponent, (G : ℚ) / m) ≤ 1 / 2 := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_div_assoc] using hs
  have h := RationalProducts.rising_bounds (Finset.range exponent) (fun _ => (G : ℚ) / m)
    (fun _ _ => by positivity) hsum
  have hbase : (1 : ℚ) + G / m = ((m : ℚ) + G) / m := by field_simp
  simpa only [Finset.prod_const, Finset.card_range, Finset.sum_const, nsmul_eq_mul,
    hbase, ← mul_div_assoc, mul_assoc] using h

end CoefficientTwoPrecision.ElementaryCountFactors

#print axioms CoefficientTwoPrecision.ElementaryCountFactors.sourceEta_width
#print axioms CoefficientTwoPrecision.ElementaryCountFactors.rounded_factor
#print axioms CoefficientTwoPrecision.ElementaryCountFactors.background_power
