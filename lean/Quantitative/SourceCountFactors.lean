import Quantitative.ConstructionSize
import Quantitative.ElementaryCountFactors

/-!
# Error bounds for the exact candidate factors

All four factors here are defined by the actual guard count, selected floor
size, background size, and insertion denominator. The only size hypothesis
is the prescribed m >= 4E threshold.
-/

namespace CoefficientTwoPrecision.SourceCountFactors

open CandidateFactorization ConstructionSize

variable (r m : Nat) (hr : 6 ≤ r)
  (hm : 4 * errorNumerator r (sourceWidth r) ≤ m)

include hr hm

theorem guard_error :
    |guardFactor r m - 1| ≤ (sourceWidth r : ℚ) ^ 2 / (2 * m) := by
  obtain ⟨hm0, hGm, _, _, _, _, _⟩ := threshold_conditions r m hr hm
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  have h := CountingRatios.falling_bounds m (guardCount r) hm0 (by omega)
  have hG : (guardCount r : ℚ) ≤ sourceWidth r := by
    exact_mod_cast (Nat.sub_le (sourceWidth r) r)
  have hG0 : (0 : ℚ) ≤ guardCount r := by positivity
  have hW0 : (0 : ℚ) ≤ sourceWidth r := by positivity
  have hsq := pow_le_pow_left₀ hG0 hG 2
  have he : (guardCount r : ℚ) * ((guardCount r : ℚ) - 1) / (2 * m) ≤
      (sourceWidth r : ℚ) ^ 2 / (2 * m) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  change |(m.descFactorial (guardCount r) : ℚ) / (m : ℚ) ^ guardCount r - 1| ≤ _
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem floor_error :
    |floorFactor r m - 1| ≤ (sourceWidth r : ℚ) / m := by
  have hsize := threshold_conditions r m hr hm
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hsize.1
  have hM : m ≤ backgroundSize r m := by unfold backgroundSize; omega
  have hM1 : (1 : ℚ) ≤ backgroundSize r m := by exact_mod_cast (show 1 ≤ backgroundSize r m by omega)
  have hpower : (m : ℚ) ≤ (backgroundSize r m : ℚ) ^ (r - 3) :=
    (show (m : ℚ) ≤ backgroundSize r m by exact_mod_cast hM).trans
      (le_self_pow₀ hM1 (by omega))
  have hW : (0 : ℚ) < sourceWidth r := by
    exact_mod_cast (show 0 < sourceWidth r from width_positive r hr)
  have h := ElementaryCountFactors.rounded_factor (sourceEta r)
    ((backgroundSize r m : ℚ) ^ (r - 3)) m (sourceWidth r)
    (eta_pos r hr) hmQ hW hpower (ElementaryCountFactors.sourceEta_width r hr)
  change |(⌊sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)⌋₊ : ℚ) /
    (sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)) - 1| ≤ _
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem background_error (exponent : Nat) (he : exponent ≤ r) :
    |backgroundFactor r m ^ exponent - 1| ≤ 2 * (sourceWidth r : ℚ) ^ 2 / m := by
  obtain ⟨hm0, _, _, _, _, hscale, _⟩ := threshold_conditions r m hr hm
  have hsmall : 2 * exponent * guardCount r ≤ m := by
    exact (Nat.mul_le_mul_right (guardCount r) (Nat.mul_le_mul_left 2 he)).trans hscale
  have h := ElementaryCountFactors.background_power m (guardCount r) exponent hm0 hsmall
  have heW : (exponent : ℚ) ≤ sourceWidth r := by
    exact_mod_cast he.trans (width_linear r hr)
  have hGW : (guardCount r : ℚ) ≤ sourceWidth r := by exact_mod_cast (Nat.sub_le (sourceWidth r) r)
  have hprod := mul_le_mul heW hGW (by positivity : (0 : ℚ) ≤ guardCount r)
    (by positivity : (0 : ℚ) ≤ sourceWidth r)
  have hbound : 2 * (exponent : ℚ) * guardCount r / m ≤
      2 * (sourceWidth r : ℚ) ^ 2 / m := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  simp only [backgroundFactor, backgroundSize, Nat.cast_add]
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem insertion_error :
    |insertionFactor r m - 1| ≤ (sourceWidth r : ℚ) ^ 2 / m := by
  obtain ⟨hm0, _, _, _, hW, _, _⟩ := threshold_conditions r m hr hm
  have h := CountingRatios.rising_bounds m (sourceWidth r) hm0 hW
  unfold insertionFactor
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

end CoefficientTwoPrecision.SourceCountFactors

#print axioms CoefficientTwoPrecision.SourceCountFactors.guard_error
#print axioms CoefficientTwoPrecision.SourceCountFactors.floor_error
#print axioms CoefficientTwoPrecision.SourceCountFactors.background_error
#print axioms CoefficientTwoPrecision.SourceCountFactors.insertion_error
