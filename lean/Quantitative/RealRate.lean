import Quantitative.CompletionEstimates
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The real exponent from the integer parameter choice

The construction and its transfer use rational arithmetic. This file takes
real sixty-first roots only after the integer parameter has been chosen.
No source family or covering-word hypothesis is used here.
-/

namespace CoefficientTwoPrecision

theorem parameter_threshold_pos (n : ℕ)
    (hn : transferConstant * 6 ^ 61 ≤ n) : 0 < n := by
  have hC : 1 ≤ transferConstant := by norm_num [transferConstant]
  have hn1 := parameter_index_le_bound transferConstant n 1 hC
    (by simpa only [Nat.mul_one] using hn)
  exact lt_of_lt_of_le Nat.zero_lt_one hn1

theorem parameter_inverse_real_bound (n : ℕ)
    (hn : transferConstant * 6 ^ 61 ≤ n) :
    (74 : ℝ) / (parameterFor n : ℝ) ≤
      148 * (transferConstant : ℝ) ^ (1 / 61 : ℝ) * (n : ℝ) ^ (-1 / 61 : ℝ) := by
  obtain ⟨hr, _, _, _, hupper⟩ := parameterFor_bounds n hn
  have hr0 : (0 : ℝ) < parameterFor n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 6) hr)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast parameter_threshold_pos n hn
  have hC0 : (0 : ℝ) < transferConstant := by norm_num [transferConstant]
  have hcast : (n : ℝ) ≤ (transferConstant : ℝ) * (2 * (parameterFor n : ℝ)) ^ 61 := by
    exact_mod_cast (le_of_lt hupper)
  have hroot := Real.rpow_le_rpow (le_of_lt hn0) hcast (by norm_num : (0 : ℝ) ≤ 1 / 61)
  have hrootPower : ((2 * (parameterFor n : ℝ)) ^ 61) ^ (1 / 61 : ℝ) =
      2 * (parameterFor n : ℝ) := by
    simpa only [one_div, Nat.cast_ofNat] using
      (Real.pow_rpow_inv_natCast (show (0 : ℝ) ≤ 2 * (parameterFor n : ℝ) by positivity)
        (by decide : (61 : ℕ) ≠ 0))
  rw [Real.mul_rpow (le_of_lt hC0) (by positivity), hrootPower] at hroot
  have hroot0 : (0 : ℝ) < (n : ℝ) ^ (1 / 61 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hscaled := mul_le_mul_of_nonneg_left hroot
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 74) (le_of_lt hr0))
  have hscaleIdentity : ((74 : ℝ) / (parameterFor n : ℝ)) *
      ((transferConstant : ℝ) ^ (1 / 61 : ℝ) * (2 * (parameterFor n : ℝ))) =
      148 * (transferConstant : ℝ) ^ (1 / 61 : ℝ) := by
    field_simp [ne_of_gt hr0] <;> ring
  rw [hscaleIdentity] at hscaled
  calc
    (74 : ℝ) / (parameterFor n : ℝ) ≤
        (148 * (transferConstant : ℝ) ^ (1 / 61 : ℝ)) / (n : ℝ) ^ (1 / 61 : ℝ) :=
      (le_div_iff₀ hroot0).2 hscaled
    _ = 148 * (transferConstant : ℝ) ^ (1 / 61 : ℝ) * (n : ℝ) ^ (-1 / 61 : ℝ) := by
      rw [show (-1 / 61 : ℝ) = -(1 / 61 : ℝ) by ring,
        Real.rpow_neg (le_of_lt hn0)]
      rfl

theorem lower_error_real_bound (n : ℕ) (hn : 8 ≤ n) :
    (2 : ℝ) / ((n : ℝ) - 4) ≤ 4 * (n : ℝ) ^ (-1 / 61 : ℝ) := by
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn8]
  have hn4 : (0 : ℝ) < (n : ℝ) - 4 := by linarith only [hn8]
  have hfirst : (2 : ℝ) / ((n : ℝ) - 4) ≤ 4 / (n : ℝ) := by
    apply (div_le_div_iff₀ hn4 hn0).2
    linarith only [hn8]
  have hpower := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ n by linarith only [hn8])
    (by norm_num : (-1 : ℝ) ≤ -1 / 61)
  rw [Real.rpow_neg_one] at hpower
  calc
    (2 : ℝ) / ((n : ℝ) - 4) ≤ 4 / (n : ℝ) := hfirst
    _ = 4 * (n : ℝ)⁻¹ := by rfl
    _ ≤ 4 * (n : ℝ) ^ (-1 / 61 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower (by norm_num)

noncomputable def remainderConstant : ℝ :=
  148 * (transferConstant : ℝ) ^ (1 / 61 : ℝ) + 4

theorem remainderConstant_bounds :
    4 ≤ remainderConstant ∧
      148 * (transferConstant : ℝ) ^ (1 / 61 : ℝ) ≤ remainderConstant := by
  have hp : (0 : ℝ) ≤ (transferConstant : ℝ) ^ (1 / 61 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold remainderConstant
  constructor <;> linarith only [hp]

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.parameter_inverse_real_bound
#print axioms CoefficientTwoPrecision.lower_error_real_bound
