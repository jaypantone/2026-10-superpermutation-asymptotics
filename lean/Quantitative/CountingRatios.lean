import Quantitative.RationalProducts
import Quantitative.SourceUniverse

/-!
# Relative estimates for the actual insertion and guard counts

The rising count is the size of the canonical insertion universe. The
falling count is the number of distinct labelled guard-cut assignments.
Their normalized products have elementary errors of order W^2/m and G^2/m.
-/

namespace CoefficientTwoPrecision.CountingRatios

open SourceUniverse RationalProducts

theorem sum_range_rat (W : Nat) :
    (∑ i ∈ Finset.range W, (i : ℚ)) = (W : ℚ) * ((W : ℚ) - 1) / 2 := by
  induction W with
  | zero => simp
  | succ W ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_errors (m W : Nat) :
    (∑ i ∈ Finset.range W, (i : ℚ) / m) =
      (W : ℚ) * ((W : ℚ) - 1) / (2 * (m : ℚ)) := by
  rw [← Finset.sum_div, sum_range_rat]
  ring

theorem rising_ratio (m W : Nat) (hm : 0 < m) :
    (risingCount m W : ℚ) / (m : ℚ) ^ W =
      ∏ i ∈ Finset.range W, (1 + (i : ℚ) / m) := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  induction W with
  | zero => simp [risingCount]
  | succ W ih =>
    rw [risingCount, Nat.cast_mul, Nat.cast_add, pow_succ, Finset.prod_range_succ, ← ih]
    field_simp

theorem rising_bounds (m W : Nat) (hm : 0 < m) (hsize : W ^ 2 ≤ m) :
    1 ≤ (risingCount m W : ℚ) / (m : ℚ) ^ W ∧
      (risingCount m W : ℚ) / (m : ℚ) ^ W ≤ 1 + (W : ℚ) ^ 2 / m := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  have hsizeQ : (W : ℚ) ^ 2 ≤ m := by exact_mod_cast hsize
  have hsum : (∑ i ∈ Finset.range W, (i : ℚ) / m) ≤ 1 / 2 := by
    rw [sum_errors, div_le_iff₀ (by positivity : (0 : ℚ) < 2 * m)]
    nlinarith [Nat.cast_nonneg (α := ℚ) W]
  have h := RationalProducts.rising_bounds (Finset.range W) (fun i => (i : ℚ) / m)
    (fun i _ => by positivity) hsum
  rw [← rising_ratio m W hm] at h
  refine ⟨h.1, h.2.trans ?_⟩
  rw [sum_errors]
  have hw : (0 : ℚ) ≤ W := Nat.cast_nonneg _
  have hdiff : 0 ≤ (W : ℚ) / m := by positivity
  have hid : 1 + (W : ℚ) ^ 2 / m -
      (1 + 2 * ((W : ℚ) * ((W : ℚ) - 1) / (2 * m))) = (W : ℚ) / m := by
    field_simp
    ring
  linarith

theorem falling_ratio (m G : Nat) (hm : 0 < m) (hG : G ≤ m) :
    (m.descFactorial G : ℚ) / (m : ℚ) ^ G =
      ∏ i ∈ Finset.range G, (1 - (i : ℚ) / m) := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  induction G with
  | zero => simp
  | succ G ih =>
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega), pow_succ,
      Finset.prod_range_succ, ← ih (by omega)]
    field_simp

theorem falling_bounds (m G : Nat) (hm : 0 < m) (hG : G ≤ m) :
    1 - (G : ℚ) * ((G : ℚ) - 1) / (2 * m) ≤
      (m.descFactorial G : ℚ) / (m : ℚ) ^ G ∧
      (m.descFactorial G : ℚ) / (m : ℚ) ^ G ≤ 1 := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  have hu (i : Nat) (hi : i ∈ Finset.range G) : 0 ≤ (i : ℚ) / m ∧ (i : ℚ) / m ≤ 1 := by
    refine ⟨by positivity, ?_⟩
    apply (div_le_one hm0).2
    exact_mod_cast (show i ≤ m by have := Finset.mem_range.mp hi; omega)
  have h := RationalProducts.falling_bounds (Finset.range G) (fun i => (i : ℚ) / m) hu
  rwa [sum_errors, ← falling_ratio m G hm hG] at h

end CoefficientTwoPrecision.CountingRatios

#print axioms CoefficientTwoPrecision.CountingRatios.rising_bounds
#print axioms CoefficientTwoPrecision.CountingRatios.falling_bounds
