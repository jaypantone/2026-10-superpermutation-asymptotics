import Quantitative.FiniteTransfer
import Quantitative.FiniteParameters
import Mathlib.Data.Nat.Find

/-!
# Completion costs and the integer choice of the parameter

The estimates in this file discharge the elementary dense-tail and joining
bounds used by the finite transfer. They do not construct the tail or the
word. The parameter is the largest multiple of six satisfying the integer
threshold; this is the integer formulation of rounding the positive
sixty-first root down to a multiple of six.
-/

namespace CoefficientTwoPrecision

theorem dense_cost_scaling (n a p tail : ℚ) (ha : 0 < a) (hp : 0 ≤ p)
    (hn : 0 ≤ n) (hroom : n ≤ 2 * a) (htail : tail ≤ 8 * p / a) :
    n * tail ≤ 16 * p := by
  have hrate : 0 ≤ 8 * p / a :=
    div_nonneg (mul_nonneg (by norm_num) hp) (le_of_lt ha)
  calc
    n * tail ≤ n * (8 * p / a) := mul_le_mul_of_nonneg_left htail hn
    _ ≤ (2 * a) * (8 * p / a) := mul_le_mul_of_nonneg_right hroom hrate
    _ = 16 * p := by field_simp [ne_of_gt ha] <;> ring

theorem joining_error_bound (n r : ℚ) (hr : 6 ≤ r) (hn : 96 * r ^ 2 ≤ n) :
    (32 * r + 96) / n + 2 / n ^ 2 ≤ 1 / r := by
  have hr0 : 0 < r := by linarith
  have hrr : r ≤ r ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right (show (1 : ℚ) ≤ r by linarith) (le_of_lt hr0)
    nlinarith only [hm]
  have hn0 : 0 < n := by nlinarith only [hn, hrr, hr0]
  have h2r : 0 < 2 * r := mul_pos (by norm_num) hr0
  have hscale := mul_le_mul_of_nonneg_right hr
    (show (0 : ℚ) ≤ 32 * r by nlinarith only [hr0])
  have hfirstNumerator : (32 * r + 96) * (2 * r) ≤ n := by
    nlinarith only [hn, hscale]
  have hfirst : (32 * r + 96) / n ≤ 1 / (2 * r) := by
    apply (div_le_div_iff₀ hn0 h2r).2
    simpa only [one_mul] using hfirstNumerator
  have hn2 : (2 : ℚ) ≤ n := by nlinarith only [hn, hrr, hr]
  have hn2r : 2 * r ≤ n := by nlinarith only [hn, hrr, hr0]
  have hproduct : 4 * r ≤ n ^ 2 := by
    have hm := mul_le_mul hn2r hn2 (by norm_num : (0 : ℚ) ≤ 2) (le_of_lt hn0)
    nlinarith only [hm]
  have hsecond : 2 / n ^ 2 ≤ 1 / (2 * r) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hn0) h2r).2
    nlinarith only [hproduct]
  calc
    (32 * r + 96) / n + 2 / n ^ 2 ≤ 1 / (2 * r) + 1 / (2 * r) :=
      add_le_add hfirst hsecond
    _ = 1 / r := by field_simp [ne_of_gt hr0] <;> ring

/-- The two final normalized masses contribute at most the joining
allowance. Their bounds are still explicit hypotheses. -/
theorem completion_mass_error_bound (n r z p : ℚ)
    (hr : 6 ≤ r) (hn : 96 * r ^ 2 ≤ n)
    (hz : z ≤ (32 * r + 96) / n ^ 2) (hp : p ≤ 1 / n ^ 3) :
    n * z + 2 * n * p ≤ 1 / r := by
  have hr0 : 0 < r := by linarith
  have hrpow : 0 < r ^ 2 := sq_pos_of_pos hr0
  have hn0 : 0 < n := by nlinarith only [hrpow, hn]
  have hz' : n * z ≤ (32 * r + 96) / n := by
    calc
      n * z ≤ n * ((32 * r + 96) / n ^ 2) :=
        mul_le_mul_of_nonneg_left hz (le_of_lt hn0)
      _ = (32 * r + 96) / n := by field_simp [ne_of_gt hn0] <;> ring
  have hp' : 2 * n * p ≤ 2 / n ^ 2 := by
    calc
      2 * n * p ≤ (2 * n) * (1 / n ^ 3) :=
        mul_le_mul_of_nonneg_left hp (by nlinarith only [hn0])
      _ = 2 / n ^ 2 := by field_simp [ne_of_gt hn0] <;> ring
  exact (add_le_add hz' hp').trans (joining_error_bound n r hr hn)

/-- The exact completion expression is bounded by the form used by the
transfer. In an application `h = n - 3` and `X = y + z`. -/
theorem completion_coefficient_le (n h y z p X : ℚ) (hhn : h ≤ n)
    (hX : 0 ≤ X) (hz : 0 ≤ z) (hp : 0 ≤ p) (hdef : X = y + z) :
    h * y + (2 * h - 1) * (z + p) ≤ n * X + n * z + 2 * n * p := by
  have hfirst := mul_le_mul_of_nonneg_right hhn hX
  have hsecond := mul_le_mul_of_nonneg_right (show h - 1 ≤ n by linarith) hz
  have hthird := mul_le_mul_of_nonneg_right (show 2 * h - 1 ≤ 2 * n by linarith) hp
  have heq : h * y + (2 * h - 1) * (z + p) =
      h * X + (h - 1) * z + (2 * h - 1) * p := by rw [hdef]; ring
  linarith only [hfirst, hsecond, hthird, heq]

/-- Search indices for an admissible parameter never exceed `n`. This
justifies the finite search bound without any extraction of real roots. -/
theorem parameter_index_le_bound (C n k : ℕ) (hC : 1 ≤ C)
    (hk : C * (6 * k) ^ 61 ≤ n) : k ≤ n := by
  calc
    k ≤ 6 * k := by omega
    _ ≤ (6 * k) ^ 61 := Nat.le_pow (by decide : 0 < 61)
    _ ≤ C * (6 * k) ^ 61 := by
      simpa only [one_mul] using Nat.mul_le_mul_right ((6 * k) ^ 61) hC
    _ ≤ n := hk

/-- The largest multiple of six satisfying the integer size condition. -/
def largestSixParameter (C n : ℕ) : ℕ :=
  6 * Nat.findGreatest (fun k => C * (6 * k) ^ 61 ≤ n) n

theorem largestSixParameter_bounds (C n : ℕ) (hC : 1 ≤ C)
    (hn : C * 6 ^ 61 ≤ n) :
    6 ≤ largestSixParameter C n ∧
      6 ∣ largestSixParameter C n ∧
      C * largestSixParameter C n ^ 61 ≤ n ∧
      n < C * (largestSixParameter C n + 6) ^ 61 ∧
      n < C * (2 * largestSixParameter C n) ^ 61 := by
  let P : ℕ → Prop := fun k => C * (6 * k) ^ 61 ≤ n
  let k := Nat.findGreatest P n
  have hOne : P 1 := by simpa only [P, Nat.mul_one] using hn
  have hn1 : 1 ≤ n := parameter_index_le_bound C n 1 hC hOne
  have hk1 : 1 ≤ k := Nat.le_findGreatest hn1 hOne
  have hk : P k := Nat.findGreatest_spec hn1 hOne
  have hnext : ¬ P (k + 1) := by
    intro hnext
    have hnextBound : k + 1 ≤ n := parameter_index_le_bound C n (k + 1) hC hnext
    exact (Nat.findGreatest_is_greatest (P := P) (n := n)
      (show Nat.findGreatest P n < k + 1 by dsimp [k]; omega) hnextBound) hnext
  have hupper : n < C * (6 * k + 6) ^ 61 := by
    have hstrict : n < C * (6 * (k + 1)) ^ 61 := Nat.lt_of_not_ge hnext
    simpa only [Nat.mul_add, Nat.mul_one] using hstrict
  have hdef : largestSixParameter C n = 6 * k := rfl
  simp only [hdef]
  refine ⟨by omega, ⟨k, rfl⟩, hk, hupper, ?_⟩
  exact hupper.trans_le (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_left (show 6 * k + 6 ≤ 2 * (6 * k) by omega) 61))

/-- The choice with the explicit constant from the source construction. -/
def parameterFor (n : ℕ) : ℕ := largestSixParameter transferConstant n

theorem parameterFor_bounds (n : ℕ) (hn : transferConstant * 6 ^ 61 ≤ n) :
    6 ≤ parameterFor n ∧ 6 ∣ parameterFor n ∧
      transferConstant * parameterFor n ^ 61 ≤ n ∧
      n < transferConstant * (parameterFor n + 6) ^ 61 ∧
      n < transferConstant * (2 * parameterFor n) ^ 61 := by
  exact largestSixParameter_bounds transferConstant n
    (by norm_num [transferConstant]) hn

/-- A rational form of the inverse sixty-first-root estimate. The
constant on the right is absolute once `C` is fixed. -/
theorem inverse_parameter_power_bound (C n r : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n)
    (hupper : n ≤ C * (2 * r) ^ 61) :
    ((74 : ℚ) / (r : ℚ)) ^ 61 ≤ ((148 : ℚ) ^ 61 * (C : ℚ)) / (n : ℚ) := by
  have hnatural : 74 ^ 61 * n ≤ (148 ^ 61 * C) * r ^ 61 := by
    calc
      74 ^ 61 * n ≤ 74 ^ 61 * (C * (2 * r) ^ 61) :=
        Nat.mul_le_mul_left (74 ^ 61) hupper
      _ = (148 ^ 61 * C) * r ^ 61 := by ring
  have hrQ : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcast : (74 : ℚ) ^ 61 * (n : ℚ) ≤
      ((148 : ℚ) ^ 61 * (C : ℚ)) * (r : ℚ) ^ 61 := by exact_mod_cast hnatural
  rw [div_pow]
  apply (le_div_iff₀ hnQ).2
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (pow_pos hrQ 61)).2 hcast

theorem parameterFor_inverse_power_bound (n : ℕ)
    (hn : transferConstant * 6 ^ 61 ≤ n) :
    ((74 : ℚ) / (parameterFor n : ℚ)) ^ 61 ≤
      ((148 : ℚ) ^ 61 * (transferConstant : ℚ)) / (n : ℚ) := by
  obtain ⟨hr, _, _, _, hupper⟩ := parameterFor_bounds n hn
  have hC : 1 ≤ transferConstant := by norm_num [transferConstant]
  have hn1 : 1 ≤ n := parameter_index_le_bound transferConstant n 1 hC
    (by simpa only [Nat.mul_one] using hn)
  exact inverse_parameter_power_bound transferConstant n (parameterFor n)
    (le_trans (by decide : (1 : ℕ) ≤ 6) hr) hn1 (le_of_lt hupper)

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.joining_error_bound
#print axioms CoefficientTwoPrecision.dense_cost_scaling
#print axioms CoefficientTwoPrecision.parameterFor_bounds
#print axioms CoefficientTwoPrecision.parameterFor_inverse_power_bound
