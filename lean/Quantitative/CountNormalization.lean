import Quantitative.SourceUniverse
import Quantitative.RationalTransfer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Normalization of the actual integer update expressions

The denominator is the cardinality of `SourceUniverse.sourceUniverse`.
These lemmas apply to the count expressions in the variable-width Stage
constructor. They prove arithmetic identities, not existence of a Stage.
-/

namespace CoefficientTwoPrecision

open SourceUniverse

theorem risingCount_pos (m W : ℕ) (hm : 0 < m) : 0 < risingCount m W := by
  induction W with
  | zero => simp [risingCount]
  | succ W ih =>
    exact Nat.mul_pos ih (by omega)

theorem risingCount_advance_factorial (m W : ℕ) :
    risingCount (m + 1) W * m.factorial = (m + W).factorial := by
  have h := risingCount_mul_factorial (m + 1) W (by omega)
  have hold : m + 1 - 1 = m := by omega
  have hnew : m + 1 + W - 1 = m + W := by omega
  simpa only [hold, hnew] using h

theorem risingCount_balance (m W : ℕ) (hm : 0 < m) :
    (m + W) * risingCount m W = m * risingCount (m + 1) W := by
  apply Nat.mul_right_cancel (Nat.factorial_pos (m - 1))
  calc
    ((m + W) * risingCount m W) * (m - 1).factorial =
        (m + W) * (risingCount m W * (m - 1).factorial) := by ring
    _ = (m + W) * (m + W - 1).factorial := by rw [risingCount_mul_factorial m W hm]
    _ = (m + W).factorial := Nat.mul_factorial_pred (by omega)
    _ = risingCount (m + 1) W * m.factorial := (risingCount_advance_factorial m W).symm
    _ = (m * risingCount (m + 1) W) * (m - 1).factorial := by
      rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hm)]
      ring

theorem integer_update_mass (m W R P B : ℕ) (hm : 0 < m)
    (hB : B ≤ risingCount m W) :
    (risingCount (m + 1) W * R + (m + W) * P * B) +
      (m + W) * (P * (risingCount m W - B)) =
        risingCount (m + 1) W * (R + m * P) := by
  calc
    (risingCount (m + 1) W * R + (m + W) * P * B) +
        (m + W) * (P * (risingCount m W - B)) =
        risingCount (m + 1) W * R + (m + W) * P *
          (B + (risingCount m W - B)) := by ring
    _ = risingCount (m + 1) W * R + (m + W) * P * risingCount m W := by
      rw [Nat.add_sub_of_le hB]
    _ = risingCount (m + 1) W * R + ((m + W) * risingCount m W) * P := by ring
    _ = risingCount (m + 1) W * R + (m * risingCount (m + 1) W) * P := by
      rw [risingCount_balance m W hm]
    _ = risingCount (m + 1) W * (R + m * P) := by ring

theorem integer_update_mass_factorial (m W R P B : ℕ) (hm : 0 < m)
    (hB : B ≤ risingCount m W) (hmass : R + m * P = m.factorial) :
    (risingCount (m + 1) W * R + (m + W) * P * B) +
      (m + W) * (P * (risingCount m W - B)) = (m + W).factorial := by
  rw [integer_update_mass m W R P B hm hB, hmass, risingCount_advance_factorial]

theorem normalized_charge_update (m W Q P q : ℕ) (hm : 0 < m) :
    ((risingCount (m + 1) W * Q + (m + W) * P * q : ℕ) : ℚ) /
        ((m + W).factorial : ℚ) =
      (Q : ℚ) / (m.factorial : ℚ) +
        ((P : ℚ) / ((m - 1).factorial : ℚ)) * ((q : ℚ) / (risingCount m W : ℚ)) := by
  have hA : (risingCount (m + 1) W : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (risingCount_pos (m + 1) W (by omega)))
  have hD : (risingCount m W : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (risingCount_pos m W hm))
  have hF : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hS : ((m - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m - 1)
  have hM : (m + W : ℚ) ≠ 0 := by exact_mod_cast (show m + W ≠ 0 by omega)
  have hinherited : ((risingCount (m + 1) W * Q : ℕ) : ℚ) /
      ((m + W).factorial : ℚ) = (Q : ℚ) / (m.factorial : ℚ) := by
    rw [← risingCount_advance_factorial m W]
    push_cast
    field_simp [hA, hF] <;> ring
  have hnew : (((m + W) * P * q : ℕ) : ℚ) / ((m + W).factorial : ℚ) =
      ((P : ℚ) / ((m - 1).factorial : ℚ)) * ((q : ℚ) / (risingCount m W : ℚ)) := by
    rw [← Nat.mul_factorial_pred (show m + W ≠ 0 by omega),
      ← risingCount_mul_factorial m W hm]
    push_cast
    field_simp [hM, hD, hS] <;> ring
  rw [Nat.cast_add, add_div, hinherited, hnew]

theorem normalized_circle_update (m W c P a : ℕ) (hm : 0 < m) :
    ((risingCount m W * c + P * a : ℕ) : ℚ) / ((m + W - 1).factorial : ℚ) =
      (c : ℚ) / ((m - 1).factorial : ℚ) +
        ((P : ℚ) / ((m - 1).factorial : ℚ)) * ((a : ℚ) / (risingCount m W : ℚ)) := by
  have hD : (risingCount m W : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (risingCount_pos m W hm))
  have hS : ((m - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m - 1)
  rw [← risingCount_mul_factorial m W hm]
  push_cast
  field_simp [hD, hS] <;> ring

theorem normalized_pending_update (m W P B : ℕ) (hm : 0 < m)
    (hB : B ≤ risingCount m W) :
    ((P * (risingCount m W - B) : ℕ) : ℚ) / ((m + W - 1).factorial : ℚ) =
      ((P : ℚ) / ((m - 1).factorial : ℚ)) * (1 - (B : ℚ) / (risingCount m W : ℚ)) := by
  have hD : (risingCount m W : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (risingCount_pos m W hm))
  have hS : ((m - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m - 1)
  rw [← risingCount_mul_factorial m W hm, Nat.cast_mul, Nat.cast_sub hB]
  push_cast
  field_simp [hD, hS] <;> ring

theorem normalized_total_update (m W Q c P q a : ℕ) (hm : 0 < m) :
    ((risingCount (m + 1) W * Q + (m + W) * P * q : ℕ) : ℚ) /
        ((m + W).factorial : ℚ) +
      ((risingCount m W * c + P * a : ℕ) : ℚ) / ((m + W - 1).factorial : ℚ) =
      ((Q : ℚ) / (m.factorial : ℚ) + (c : ℚ) / ((m - 1).factorial : ℚ)) +
        ((P : ℚ) / ((m - 1).factorial : ℚ)) *
          (((q : ℚ) + (a : ℚ)) / (risingCount m W : ℚ)) := by
  rw [normalized_charge_update m W Q P q hm, normalized_circle_update m W c P a hm]
  ring

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.integer_update_mass_factorial
#print axioms CoefficientTwoPrecision.normalized_pending_update
#print axioms CoefficientTwoPrecision.normalized_total_update
