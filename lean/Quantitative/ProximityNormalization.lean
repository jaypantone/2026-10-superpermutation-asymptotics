import Quantitative.CandidatePositivity
import Quantitative.GuardRelativeLoss

/-!
# Normalizing the two kinds of proximity deletion

The guard-variable and guard-free cases are alternatives. A common bound
for their maximum retains the prescribed coefficient 7118280 after the
finite catalogue is summed. The selected size is its actual floor count.
-/

namespace CoefficientTwoPrecision.ProximityNormalization

theorem selected_scaled (d M selected : Nat)
    (hhalf : sourceEta (d + 3) * (M : ℚ) ^ d / 2 ≤ selected) :
    (d + 3).factorial * M ^ d ≤ 4 * d.factorial * (sourceDegree (d + 3) + 1) * selected := by
  have hden : (0 : ℚ) < (4 * d.factorial * (sourceDegree (d + 3) + 1) : Nat) := by positivity
  have heq : sourceEta (d + 3) * (M : ℚ) ^ d / 2 =
      (((d + 3).factorial * M ^ d : Nat) : ℚ) /
        ((4 * d.factorial * (sourceDegree (d + 3) + 1) : Nat) : ℚ) := by
    simp only [sourceEta, Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat]
    have hfac : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
    have hdegree : (sourceDegree (d + 3) : ℚ) + 1 ≠ 0 := by positivity
    field_simp [hfac, hdegree] <;> ring
  rw [heq] at hhalf
  have h := (div_le_iff₀ hden).mp hhalf
  have hnat : (d + 3).factorial * M ^ d ≤ selected * (4 * d.factorial * (sourceDegree (d + 3) + 1)) := by
    exact_mod_cast h
  simpa only [Nat.mul_comm selected] using hnat

theorem coefficient_bound (d : Nat) :
    8 * d ^ 2 * (d + 1) * (d - 1) ^ 2 * (sourceDegree (d + 3) + 1) ≤
      1560 * (d + 3) ^ 13 := by
  have hp : d ^ 2 * (d + 1) * (d - 1) ^ 2 ≤ (d + 3) ^ 5 := by
    calc
      d ^ 2 * (d + 1) * (d - 1) ^ 2 ≤
          (d + 3) ^ 2 * (d + 3) * (d + 3) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (by omega))
          (Nat.pow_le_pow_left (by omega) 2)
      _ = (d + 3) ^ 5 := by ring
  have hpow : 1 ≤ (d + 3) ^ 8 := one_le_pow₀ (by omega)
  have hdegree : sourceDegree (d + 3) + 1 ≤ 65 * (d + 3) ^ 8 := by
    unfold sourceDegree
    omega
  calc
    8 * d ^ 2 * (d + 1) * (d - 1) ^ 2 * (sourceDegree (d + 3) + 1) =
        8 * (d ^ 2 * (d + 1) * (d - 1) ^ 2) * (sourceDegree (d + 3) + 1) := by ring
    _ ≤ 8 * (d + 3) ^ 5 * (65 * (d + 3) ^ 8) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 8 hp) hdegree
    _ = 520 * (d + 3) ^ 13 := by ring
    _ ≤ 1560 * (d + 3) ^ 13 := Nat.mul_le_mul_right _ (by decide)

theorem frame_bound_scaled (m M d guards selected : Nat) (hd : 1 ≤ d) (hmM : m ≤ M)
    (hselection : (d + 3).factorial * M ^ d ≤
      4 * d.factorial * (sourceDegree (d + 3) + 1) * selected) :
    m * (guards * (d + 3).factorial * (d + 1) * d * M ^ (d - 1) * (2 * (d - 1) ^ 2)) ≤
      (d - 1).factorial * (1560 * (d + 3) ^ 13 * guards * selected) := by
  have hpower : M * M ^ (d - 1) = M ^ d := by rw [← pow_succ', Nat.sub_add_cancel hd]
  have hfactorial : d.factorial = d * (d - 1).factorial :=
    (Nat.mul_factorial_pred (Nat.ne_of_gt hd)).symm
  calc
    m * (guards * (d + 3).factorial * (d + 1) * d * M ^ (d - 1) * (2 * (d - 1) ^ 2)) ≤
        M * (guards * (d + 3).factorial * (d + 1) * d * M ^ (d - 1) * (2 * (d - 1) ^ 2)) :=
      Nat.mul_le_mul_right _ hmM
    _ = (guards * (d + 1) * d * (2 * (d - 1) ^ 2)) *
        ((d + 3).factorial * (M * M ^ (d - 1))) := by ring
    _ = (guards * (d + 1) * d * (2 * (d - 1) ^ 2)) * ((d + 3).factorial * M ^ d) := by rw [hpower]
    _ ≤ (guards * (d + 1) * d * (2 * (d - 1) ^ 2)) *
        (4 * d.factorial * (sourceDegree (d + 3) + 1) * selected) := Nat.mul_le_mul_left _ hselection
    _ = (d - 1).factorial *
        ((8 * d ^ 2 * (d + 1) * (d - 1) ^ 2 * (sourceDegree (d + 3) + 1)) * guards * selected) := by
      rw [hfactorial]
      ring
    _ ≤ (d - 1).factorial * (1560 * (d + 3) ^ 13 * guards * selected) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (coefficient_bound d)))

theorem guard_bound_scaled (m G d guards selected : Nat) (hG : 1 ≤ G)
    (hguards : m ^ G ≤ 2 * guards) :
    m * (selected * m ^ (G - 1) * (2 * (d - 1) ^ 2)) ≤
      1560 * (d + 3) ^ 13 * guards * selected := by
  have hpower : m * m ^ (G - 1) = m ^ G := by rw [← pow_succ', Nat.sub_add_cancel hG]
  have hp : (d - 1) ^ 2 ≤ (d + 3) ^ 13 :=
    (Nat.pow_le_pow_left (by omega) 2).trans
      (pow_le_pow_right₀ (show 1 ≤ d + 3 by omega) (by decide : 2 ≤ 13))
  have hc : 4 * (d - 1) ^ 2 ≤ 1560 * (d + 3) ^ 13 := by nlinarith
  calc
    m * (selected * m ^ (G - 1) * (2 * (d - 1) ^ 2)) =
        selected * (2 * (d - 1) ^ 2) * (m * m ^ (G - 1)) := by ring
    _ = selected * (2 * (d - 1) ^ 2) * m ^ G := by rw [hpower]
    _ ≤ selected * (2 * (d - 1) ^ 2) * (2 * guards) := Nat.mul_le_mul_left _ hguards
    _ = (4 * (d - 1) ^ 2) * guards * selected := by ring
    _ ≤ 1560 * (d + 3) ^ 13 * guards * selected :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)

theorem maximum_scaled (m M G d guards selected : Nat) (hd : 1 ≤ d) (hG : 1 ≤ G)
    (hmM : m ≤ M) (hguards : m ^ G ≤ 2 * guards)
    (hselection : (d + 3).factorial * M ^ d ≤
      4 * d.factorial * (sourceDegree (d + 3) + 1) * selected) :
    m * max ((d - 1).factorial * (selected * m ^ (G - 1) * (2 * (d - 1) ^ 2)))
      (guards * (d + 3).factorial * (d + 1) * d * M ^ (d - 1) * (2 * (d - 1) ^ 2)) ≤
        (d - 1).factorial * (1560 * (d + 3) ^ 13 * guards * selected) := by
  have hleft := Nat.mul_le_mul_left (d - 1).factorial
    (guard_bound_scaled m G d guards selected hG hguards)
  have hright := frame_bound_scaled m M d guards selected hd hmM hselection
  rcases le_total ((d - 1).factorial * (selected * m ^ (G - 1) * (2 * (d - 1) ^ 2)))
    (guards * (d + 3).factorial * (d + 1) * d * M ^ (d - 1) * (2 * (d - 1) ^ 2)) with h | h
  · rw [max_eq_right h]
    exact hright
  · rw [max_eq_left h]
    simpa only [mul_left_comm m] using hleft

end CoefficientTwoPrecision.ProximityNormalization

#print axioms CoefficientTwoPrecision.ProximityNormalization.selected_scaled
#print axioms CoefficientTwoPrecision.ProximityNormalization.maximum_scaled
