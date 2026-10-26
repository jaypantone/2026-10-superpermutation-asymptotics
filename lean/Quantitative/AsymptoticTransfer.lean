import Quantitative.RealRate
import ConstAsym.Remainder8
import Mathlib.Analysis.Asymptotics.Defs

/-!
# The asymptotic consequence of the original-word finite bound

The input interface in this file is `OriginalWordFiniteBound61`.
It asserts the existence of actual covering words, using the original
coverage predicate. It is the finite construction theorem required by the
project, not an assumption about numerical recurrences. The results below
are explicitly conditional on this input.
MainTheorems supplies the proved finite-word construction.

The lower bound is the imported theorem `ConstAsym.lower2_ratio`, applied
to the original minimum length `ConstAsym.L`. Real powers enter only in
the final error estimate.
-/

namespace CoefficientTwoPrecision

open Filter Asymptotics

/-- The finite upper bound for the literal covering-word construction.
MainTheorems.original_finite_bound proves this proposition. -/
def OriginalWordFiniteBound61 : Prop :=
  ∀ r : ℕ, 6 ≤ r → 6 ∣ r → ∀ n : ℕ, transferConstant * r ^ 61 ≤ n →
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * SuperpermutationUpperBound.F3 n +
        (2 * r + 74) * (n - 4).factorial

/-- The finite word bound gives the corresponding upper ratio for the
original shortest length. -/
theorem conditional_upper_ratio (hwords : OriginalWordFiniteBound61)
    (n : ℕ) (hn : transferConstant * 6 ^ 61 ≤ n) :
    ((ConstAsym.L n : ℚ) - SuperpermutationBounds.F3 n) /
        ((n - 4).factorial : ℚ) ≤ 2 + 74 / (parameterFor n : ℚ) := by
  obtain ⟨hr, hdvd, hsize, _, _⟩ := parameterFor_bounds n hn
  have hr0 : 0 < parameterFor n :=
    lt_of_lt_of_le (by decide : (0 : ℕ) < 6) hr
  obtain ⟨w, hw, hlength⟩ := hwords (parameterFor n) hr hdvd n hsize
  have hword := (integer_bound_iff n (parameterFor n) hr0 w).1 hlength
  have hminimum : (ConstAsym.L n : ℚ) ≤ (w.length : ℚ) := by
    exact_mod_cast ConstAsym.L_le_length hw
  have hfac : (0 : ℚ) < ((n - 4).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos (n - 4)
  apply (div_le_iff₀ hfac).2
  linarith only [hminimum, hword]

/-- An explicit two-sided estimate, conditional only on the actual
finite-word upper theorem. The lower inequality uses the original
formalized lower bound. -/
theorem conditional_normalized_error_bound (hwords : OriginalWordFiniteBound61)
    (n : ℕ) (hn : transferConstant * 6 ^ 61 ≤ n) (hn8 : 8 ≤ n) :
    |((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
        ((n - 4).factorial : ℝ) - 2| ≤
      remainderConstant * (n : ℝ) ^ (-1 / 61 : ℝ) := by
  have hupperQ := conditional_upper_ratio hwords n hn
  have hupper : ((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
      ((n - 4).factorial : ℝ) ≤ 2 + 74 / (parameterFor n : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hupperQ
    push_cast at hcast
    exact hcast
  have hlowerQ := ConstAsym.lower2_ratio (le_trans (by decide : 7 ≤ 8) hn8)
  have hlower : 2 - 2 / ((n : ℝ) - 4) ≤
      ((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
        ((n - 4).factorial : ℝ) := by
    exact_mod_cast hlowerQ
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-1 / 61 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hupperRate := parameter_inverse_real_bound n hn
  have hlowerRate := lower_error_real_bound n hn8
  have hKlower := mul_le_mul_of_nonneg_right remainderConstant_bounds.1 hp
  have hKupper := mul_le_mul_of_nonneg_right remainderConstant_bounds.2 hp
  apply abs_le.2
  constructor
  · linarith only [hlower, hlowerRate, hKlower]
  · linarith only [hupper, hupperRate, hKupper]

/-- Restoring the factorial gives the actual error in shortest word
length, rather than only a normalized statement. -/
theorem conditional_length_error_bound (hwords : OriginalWordFiniteBound61)
    (n : ℕ) (hn : transferConstant * 6 ^ 61 ≤ n) (hn8 : 8 ≤ n) :
    |(ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ) -
        2 * ((n - 4).factorial : ℝ)| ≤
      remainderConstant * (((n - 4).factorial : ℝ) *
        (n : ℝ) ^ (-1 / 61 : ℝ)) := by
  have hfac : (0 : ℝ) < ((n - 4).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - 4)
  have hid : (ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ) -
      2 * ((n - 4).factorial : ℝ) =
      ((n - 4).factorial : ℝ) *
        (((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
          ((n - 4).factorial : ℝ) - 2) := by
    field_simp [ne_of_gt hfac]
  rw [hid, abs_mul, abs_of_pos hfac]
  have hscaled := mul_le_mul_of_nonneg_left
    (conditional_normalized_error_bound hwords n hn hn8) (le_of_lt hfac)
  calc
    ((n - 4).factorial : ℝ) *
        |((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
          ((n - 4).factorial : ℝ) - 2| ≤
      ((n - 4).factorial : ℝ) *
        (remainderConstant * (n : ℝ) ^ (-1 / 61 : ℝ)) := hscaled
    _ = remainderConstant * (((n - 4).factorial : ℝ) *
        (n : ℝ) ^ (-1 / 61 : ℝ)) := by ring

/-- The precise eventual real-power bound, with an explicit absolute
constant. The finite upper construction remains an explicit premise. -/
theorem conditional_eventual_error_bound (hwords : OriginalWordFiniteBound61) :
    ∀ᶠ n : ℕ in atTop,
      |(ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ) -
          2 * ((n - 4).factorial : ℝ)| ≤
        remainderConstant * (((n - 4).factorial : ℝ) *
          (n : ℝ) ^ (-1 / 61 : ℝ)) := by
  apply eventually_atTop.2
  refine ⟨max (transferConstant * 6 ^ 61) 8, fun n hn => ?_⟩
  exact conditional_length_error_bound hwords n
    (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn)

/-- Conditional formal version of
`L(n) = F3(n) + 2 (n-4)! + O((n-4)! n^(-1/61))`.
The functions here use the original `L` and `F3`; the remaining hypothesis
is exactly the finite original-word existence theorem. -/
theorem conditional_asymptotic_61 (hwords : OriginalWordFiniteBound61) :
    (fun n : ℕ => (ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ) -
        2 * ((n - 4).factorial : ℝ)) =O[atTop]
      (fun n : ℕ => ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 61 : ℝ)) := by
  apply isBigO_iff.2
  refine ⟨remainderConstant, ?_⟩
  apply (conditional_eventual_error_bound hwords).mono
  intro n hn
  have hscale : (0 : ℝ) ≤ ((n - 4).factorial : ℝ) *
      (n : ℝ) ^ (-1 / 61 : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hscale] using hn

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.conditional_upper_ratio
#print axioms CoefficientTwoPrecision.conditional_normalized_error_bound
#print axioms CoefficientTwoPrecision.conditional_length_error_bound
#print axioms CoefficientTwoPrecision.conditional_eventual_error_bound
#print axioms CoefficientTwoPrecision.conditional_asymptotic_61
