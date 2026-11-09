import AlmanacDefs
import Quantitative.MainTheorems

/-!
# Links to the Superpermutation Almanac's definitions

`AlmanacSolution.lean` states two results with the Almanac's own definitions
from `AlmanacDefs.lean`. This module proves both from the released theorems in
`Quantitative.MainTheorems`. Those theorems use this project's covering
predicate `SuperpermutationBounds.Covers`, `Nat.factorial`, and the minimum
length `ConstAsym.L`. The first two lemmas show that `Covers` is the Almanac's
`IsSuperpermutation` and that the Almanac's `fact` is `Nat.factorial`.
-/

namespace AlmanacAdapter

/-- The Almanac's factorial is `Nat.factorial`. -/
theorem fact_eq (k : Nat) : Almanac.fact k = Nat.factorial k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Almanac.fact, Nat.factorial, ih]

/-- The project's covering predicate is the Almanac's superpermutation predicate. -/
theorem covers_iff {n : Nat} (w : Almanac.Word n) :
    SuperpermutationBounds.Covers w ↔ Almanac.IsSuperpermutation n w := by
  constructor
  · intro h p hp hl
    obtain ⟨u, v, huv⟩ := h p hl hp
    exact ⟨u, v, huv.symm⟩
  · intro h p hl hp
    obtain ⟨u, v, huv⟩ := h p hp hl
    exact ⟨u, v, huv.symm⟩

/-- For every `ε > 0` and all large `n`, some superpermutation on `n` symbols
has length at most `n! + (n-1)! + (n-2)! + (2 + ε)(n-4)!`.

Given `ε`, take `r = 6(m + 1)` with `m > 13 / ε`, so that `74 ≤ ε r`. The
finite theorem then gives, for `n ≥ 8·10¹²·352⁴·r⁶¹`, a covering word with
`r |w| ≤ r F₃(n) + (2r + 74)(n-4)!`. -/
theorem asymptotic_upper_four : Almanac.AsymptoticUpperAt 4 2 := by
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt ((13 : ℚ) / ε)
  refine ⟨8 * 10 ^ 12 * 352 ^ 4 * (6 * (m + 1)) ^ 61, fun n hn => ?_⟩
  obtain ⟨w, hw, hlen⟩ := CoefficientTwoPrecision.finite_covering_word n (6 * (m + 1))
    (by omega) (Dvd.intro _ rfl) hn
  refine ⟨w, (covers_iff w).1 hw, ?_⟩
  have hcast : (6 * ((m : ℚ) + 1)) * (w.length : ℚ) ≤
      (6 * ((m : ℚ) + 1)) * ((n.factorial : ℚ) + ((n - 1).factorial : ℚ) +
          ((n - 2).factorial : ℚ)) +
        (2 * (6 * ((m : ℚ) + 1)) + 74) * ((n - 4).factorial : ℚ) := by
    have h := (Nat.cast_le (α := ℚ)).2 hlen
    simpa [SuperpermutationUpperBound.F3] using h
  have hεm : 13 < ε * (m : ℚ) := by
    rw [div_lt_iff₀ hε] at hm
    linarith
  have hcoeff : 2 * (6 * ((m : ℚ) + 1)) + 74 ≤ (6 * ((m : ℚ) + 1)) * (2 + ε) := by
    nlinarith
  have hf : (0 : ℚ) ≤ ((n - 4).factorial : ℚ) := by positivity
  have hr : (0 : ℚ) < 6 * ((m : ℚ) + 1) := by positivity
  unfold Almanac.asymptoticFormAt
  simp only [fact_eq]
  apply le_of_mul_le_mul_left _ hr
  linear_combination hcast + mul_le_mul_of_nonneg_right hcoeff hf

/-- The constant in the released error bound is at most 400. -/
theorem remainderConstant_le : CoefficientTwoPrecision.remainderConstant ≤ 400 := by
  have h : ((CoefficientTwoPrecision.transferConstant : ℕ) : ℝ) ^ (1 / 61 : ℝ) ≤ 5 / 2 := by
    rw [one_div, Real.rpow_inv_le_iff_of_pos (by positivity) (by norm_num) (by norm_num),
      show (61 : ℝ) = ((61 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num [CoefficientTwoPrecision.transferConstant]
  unfold CoefficientTwoPrecision.remainderConstant
  linarith

/-- For every `n ≥ 8·10¹²·352⁴·6⁶¹`, the shortest length `S(n)` of a
superpermutation on `n` symbols satisfies
`|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 400 (n-4)! n^(-1/61)`.
The first part gives a superpermutation no longer than the upper end; the
second says that no superpermutation is shorter than the lower end. -/
def ExplicitError : Prop :=
  ∀ n : Nat, 8 * 10 ^ 12 * 352 ^ 4 * 6 ^ 61 ≤ n →
    (∃ w : Almanac.Word n, Almanac.IsSuperpermutation n w ∧
      (w.length : Real) ≤ (Almanac.fact n : Real) + (Almanac.fact (n - 1) : Real) +
        (Almanac.fact (n - 2) : Real) + 2 * (Almanac.fact (n - 4) : Real) +
        400 * (Almanac.fact (n - 4) : Real) * (n : Real) ^ (-1 / 61 : Real)) ∧
    ∀ w : Almanac.Word n, Almanac.IsSuperpermutation n w →
      (Almanac.fact n : Real) + (Almanac.fact (n - 1) : Real) +
        (Almanac.fact (n - 2) : Real) + 2 * (Almanac.fact (n - 4) : Real) -
        400 * (Almanac.fact (n - 4) : Real) * (n : Real) ^ (-1 / 61 : Real) ≤
          (w.length : Real)

/-- The explicit two-sided error bound, from
`CoefficientTwoPrecision.shortest_length_error`. -/
theorem explicit_error : ExplicitError := by
  intro n hn
  have hn8 : 8 ≤ n := le_trans (by norm_num) hn
  have herr := CoefficientTwoPrecision.shortest_length_error n (by exact hn) hn8
  have hf : (0 : ℝ) < ((n - 4).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-1 / 61 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK := remainderConstant_le
  have hF3 : ((SuperpermutationBounds.F3 n : ℚ) : ℝ) =
      (n.factorial : ℝ) + ((n - 1).factorial : ℝ) + ((n - 2).factorial : ℝ) := by
    simp [SuperpermutationBounds.F3]
  rw [hF3] at herr
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  rw [le_sub_iff_add_le, le_div_iff₀ hf] at hlo
  rw [sub_le_iff_le_add, div_le_iff₀ hf] at hhi
  have hslack : CoefficientTwoPrecision.remainderConstant * (n : ℝ) ^ (-1 / 61 : ℝ) *
      ((n - 4).factorial : ℝ) ≤ 400 * ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 61 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hK (mul_nonneg hp hf.le)
    linarith
  simp only [fact_eq]
  constructor
  · obtain ⟨w, hw, hwl⟩ := ConstAsym.L_spec n
    refine ⟨w, (covers_iff w).1 hw, ?_⟩
    rw [hwl]
    nlinarith
  · intro w hw
    have hmin : (ConstAsym.L n : ℝ) ≤ (w.length : ℝ) := by
      exact_mod_cast ConstAsym.L_le_length ((covers_iff w).2 hw)
    nlinarith

end AlmanacAdapter
