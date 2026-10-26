import Quantitative.SourceCountFactors

/-!
# Nonzero actual candidate counts at the construction threshold

The selected floor is at least half of its rational argument, which is
at least four. Both the guard count and the actual raw candidate count
are positive. These facts justify normalization of the surviving counts.
-/

namespace CoefficientTwoPrecision.CandidatePositivity

open CandidateFactorization ConstructionSize

theorem floor_half (x : ℚ) (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℚ) := by
  have h := Nat.lt_floor_add_one x
  linarith

theorem floor_argument (r m : Nat) (hr : 6 ≤ r)
    (hm : 4 * errorNumerator r (sourceWidth r) ≤ m) :
    4 ≤ sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3) := by
  have hm0 := (threshold_conditions r m hr hm).1
  have hM : m ≤ backgroundSize r m := by unfold backgroundSize; omega
  have hM1 : (1 : ℚ) ≤ backgroundSize r m := by
    exact_mod_cast (show 1 ≤ backgroundSize r m by omega)
  have hX : (m : ℚ) ≤ (backgroundSize r m : ℚ) ^ (r - 3) :=
    (show (m : ℚ) ≤ backgroundSize r m by exact_mod_cast hM).trans
      (le_self_pow₀ hM1 (by omega))
  have hEW := errorNumerator_ge_width r (sourceWidth r) (by omega)
  have h4W : (4 : ℚ) * sourceWidth r ≤ m := by
    exact_mod_cast (show 4 * sourceWidth r ≤ m by omega)
  have heta := eta_pos r hr
  have hscale := ElementaryCountFactors.sourceEta_width r hr
  have hfirst := mul_le_mul_of_nonneg_left h4W heta.le
  have hsecond := mul_le_mul_of_nonneg_left hX heta.le
  nlinarith

theorem selected_floor_half (r m : Nat) (hr : 6 ≤ r)
    (hm : 4 * errorNumerator r (sourceWidth r) ≤ m) :
    sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3) / 2 ≤
      (⌊sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)⌋₊ : ℚ) :=
  floor_half _ (by have := floor_argument r m hr hm; linarith)

theorem candidate_positive (r m : Nat) (hr : 6 ≤ r)
    (hm : 4 * errorNumerator r (sourceWidth r) ≤ m) : 0 < candidateCount r m := by
  have hsize := threshold_conditions r m hr hm
  have hguards : 0 < m.descFactorial (guardCount r) := Nat.descFactorial_pos.mpr (by omega)
  have hfloor : 0 < ⌊sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)⌋₊ :=
    Nat.floor_pos.mpr (by have := floor_argument r m hr hm; linarith)
  have hA := sourceA_pos r hr
  have hr0 : 0 < r := by omega
  unfold candidateCount sourceGridCount
  positivity

end CoefficientTwoPrecision.CandidatePositivity

#print axioms CoefficientTwoPrecision.CandidatePositivity.selected_floor_half
#print axioms CoefficientTwoPrecision.CandidatePositivity.candidate_positive
