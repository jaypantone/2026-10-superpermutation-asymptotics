import Quantitative.CountingRatios
import Quantitative.CountNormalization
import Quantitative.ConstructionParameters

/-!
# Exact factors in the candidate counts

The powers of the enlarged background size M are retained explicitly.
The identities precede deletion and the perturbation of contour lengths.
-/

namespace CoefficientTwoPrecision.CandidateFactorization

theorem leading_row_identity (m M H eta guards selected D c : ℚ)
    (G d : Nat) (hm : m ≠ 0) (hM : M ≠ 0) (heta : eta ≠ 0)
    (hD : D ≠ 0) :
    (H * guards * selected) * c * M ^ 2 / D =
      (H * (c * eta) / m) *
        ((guards / m ^ G) * (selected / (eta * M ^ d)) *
          (M / m) ^ (d + 2) / (D / m ^ (G + d + 3))) := by
  simp only [div_pow, pow_add]
  field_simp

theorem leading_charge_identity (m M H eta guards selected D c : ℚ)
    (G d : Nat) (hm : m ≠ 0) (hM : M ≠ 0) (heta : eta ≠ 0)
    (hD : D ≠ 0) :
    (H * guards * selected) * c * M / D =
      (H * (c * eta) / m ^ 2) *
        ((guards / m ^ G) * (selected / (eta * M ^ d)) *
          (M / m) ^ (d + 1) / (D / m ^ (G + d + 3))) := by
  simp only [div_pow, pow_add]
  field_simp

def guardCount (r : Nat) : Nat := sourceWidth r - r

def backgroundSize (r m : Nat) : Nat := m + guardCount r

def candidateCount (r m : Nat) : Nat :=
  sourceGridCount r * m.descFactorial (guardCount r) *
    ⌊sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)⌋₊

def guardFactor (r m : Nat) : ℚ :=
  (m.descFactorial (guardCount r) : ℚ) / (m : ℚ) ^ guardCount r

def floorFactor (r m : Nat) : ℚ :=
  (⌊sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)⌋₊ : ℚ) /
    (sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3))

def backgroundFactor (r m : Nat) : ℚ := (backgroundSize r m : ℚ) / m

def insertionFactor (r m : Nat) : ℚ :=
  (SourceUniverse.risingCount m (sourceWidth r) : ℚ) / (m : ℚ) ^ sourceWidth r

theorem width_exponents (r : Nat) (hr : 6 ≤ r) :
    guardCount r + (r - 3) + 3 = sourceWidth r := by
  have hlower := sourceWidth_lower r hr
  have hlinear : r ≤ r ^ 2 := by nlinarith
  unfold guardCount
  omega

theorem eta_pos (r : Nat) (hr : 6 ≤ r) : 0 < sourceEta r := by
  have hbeta := (sourceBeta_bounds r hr).1
  unfold sourceBeta at hbeta
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  exact pos_of_mul_pos_right hbeta (by linarith)

theorem actual_leading_rows (r m : Nat) (hr : 6 ≤ r) (hm : 0 < m) :
    (candidateCount r m : ℚ) * ((r : ℚ) - 2) * (backgroundSize r m : ℚ) ^ 2 /
        (SourceUniverse.risingCount m (sourceWidth r) : ℚ) =
      (sourceRho r * sourceWidth r / m) *
        (guardFactor r m * floorFactor r m * backgroundFactor r m ^ (r - 3 + 2) /
          insertionFactor r m) := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hM : (backgroundSize r m : ℚ) ≠ 0 := by
    exact_mod_cast (show backgroundSize r m ≠ 0 by unfold backgroundSize; omega)
  have hD : (SourceUniverse.risingCount m (sourceWidth r) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (risingCount_pos m (sourceWidth r) hm)
  have h := leading_row_identity (m : ℚ) (backgroundSize r m : ℚ)
    (sourceGridCount r : ℚ) (sourceEta r) (m.descFactorial (guardCount r) : ℚ)
    (⌊sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)⌋₊ : ℚ)
    (SourceUniverse.risingCount m (sourceWidth r) : ℚ) ((r : ℚ) - 2)
    (guardCount r) (r - 3) hmQ hM (ne_of_gt (eta_pos r hr)) hD
  rw [width_exponents r hr, ← sourceBeta,
    source_coefficient_identity r (by omega)] at h
  simpa only [candidateCount, Nat.cast_mul, guardFactor, floorFactor,
    backgroundFactor, insertionFactor] using h

theorem actual_leading_charge (r m : Nat) (hr : 6 ≤ r) (hm : 0 < m) :
    (candidateCount r m : ℚ) * (2 * ((r : ℚ) - 1)) * (backgroundSize r m : ℚ) /
        (SourceUniverse.risingCount m (sourceWidth r) : ℚ) =
      ((2 * ((r : ℚ) - 1) / ((r : ℚ) - 2)) * sourceRho r * sourceWidth r / m ^ 2) *
        (guardFactor r m * floorFactor r m * backgroundFactor r m ^ (r - 3 + 1) /
          insertionFactor r m) := by
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hM : (backgroundSize r m : ℚ) ≠ 0 := by
    exact_mod_cast (show backgroundSize r m ≠ 0 by unfold backgroundSize; omega)
  have hD : (SourceUniverse.risingCount m (sourceWidth r) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (risingCount_pos m (sourceWidth r) hm)
  have hcoef : (sourceGridCount r : ℚ) * (2 * ((r : ℚ) - 1) * sourceEta r) =
      (2 * ((r : ℚ) - 1) / ((r : ℚ) - 2)) * sourceRho r * sourceWidth r := by
    rw [mul_assoc _ (sourceRho r), ← source_coefficient_identity r (by omega)]
    unfold sourceBeta
    field_simp [show (r : ℚ) - 2 ≠ 0 by linarith]
  have h := leading_charge_identity (m : ℚ) (backgroundSize r m : ℚ)
    (sourceGridCount r : ℚ) (sourceEta r) (m.descFactorial (guardCount r) : ℚ)
    (⌊sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)⌋₊ : ℚ)
    (SourceUniverse.risingCount m (sourceWidth r) : ℚ) (2 * ((r : ℚ) - 1))
    (guardCount r) (r - 3) hmQ hM (ne_of_gt (eta_pos r hr)) hD
  rw [width_exponents r hr, hcoef] at h
  simpa only [candidateCount, Nat.cast_mul, guardFactor, floorFactor,
    backgroundFactor, insertionFactor] using h

end CoefficientTwoPrecision.CandidateFactorization

#print axioms CoefficientTwoPrecision.CandidateFactorization.actual_leading_rows
#print axioms CoefficientTwoPrecision.CandidateFactorization.actual_leading_charge
