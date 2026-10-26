import Quantitative.ContourAggregation
import Quantitative.SourceCountErrors
import Quantitative.CandidatePositivity

/-!
# Uniform estimates for the counts of an actual contour collection

The inputs are the retained fraction and the proved geometric facts for
each actual contour. This theorem derives the two relative errors; they
are not assumed as a numerical certificate. The canonical family adapter
uses precisely the row, charge and circle lists counted here.
-/

namespace CoefficientTwoPrecision.ActualCountEstimates

open SuperpermutationUpperBound SourceFamilyAdapter SourceAdvancement
open CandidateFactorization SourceCountErrors ContourAggregation

theorem connector_factor (q c k m : ℚ) (hq : 0 ≤ q) (hc : 0 ≤ c)
    (hk : 0 ≤ k) (hm : 0 < m) (hbound : c ≤ k * q / m) :
    ∃ v : ℚ, q + c = q * (1 + v) ∧ |v| ≤ k / m := by
  by_cases hzero : q = 0
  · have hc0 : c = 0 := by rw [hzero, mul_zero, zero_div] at hbound; linarith
    exact ⟨0, by simp [hzero, hc0], by simp; positivity⟩
  · have hq0 : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
    refine ⟨c / q, ?_, ?_⟩
    · field_simp
    · rw [abs_of_nonneg (div_nonneg hc hq)]
      apply (div_le_iff₀ hq0).mpr
      simpa only [div_mul_eq_mul_div, mul_comm k q] using hbound

theorem estimates {alphabet : List Nat} {h : Nat}
    (F : List (SourceContour alphabet h)) (r m K : Nat) (hr : 6 ≤ r)
    (hm : 4 * errorNumerator r (sourceWidth r) ≤ m)
    (hK : K ≤ 52 * r ^ 4 * sourceWidth r ^ 2)
    (hretention : |(F.length : ℚ) / candidateCount r m - 1| ≤
      deletionNumerator r (sourceWidth r) / m)
    (hperturb : ∀ C ∈ F,
      |(C.rows.length : ℚ) - (((r : ℚ) - 2) * (backgroundSize r m : ℚ) ^ 2 +
        ((r : ℚ) * ((r : ℚ) - 1) + 1) * backgroundSize r m)| ≤
      10 * (r : ℚ) ^ 2 * K * backgroundSize r m)
    (hcharge : ∀ C ∈ F,
      (C.rows.map Row.charge).sum = 2 * (r - 1) * backgroundSize r m)
    (hg : ∀ C ∈ F, portGcd C.rows h ≤ r - 1) :
    ∃ theta epsilon : ℚ,
      ((sourceRows F).length : ℚ) / (SourceUniverse.risingCount m (sourceWidth r) : ℚ) =
        sourceRho r * sourceWidth r / m * (1 + theta) ∧
      ((((sourceRows F).map Row.charge).sum : ℚ) + (circles F).length) /
          (SourceUniverse.risingCount m (sourceWidth r) : ℚ) =
        (2 * ((r : ℚ) - 1) / ((r : ℚ) - 2)) * sourceRho r * sourceWidth r / (m : ℚ) ^ 2 *
          (1 + epsilon) ∧
      |theta| ≤ (errorNumerator r (sourceWidth r) : ℚ) / m ∧
      |epsilon| ≤ (errorNumerator r (sourceWidth r) : ℚ) / m ∧
      ((circles F).length : ℚ) ≤ ((r : ℚ) - 1) *
        (((sourceRows F).map Row.charge).sum : ℚ) / m := by
  have hm0 := (ConstructionSize.threshold_conditions r m hr hm).1
  have hmM : m ≤ backgroundSize r m := by unfold backgroundSize; omega
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hcount0 : (candidateCount r m : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (CandidatePositivity.candidate_positive r m hr hm)
  let t : ℚ := (F.length : ℚ) / candidateCount r m
  have hcount : (F.length : ℚ) = candidateCount r m * t := by
    dsimp only [t]
    field_simp
  obtain ⟨u, hrows, hu⟩ := averaged_row_error F r m (backgroundSize r m)
    (sourceWidth r) K hr hm0 hmM hK hperturb
  have hconnect := connector_ratio F r m (backgroundSize r m) (by omega) hm0 hmM hcharge hg
  obtain ⟨v, hcost, hv⟩ := connector_factor (((sourceRows F).map Row.charge).sum)
    (circles F).length ((r : ℚ) - 1) m (by positivity) (by positivity)
    (by linarith) (by exact_mod_cast hm0) hconnect
  have hv' : |v| ≤ (r : ℚ) / m := hv.trans
    (div_le_div_of_nonneg_right (by linarith) (by positivity))
  have hchargeQ : (((sourceRows F).map Row.charge).sum : ℚ) =
      (F.length : ℚ) * (2 * ((r : ℚ) - 1) * backgroundSize r m) := by
    rw [uniform_charge F r (backgroundSize r m) hcharge]
    simp only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one, Nat.cast_ofNat]
  let rowFactor := guardFactor r m * floorFactor r m * t *
    backgroundFactor r m ^ (r - 3 + 2) * (1 + u) / insertionFactor r m
  let costFactor := guardFactor r m * floorFactor r m * t *
    backgroundFactor r m ^ (r - 3 + 1) * (1 + v) / insertionFactor r m
  refine ⟨rowFactor - 1, costFactor - 1, ?_, ?_, ?_, ?_, hconnect⟩
  · rw [hrows, hcount]
    calc
      ((candidateCount r m : ℚ) * t * (((r : ℚ) - 2) * (backgroundSize r m : ℚ) ^ 2) * (1 + u)) /
          (SourceUniverse.risingCount m (sourceWidth r) : ℚ) =
        ((candidateCount r m : ℚ) * ((r : ℚ) - 2) * (backgroundSize r m : ℚ) ^ 2 /
          (SourceUniverse.risingCount m (sourceWidth r) : ℚ)) * t * (1 + u) := by ring
      _ = _ := by
        rw [actual_leading_rows r m hr hm0]
        dsimp only [rowFactor]
        ring
  · rw [hcost, hchargeQ, hcount]
    calc
      ((candidateCount r m : ℚ) * t * (2 * ((r : ℚ) - 1) * backgroundSize r m) * (1 + v)) /
          (SourceUniverse.risingCount m (sourceWidth r) : ℚ) =
        ((candidateCount r m : ℚ) * (2 * ((r : ℚ) - 1)) * backgroundSize r m /
          (SourceUniverse.risingCount m (sourceWidth r) : ℚ)) * t * (1 + v) := by ring
      _ = _ := by
        rw [actual_leading_charge r m hr hm0]
        dsimp only [costFactor]
        ring
  · exact row_error r m hr hm t u hretention hu
  · exact charge_error r m hr hm t v hretention hv'

end CoefficientTwoPrecision.ActualCountEstimates

#print axioms CoefficientTwoPrecision.ActualCountEstimates.estimates
