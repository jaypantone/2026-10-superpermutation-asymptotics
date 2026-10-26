import Quantitative.SourceCountFactors
import Quantitative.CountErrorBudget

/-!
# Combining the actual source-count factors

Only retention and the perturbation of a surviving contour enter as inputs.
The remaining factors and all numerical constants are derived from their
definitions. The estimates use the same error numerator for rows and charge.
-/

namespace CoefficientTwoPrecision.SourceCountErrors

open CandidateFactorization SourceCountFactors

def deletionNumerator (r W : ℚ) : ℚ :=
  18 * r ^ 2 * W ^ 3 + 7118280 * r ^ 22 * W ^ 4

def rowNumerator (r W : ℚ) : ℚ := 2 * r + 1040 * r ^ 5 * W ^ 2

theorem combined_error (r m exponent : Nat) (hr : 6 ≤ r)
    (hm : 4 * errorNumerator r (sourceWidth r) ≤ m) (he : exponent ≤ r)
    (retention last : ℚ)
    (ht : |retention - 1| ≤ deletionNumerator r (sourceWidth r) / m)
    (hlast : |last - 1| ≤ (rowNumerator r (sourceWidth r) + r) / m) :
    |guardFactor r m * floorFactor r m * retention *
        backgroundFactor r m ^ exponent * last / insertionFactor r m - 1| ≤
      (errorNumerator r (sourceWidth r) : ℚ) / m := by
  let factor : Fin 5 → ℚ := fun i => match i.val with
    | 0 => guardFactor r m
    | 1 => floorFactor r m
    | 2 => retention
    | 3 => backgroundFactor r m ^ exponent
    | _ => last
  let error : Fin 5 → ℚ := fun i => match i.val with
    | 0 => (sourceWidth r : ℚ) ^ 2 / (2 * m)
    | 1 => (sourceWidth r : ℚ) / m
    | 2 => deletionNumerator r (sourceWidth r) / m
    | 3 => 2 * (sourceWidth r : ℚ) ^ 2 / m
    | _ => (rowNumerator r (sourceWidth r) + r) / m
  have hf (i : Fin 5) : |factor i - 1| ≤ error i := by
    fin_cases i
    · simpa only [factor, error] using guard_error r m hr hm
    · simpa only [factor, error] using floor_error r m hr hm
    · exact ht
    · simpa only [factor, error] using background_error r m hr hm exponent he
    · exact hlast
  have htotal : (∑ i : Fin 5, error i) + (sourceWidth r : ℚ) ^ 2 / m =
      CountErrorBudget.numerator r (sourceWidth r) / m := by
    norm_num [error, Fin.sum_univ_succ, CountErrorBudget.numerator,
      deletionNumerator, rowNumerator]
    <;> ring
  have hprod : (∏ i : Fin 5, factor i) =
      guardFactor r m * floorFactor r m * retention *
        backgroundFactor r m ^ exponent * last := by
    norm_num [factor, Fin.prod_univ_succ]
    <;> ring
  have hsize := ConstructionSize.threshold_conditions r m hr hm
  have h := CountErrorBudget.source_ratio_error Finset.univ factor error
    (insertionFactor r m) ((sourceWidth r : ℚ) ^ 2 / m)
    r (sourceWidth r) m (by omega) (ConstructionSize.width_positive r hr)
    hsize.1 hm (fun i _ => (abs_nonneg _).trans (hf i))
    (fun i _ => hf i) (by positivity) (insertion_error r m hr hm)
    (le_of_eq htotal)
  rwa [hprod] at h

theorem row_error (r m : Nat) (hr : 6 ≤ r)
    (hm : 4 * errorNumerator r (sourceWidth r) ≤ m) (retention u : ℚ)
    (ht : |retention - 1| ≤ deletionNumerator r (sourceWidth r) / m)
    (hu : |u| ≤ rowNumerator r (sourceWidth r) / m) :
    |guardFactor r m * floorFactor r m * retention *
        backgroundFactor r m ^ (r - 3 + 2) * (1 + u) / insertionFactor r m - 1| ≤
      (errorNumerator r (sourceWidth r) : ℚ) / m := by
  apply combined_error r m (r - 3 + 2) hr hm (by omega) retention (1 + u) ht
  have hnonneg : (0 : ℚ) ≤ (r : ℚ) / m := by positivity
  have hsum : (rowNumerator r (sourceWidth r) + r) / m =
      rowNumerator r (sourceWidth r) / m + (r : ℚ) / m := add_div _ _ _
  rw [show (1 + u) - 1 = u by ring, hsum]
  linarith

theorem charge_error (r m : Nat) (hr : 6 ≤ r)
    (hm : 4 * errorNumerator r (sourceWidth r) ≤ m) (retention v : ℚ)
    (ht : |retention - 1| ≤ deletionNumerator r (sourceWidth r) / m)
    (hv : |v| ≤ (r : ℚ) / m) :
    |guardFactor r m * floorFactor r m * retention *
        backgroundFactor r m ^ (r - 3 + 1) * (1 + v) / insertionFactor r m - 1| ≤
      (errorNumerator r (sourceWidth r) : ℚ) / m := by
  apply combined_error r m (r - 3 + 1) hr hm (by omega) retention (1 + v) ht
  have hnonneg : 0 ≤ rowNumerator r (sourceWidth r) / m := by
    unfold rowNumerator
    positivity
  have hsum : (rowNumerator r (sourceWidth r) + r) / m =
      rowNumerator r (sourceWidth r) / m + (r : ℚ) / m := add_div _ _ _
  rw [show (1 + v) - 1 = v by ring, hsum]
  linarith

end CoefficientTwoPrecision.SourceCountErrors

#print axioms CoefficientTwoPrecision.SourceCountErrors.row_error
#print axioms CoefficientTwoPrecision.SourceCountErrors.charge_error
