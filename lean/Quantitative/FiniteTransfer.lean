import Quantitative.RationalTransfer
import Quantitative.WordBounds

/-!
# The finite rational coefficient bound

The sparse source estimates imply a local cost bound. Together with the
exact recurrence invariants, a bound for the dense tail, and a bound for
joining, this gives coefficient `2 + 74/r`.

All source estimates, density constraints, and completion statements are
explicit hypotheses. This file does not construct a source family, a Stage,
or a covering word. The final theorem bounds a word already supplied in
its hypotheses and preserves the original `Covers` predicate.
-/

namespace CoefficientTwoPrecision

/-- The cancellation from the rational starting fraction, with room for
the relative errors in the source counts. -/
theorem sparse_leading_coefficient_bound (r : ℚ) (hr : 6 ≤ r) :
    2 * r / (r - 2) ≤ 2 + 6 / r := by
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r - 2 := by linarith
  have hs : 6 / r ≤ 1 := (div_le_iff₀ hr0).2 (by linarith)
  have heq : (2 + 6 / r) * (r - 2) - 2 * r = 2 * (1 - 6 / r) := by
    field_simp [ne_of_gt hr0] <;> ring
  apply (div_le_iff₀ hr2).2
  nlinarith only [hs, heq]

theorem sparse_coefficient_product_bound (r : ℚ) (hr : 6 ≤ r) :
    (2 + 6 / r) * (1 + 1 / r) ≤ 2 + 9 / r := by
  have hr0 : 0 < r := by linarith
  have ht : 0 ≤ 1 / r := div_nonneg (by norm_num) (le_of_lt hr0)
  have hs : 6 / r ≤ 1 := (div_le_iff₀ hr0).2 (by linarith)
  have hprod : 0 ≤ (1 / r) * (1 - 6 / r) := mul_nonneg ht (sub_nonneg.mpr hs)
  have heq : (2 + 6 / r) * (1 + 1 / r) - (2 + 9 / r) =
      -(1 / r) * (1 - 6 / r) := by ring
  nlinarith only [hprod, heq]

/-- The error factors are compared without dividing by `1 + theta`. -/
theorem sparse_error_factor_bound (r theta epsilon : ℚ) (hr : 6 ≤ r)
    (htheta : -(1 / (4 * r)) ≤ theta) (hepsilon : epsilon ≤ 1 / (4 * r)) :
    0 ≤ 1 + theta ∧ 1 + epsilon ≤ (1 + 1 / r) * (1 + theta) := by
  have hr0 : 0 < r := by linarith
  have ht0 : 0 ≤ 1 / r := div_nonneg (by norm_num) (le_of_lt hr0)
  have ht1 : 1 / r ≤ 1 := (div_le_iff₀ hr0).2 (by linarith)
  have hdelta : 1 / (4 * r) = (1 / r) / 4 := by
    field_simp [ne_of_gt hr0] <;> ring
  rw [hdelta] at htheta hepsilon
  have hfactor : 0 ≤ 1 + 1 / r := by linarith
  have hmul := mul_le_mul_of_nonneg_left htheta hfactor
  have hsquare : 0 ≤ (1 / r) * (1 - 1 / r) :=
    mul_nonneg ht0 (sub_nonneg.mpr ht1)
  constructor
  · linarith only [htheta, ht1]
  · nlinarith only [hmul, hepsilon, ht0, hsquare]

/-- The actual sparse count formulas yield the local bound used by the
telescoping invariant. `lambda` may be instantiated with `rho * W`. -/
theorem sparse_local_cost_bound (n m r lambda theta epsilon f g : ℚ)
    (hr : 6 ≤ r) (hn : 0 < n)
    (hm : ((r - 1) / r) * n ≤ m) (hlambda : 0 ≤ lambda)
    (htheta : |theta| ≤ 1 / (4 * r))
    (hepsilon : |epsilon| ≤ 1 / (4 * r))
    (hf : f = (lambda / m) * (1 + theta))
    (hg : g = ((2 * (r - 1) / (r - 2)) * lambda / m ^ 2) * (1 + epsilon)) :
    n * g ≤ (2 + 9 / r) * f := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hr2 : 0 < r - 2 := by linarith
  have hmMul : (r - 1) * n ≤ m * r := by
    apply (div_le_iff₀ hr0).1
    simpa only [div_mul_eq_mul_div] using hm
  have hm0 : 0 < m :=
    (mul_pos_iff_of_pos_right hr0).1 ((mul_pos hr1 hn).trans_le hmMul)
  have hstart := mul_le_mul_of_nonneg_left hmMul
    (div_nonneg (by norm_num : (0 : ℚ) ≤ 2) (le_of_lt hr2))
  have hstart' : (2 * (r - 1) / (r - 2)) * n ≤
      (2 * r / (r - 2)) * m := by
    calc
      (2 * (r - 1) / (r - 2)) * n = (2 / (r - 2)) * ((r - 1) * n) := by ring
      _ ≤ (2 / (r - 2)) * (m * r) := hstart
      _ = (2 * r / (r - 2)) * m := by ring
  have hbase : (2 * (r - 1) / (r - 2)) * n ≤ (2 + 6 / r) * m :=
    hstart'.trans (mul_le_mul_of_nonneg_right
      (sparse_leading_coefficient_bound r hr) (le_of_lt hm0))
  obtain ⟨hth0, hphase⟩ := sparse_error_factor_bound r theta epsilon hr
    (abs_le.mp htheta).1 (abs_le.mp hepsilon).2
  have hb0 : 0 ≤ 1 + 1 / r := by
    have : 0 ≤ (1 : ℚ) / r := div_nonneg (by norm_num) (le_of_lt hr0)
    linarith
  let t : ℚ := lambda / m ^ 2
  have ht : 0 ≤ t := div_nonneg hlambda (sq_nonneg m)
  have hc0 : 0 ≤ (2 * (r - 1) / (r - 2)) * n :=
    mul_nonneg (div_nonneg (by nlinarith only [hr1]) (le_of_lt hr2)) (le_of_lt hn)
  rw [hf, hg]
  calc
    n * (((2 * (r - 1) / (r - 2)) * lambda / m ^ 2) * (1 + epsilon))
        = ((2 * (r - 1) / (r - 2)) * n) * t * (1 + epsilon) := by
      dsimp [t]
      ring
    _ ≤ ((2 * (r - 1) / (r - 2)) * n) * t *
        ((1 + 1 / r) * (1 + theta)) :=
      mul_le_mul_of_nonneg_left hphase (mul_nonneg hc0 ht)
    _ = ((2 * (r - 1) / (r - 2)) * n) *
        ((1 + 1 / r) * (1 + theta)) * t := by ring
    _ ≤ ((2 + 6 / r) * m) * ((1 + 1 / r) * (1 + theta)) * t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbase (mul_nonneg hb0 hth0)) ht
    _ = ((2 + 6 / r) * (1 + 1 / r)) * (lambda / m) * (1 + theta) := by
      dsimp [t]
      field_simp [ne_of_gt hm0, ne_of_gt hr0] <;> ring
    _ ≤ (2 + 9 / r) * ((lambda / m) * (1 + theta)) := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (sparse_coefficient_product_bound r hr)
          (div_nonneg hlambda (le_of_lt hm0))) hth0
      simpa only [mul_assoc] using h

/-- The sparse recurrence, the dense-tail bound, and the joining allowance
give the advertised coefficient. Both final costs are already normalized
by the fourth factorial scale. -/
theorem finite_transfer_coefficient (f g : ℕ → ℚ) (J : ℕ)
    (n r dense joining : ℚ) (hr : 0 < r)
    (hf : ∀ i < J, 0 ≤ f i ∧ f i ≤ 1)
    (hsum : r / 4 ≤ densitySum f J)
    (hcost : ∀ i < J, n * g i ≤ (2 + 9 / r) * f i)
    (hdense : dense ≤ 16 * pending f J) (hjoining : joining ≤ 1 / r) :
    n * accumulatedCost f g J + dense + joining ≤ 2 + 74 / r := by
  have hp := pending_nonneg f J (fun i hi => (hf i hi).2)
  have hps := pending_le_four_div f J r hr hf hsum
  have hK : 0 ≤ 2 + 9 / r := by
    have : 0 ≤ (9 : ℚ) / r := div_nonneg (by norm_num) (le_of_lt hr)
    linarith
  have hI := cost_invariant f g J n (2 + 9 / r)
    (fun i hi => (hf i hi).2) hcost
  have hnonneg : 0 ≤ (2 + 9 / r) * pending f J := mul_nonneg hK hp
  have hsparse : n * accumulatedCost f g J ≤ 2 + 9 / r := by
    linarith only [hI, hnonneg]
  have hmult := mul_le_mul_of_nonneg_left hps (by norm_num : (0 : ℚ) ≤ 16)
  have htail : dense ≤ 64 / r := by
    calc
      dense ≤ 16 * pending f J := hdense
      _ ≤ 16 * (4 / r) := hmult
      _ = 64 / r := by ring
  have heq : (2 + 9 / r) + 64 / r + 1 / r = 2 + 74 / r := by ring
  linarith only [hsparse, htail, hjoining, heq]

/-- A numerical completion bound for an already supplied covering word
implies the requested integer inequality. This theorem does not supply the
word or prove the numerical completion premise from geometric objects. -/
theorem word_bound_of_normalized_completion (n r : ℕ) (hr : 6 ≤ r)
    (w : List (Fin n)) (hw : SuperpermutationBounds.Covers w)
    (f g : ℕ → ℚ) (J : ℕ) (dense joining : ℚ)
    (hf : ∀ i < J, 0 ≤ f i ∧ f i ≤ 1)
    (hsum : (r : ℚ) / 4 ≤ densitySum f J)
    (hcost : ∀ i < J, (n : ℚ) * g i ≤ (2 + 9 / (r : ℚ)) * f i)
    (hdense : dense ≤ 16 * pending f J) (hjoining : joining ≤ 1 / (r : ℚ))
    (hcompletion : ((w.length : ℚ) - SuperpermutationBounds.F3 n) /
      ((n - 4).factorial : ℚ) ≤ (n : ℚ) * accumulatedCost f g J + dense + joining) :
    SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * SuperpermutationUpperBound.F3 n +
        (2 * r + 74) * (n - 4).factorial := by
  have hrNat : 0 < r := by omega
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hrNat
  have hcoef := finite_transfer_coefficient f g J (n : ℚ) (r : ℚ)
    dense joining hrQ hf hsum hcost hdense hjoining
  have hfac : (0 : ℚ) < ((n - 4).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos (n - 4)
  have hnormalized := hcompletion.trans hcoef
  have hmul := (div_le_iff₀ hfac).1 hnormalized
  have hlength : (w.length : ℚ) ≤ SuperpermutationBounds.F3 n +
      (2 + 74 / (r : ℚ)) * ((n - 4).factorial : ℚ) := by
    linarith only [hmul]
  exact ⟨hw, (integer_bound_iff n r hrNat w).2 hlength⟩

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.sparse_local_cost_bound
#print axioms CoefficientTwoPrecision.finite_transfer_coefficient
#print axioms CoefficientTwoPrecision.word_bound_of_normalized_completion
