import Quantitative.FiniteParameters
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The explicit parameters of the source construction

The factorial quotient, rational density, natural ceiling, width, and
normalized density are defined here. Their polynomial bounds are proved
from the definitions. No source-family existence hypothesis occurs in
these arithmetic statements.
-/

namespace CoefficientTwoPrecision

def sourceDegree (r : ℕ) : ℕ := 64 * r ^ 8

def sourceEta (r : ℕ) : ℚ :=
  (r.factorial : ℚ) /
    (2 * ((r - 3).factorial : ℚ) * ((sourceDegree r : ℚ) + 1))

def sourceBeta (r : ℕ) : ℚ := ((r : ℚ) - 2) * sourceEta r

def sourceA (r : ℕ) : ℕ := ⌈(r : ℚ) ^ 3 / sourceBeta r⌉₊

def sourceWidth (r : ℕ) : ℕ := r ^ 2 * sourceA r

def sourceRho (r : ℕ) : ℚ := (sourceA r : ℚ) * sourceBeta r / (r : ℚ)

def sourceGridCount (r : ℕ) : ℕ := r * sourceA r ^ 2

def betaPolynomial (x : ℚ) : ℚ :=
  x * (x - 1) * (x - 2) ^ 2 / (2 * (64 * x ^ 8 + 1))

theorem sourceEta_closed_form (r : ℕ) (hr : 3 ≤ r) :
    sourceEta r =
      (r : ℚ) * ((r : ℚ) - 1) * ((r : ℚ) - 2) /
        (2 * (64 * (r : ℚ) ^ 8 + 1)) := by
  have hfac : (r.factorial : ℚ) =
      (r : ℚ) * ((r : ℚ) - 1) * ((r : ℚ) - 2) * ((r - 3).factorial : ℚ) := by
    obtain ⟨s, hs⟩ : ∃ s : ℕ, r = s + 3 := ⟨r - 3, by omega⟩
    subst r
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_ofNat]
    ring
  have hfac0 : ((r - 3).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r - 3)
  have hden : (64 : ℚ) * (r : ℚ) ^ 8 + 1 ≠ 0 := by positivity
  unfold sourceEta sourceDegree
  push_cast
  rw [hfac]
  field_simp [hfac0, hden] <;> ring

theorem sourceBeta_closed_form (r : ℕ) (hr : 3 ≤ r) :
    sourceBeta r = betaPolynomial (r : ℚ) := by
  unfold sourceBeta
  rw [sourceEta_closed_form r hr]
  unfold betaPolynomial
  ring

/-- A lower bound sharp enough to give the stated constant 352 in the
width estimate, together with the positivity needed for the ceiling. -/
theorem betaPolynomial_bounds (x : ℚ) (hx : 6 ≤ x) :
    0 < betaPolynomial x ∧ betaPolynomial x < 1 ∧
      1 / (351 * x ^ 4) ≤ betaPolynomial x := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℚ) ≤ x := by linarith
  have hxsub1 : 0 < x - 1 := by linarith
  have hxsub2 : 0 < x - 2 := by linarith
  let N : ℚ := x * (x - 1) * (x - 2) ^ 2
  let D : ℚ := 2 * (64 * x ^ 8 + 1)
  have hNpos : 0 < N := mul_pos (mul_pos hx0 hxsub1) (pow_pos hxsub2 2)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have h1 : (5 / 6 : ℚ) * x ≤ x - 1 := by linarith
  have h2 : (2 / 3 : ℚ) * x ≤ x - 2 := by linarith
  have h2sq : ((2 / 3 : ℚ) * x) ^ 2 ≤ (x - 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  have hprodLower := mul_le_mul_of_nonneg_left
    (mul_le_mul h1 h2sq (sq_nonneg _) (le_of_lt hxsub1)) (le_of_lt hx0)
  have hNlower : (10 / 27 : ℚ) * x ^ 4 ≤ N := by
    calc
      (10 / 27 : ℚ) * x ^ 4 =
          x * (((5 / 6 : ℚ) * x) * (((2 / 3 : ℚ) * x) ^ 2)) := by ring
      _ ≤ x * ((x - 1) * (x - 2) ^ 2) := hprodLower
      _ = N := by dsimp [N]; ring
  have h2upper : (x - 2) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hxsub2) (by linarith) 2
  have hprodUpper := mul_le_mul_of_nonneg_left
    (mul_le_mul (show x - 1 ≤ x by linarith) h2upper (sq_nonneg _) (le_of_lt hx0))
    (le_of_lt hx0)
  have hNupper : N ≤ x ^ 4 := by
    calc
      N = x * ((x - 1) * (x - 2) ^ 2) := by dsimp [N]; ring
      _ ≤ x * (x * x ^ 2) := hprodUpper
      _ = x ^ 4 := by ring
  have h8 : (1 : ℚ) ≤ x ^ 8 := one_le_pow₀ hx1
  have h48 : x ^ 4 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by decide : 4 ≤ 8)
  have hDupper : D ≤ 130 * x ^ 8 := by dsimp [D]; linarith only [h8]
  have hNltD : N < D := hNupper.trans_lt (h48.trans_lt (by dsimp [D]; linarith only [h8]))
  change 0 < N / D ∧ N / D < 1 ∧ 1 / (351 * x ^ 4) ≤ N / D
  refine ⟨div_pos hNpos hDpos, ?_, ?_⟩
  · apply (div_lt_iff₀ hDpos).2
    simpa only [one_mul] using hNltD
  · apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 351 * x ^ 4) hDpos).2
    calc
      1 * D = D := by ring
      _ ≤ 130 * x ^ 8 := hDupper
      _ = ((10 / 27 : ℚ) * x ^ 4) * (351 * x ^ 4) := by ring
      _ ≤ N * (351 * x ^ 4) := mul_le_mul_of_nonneg_right hNlower (by positivity)

theorem sourceBeta_bounds (r : ℕ) (hr : 6 ≤ r) :
    0 < sourceBeta r ∧ sourceBeta r < 1 ∧
      1 / (351 * (r : ℚ) ^ 4) ≤ sourceBeta r := by
  simp only [sourceBeta_closed_form r (by omega)]
  exact betaPolynomial_bounds (r : ℚ) (by exact_mod_cast hr)

theorem sourceA_pos (r : ℕ) (hr : 6 ≤ r) : 0 < sourceA r := by
  have hr0 : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  exact Nat.ceil_pos.mpr (div_pos (pow_pos hr0 3) (sourceBeta_bounds r hr).1)

theorem sourceWidth_lower (r : ℕ) (hr : 6 ≤ r) : r ^ 2 ≤ sourceWidth r := by
  have hA : 1 ≤ sourceA r := sourceA_pos r hr
  simpa only [Nat.mul_one, sourceWidth] using Nat.mul_le_mul_left (r ^ 2) hA

theorem sourceWidth_dvd (r : ℕ) : r ∣ sourceWidth r := by
  refine ⟨r * sourceA r, ?_⟩
  unfold sourceWidth
  ring

theorem sourceWidth_upper (r : ℕ) (hr : 6 ≤ r) : sourceWidth r ≤ 352 * r ^ 9 := by
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℚ) < r := by linarith
  obtain ⟨hbeta, _, hbetalower⟩ := sourceBeta_bounds r hr
  have hquot : (r : ℚ) ^ 3 / sourceBeta r ≤ 351 * (r : ℚ) ^ 7 := by
    calc
      (r : ℚ) ^ 3 / sourceBeta r ≤ (r : ℚ) ^ 3 / (1 / (351 * (r : ℚ) ^ 4)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hbetalower
      _ = 351 * (r : ℚ) ^ 7 := by field_simp [ne_of_gt hr0] <;> ring
  have hceil : (sourceA r : ℚ) < (r : ℚ) ^ 3 / sourceBeta r + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (div_pos (pow_pos hr0 3) hbeta))
  have hA : (sourceA r : ℚ) < 351 * (r : ℚ) ^ 7 + 1 :=
    hceil.trans_le (add_le_add hquot (le_refl 1))
  have hwidth : (sourceWidth r : ℚ) < 351 * (r : ℚ) ^ 9 + (r : ℚ) ^ 2 := by
    calc
      (sourceWidth r : ℚ) = (r : ℚ) ^ 2 * (sourceA r : ℚ) := by
        simp only [sourceWidth, Nat.cast_mul, Nat.cast_pow]
      _ < (r : ℚ) ^ 2 * (351 * (r : ℚ) ^ 7 + 1) :=
        mul_lt_mul_of_pos_left hA (pow_pos hr0 2)
      _ = 351 * (r : ℚ) ^ 9 + (r : ℚ) ^ 2 := by ring
  have h29 : (r : ℚ) ^ 2 ≤ (r : ℚ) ^ 9 :=
    pow_le_pow_right₀ (by linarith : (1 : ℚ) ≤ r) (by decide : 2 ≤ 9)
  have hwidthQ : (sourceWidth r : ℚ) ≤ 352 * (r : ℚ) ^ 9 := by
    linarith only [hwidth, h29]
  exact_mod_cast hwidthQ

theorem sourceRho_bounds (r : ℕ) (hr : 6 ≤ r) :
    (r : ℚ) ^ 2 ≤ sourceRho r ∧ sourceRho r < (r : ℚ) ^ 2 + 1 := by
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℚ) < r := by linarith
  obtain ⟨hbeta, hbeta1, _⟩ := sourceBeta_bounds r hr
  have hceil : (r : ℚ) ^ 3 / sourceBeta r ≤ (sourceA r : ℚ) :=
    Nat.le_ceil _
  have hceilUpper : (sourceA r : ℚ) < (r : ℚ) ^ 3 / sourceBeta r + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (div_pos (pow_pos hr0 3) hbeta))
  have hABlower : (r : ℚ) ^ 3 ≤ (sourceA r : ℚ) * sourceBeta r :=
    (div_le_iff₀ hbeta).1 hceil
  have hABupper : (sourceA r : ℚ) * sourceBeta r < (r : ℚ) ^ 3 + sourceBeta r := by
    calc
      (sourceA r : ℚ) * sourceBeta r <
          ((r : ℚ) ^ 3 / sourceBeta r + 1) * sourceBeta r :=
        mul_lt_mul_of_pos_right hceilUpper hbeta
      _ = (r : ℚ) ^ 3 + sourceBeta r := by field_simp [ne_of_gt hbeta] <;> ring
  unfold sourceRho
  constructor
  · apply (le_div_iff₀ hr0).2
    calc
      (r : ℚ) ^ 2 * (r : ℚ) = (r : ℚ) ^ 3 := by ring
      _ ≤ (sourceA r : ℚ) * sourceBeta r := hABlower
  · apply (div_lt_iff₀ hr0).2
    calc
      (sourceA r : ℚ) * sourceBeta r < (r : ℚ) ^ 3 + sourceBeta r := hABupper
      _ ≤ (r : ℚ) ^ 3 + (r : ℚ) := by linarith only [hbeta1, hrQ]
      _ = ((r : ℚ) ^ 2 + 1) * (r : ℚ) := by ring

/-- The geometric leading count and the recurrence density use the same
coefficient, as an exact rational identity. -/
theorem source_coefficient_identity (r : ℕ) (hr : 0 < r) :
    (sourceGridCount r : ℚ) * sourceBeta r = sourceRho r * (sourceWidth r : ℚ) := by
  have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  simp only [sourceGridCount, sourceRho, sourceWidth, Nat.cast_mul, Nat.cast_pow]
  field_simp [hrQ] <;> ring

/-- Instantiation of the finite size theorem with the actual ceiling-defined
width. The geometric source-family existence remains a separate theorem. -/
theorem construction_threshold_conditions (r n : ℕ) (hr : 6 ≤ r)
    (hn : transferConstant * r ^ 61 ≤ n) :
    8 * r * errorNumerator r (sourceWidth r) ≤ n ∧
      96 * r ^ 2 ≤ n ∧
      2 * r * (r + sourceWidth r + (3 + 36 * binaryLength n)) ≤ n := by
  exact polynomial_threshold_conditions r (sourceWidth r) n hr
    (sourceWidth_lower r hr) (sourceWidth_upper r hr) hn

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.sourceEta_closed_form
#print axioms CoefficientTwoPrecision.sourceWidth_upper
#print axioms CoefficientTwoPrecision.sourceRho_bounds
#print axioms CoefficientTwoPrecision.construction_threshold_conditions
