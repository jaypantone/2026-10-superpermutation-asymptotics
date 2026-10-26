import Quantitative.RationalProducts

/-!
# Combining the relative errors in the source-family count

Each multiplicative factor may lie on either side of one. A bound for the
sum of its absolute deviations controls their product, and one further
deviation controls division by the normalized insertion denominator.
-/

namespace CoefficientTwoPrecision.RelativeProducts

variable {ι : Type} [DecidableEq ι]

theorem product_bounds (S : Finset ι) (factor error : ι → ℚ)
    (he : ∀ i ∈ S, 0 ≤ error i)
    (hf : ∀ i ∈ S, |factor i - 1| ≤ error i)
    (hs : (∑ i ∈ S, error i) ≤ 1 / 2) :
    1 - (∑ i ∈ S, error i) ≤ (∏ i ∈ S, factor i) ∧
      (∏ i ∈ S, factor i) ≤ 1 + 2 * (∑ i ∈ S, error i) := by
  have heone (i : ι) (hi : i ∈ S) : error i ≤ 1 := by
    have hiSum := Finset.single_le_sum he hi
    linarith
  have hfactor (i : ι) (hi : i ∈ S) : 1 - error i ≤ factor i ∧ factor i ≤ 1 + error i := by
    have h := abs_le.mp (hf i hi)
    constructor <;> linarith
  have hnonneg (i : ι) (hi : i ∈ S) : 0 ≤ factor i := by
    have := hfactor i hi
    have := heone i hi
    linarith
  constructor
  · exact (RationalProducts.falling_lower S error (fun i hi => ⟨he i hi, heone i hi⟩)).trans
      (Finset.prod_le_prod₀ (fun i hi => sub_nonneg.mpr (heone i hi))
        (fun i hi => (hfactor i hi).1))
  · exact (Finset.prod_le_prod₀ hnonneg (fun i hi => (hfactor i hi).2)).trans
      (RationalProducts.rising_bounds S error he hs).2

theorem ratio_error (S : Finset ι) (factor error : ι → ℚ) (denominator denError : ℚ)
    (he : ∀ i ∈ S, 0 ≤ error i)
    (hf : ∀ i ∈ S, |factor i - 1| ≤ error i)
    (hdenError : 0 ≤ denError) (hden : |denominator - 1| ≤ denError)
    (hbudget : (∑ i ∈ S, error i) + denError ≤ 1 / 4) :
    |(∏ i ∈ S, factor i) / denominator - 1| ≤
      4 * ((∑ i ∈ S, error i) + denError) := by
  let total := (∑ i ∈ S, error i) + denError
  have hsum : 0 ≤ ∑ i ∈ S, error i := Finset.sum_nonneg he
  have hdenBounds := abs_le.mp hden
  have hdenPos : 0 < denominator := by linarith
  have hprod := product_bounds S factor error he hf (by linarith)
  have htotal : 0 ≤ total := add_nonneg hsum hdenError
  have htotalQuarter : total ≤ 1 / 4 := hbudget
  have hlowerFactor : 0 ≤ 1 - 4 * total := by linarith
  have hlowerDen := mul_le_mul_of_nonneg_left
    (show denominator ≤ 1 + denError by linarith) hlowerFactor
  have hlower : (1 - 4 * total) * denominator ≤ ∏ i ∈ S, factor i := by
    have hnonneg := mul_nonneg htotal hdenError
    dsimp only [total] at hlowerDen hnonneg ⊢
    nlinarith [hprod.1]
  have hupperDen := mul_le_mul_of_nonneg_left
    (show 1 - denError ≤ denominator by linarith)
    (show 0 ≤ 1 + 4 * total by linarith)
  have hcross := mul_le_mul_of_nonneg_right
    (show 4 * total ≤ 1 by linarith) hdenError
  have hupper : (∏ i ∈ S, factor i) ≤ (1 + 4 * total) * denominator := by
    dsimp only [total] at hupperDen hcross ⊢
    nlinarith [hprod.2]
  have hquotLower := (le_div_iff₀ hdenPos).mpr hlower
  have hquotUpper := (div_le_iff₀ hdenPos).mpr hupper
  apply abs_le.mpr
  constructor <;> change _ ≤ _ <;> linarith

end CoefficientTwoPrecision.RelativeProducts

#print axioms CoefficientTwoPrecision.RelativeProducts.ratio_error
