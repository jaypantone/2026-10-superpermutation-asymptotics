import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Elementary finite product estimates for the source counts

The estimates use only rational arithmetic. A sum of small nonnegative
errors bounds a falling product from below and a rising product from above.
They apply to distinct guard cuts, the insertion denominator, and powers
arising from the difference between the two background sizes.
-/

namespace CoefficientTwoPrecision.RationalProducts

variable {ι : Type} [DecidableEq ι]

theorem falling_lower (S : Finset ι) (u : ι → ℚ)
    (hu : ∀ i ∈ S, 0 ≤ u i ∧ u i ≤ 1) :
    1 - ∑ i ∈ S, u i ≤ ∏ i ∈ S, (1 - u i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have ha' := hu a (Finset.mem_insert_self _ _)
    have htail := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
    have hsum : 0 ≤ ∑ i ∈ S, u i := Finset.sum_nonneg
      (fun i hi => (hu i (Finset.mem_insert_of_mem hi)).1)
    have hmul := mul_le_mul_of_nonneg_left htail (sub_nonneg.mpr ha'.2)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith [mul_nonneg ha'.1 hsum]

theorem falling_bounds (S : Finset ι) (u : ι → ℚ)
    (hu : ∀ i ∈ S, 0 ≤ u i ∧ u i ≤ 1) :
    1 - ∑ i ∈ S, u i ≤ ∏ i ∈ S, (1 - u i) ∧
      (∏ i ∈ S, (1 - u i)) ≤ 1 := by
  refine ⟨falling_lower S u hu, ?_⟩
  calc
    ∏ i ∈ S, (1 - u i) ≤ ∏ _i ∈ S, (1 : ℚ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact sub_nonneg.mpr (hu i hi).2
      · intro i hi
        linarith [(hu i hi).1]
    _ = 1 := by simp

theorem rising_invariant (S : Finset ι) (u : ι → ℚ)
    (hu : ∀ i ∈ S, 0 ≤ u i) (hsum : (∑ i ∈ S, u i) ≤ 1) :
    (∏ i ∈ S, (1 + u i)) * (1 - ∑ i ∈ S, u i) ≤ 1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have ha' := hu a (Finset.mem_insert_self _ _)
    have htailNonneg : ∀ i ∈ S, 0 ≤ u i := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hsumNonneg : 0 ≤ ∑ i ∈ S, u i := Finset.sum_nonneg htailNonneg
    rw [Finset.sum_insert ha] at hsum
    have htail := ih htailNonneg (by linarith)
    have hproductNonneg : 0 ≤ ∏ i ∈ S, (1 + u i) :=
      Finset.prod_nonneg (fun i hi => by linarith [htailNonneg i hi])
    have hfactor : (1 + u a) * (1 - (u a + ∑ i ∈ S, u i)) ≤ 1 - ∑ i ∈ S, u i := by
      nlinarith [mul_nonneg ha' hsumNonneg]
    have hmul := mul_le_mul_of_nonneg_left hfactor hproductNonneg
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    nlinarith [hmul]

theorem rising_bounds (S : Finset ι) (u : ι → ℚ)
    (hu : ∀ i ∈ S, 0 ≤ u i) (hsum : (∑ i ∈ S, u i) ≤ 1 / 2) :
    1 ≤ (∏ i ∈ S, (1 + u i)) ∧
      (∏ i ∈ S, (1 + u i)) ≤ 1 + 2 * ∑ i ∈ S, u i := by
  have hlower : 1 ≤ ∏ i ∈ S, (1 + u i) := Finset.one_le_prod₀
    (fun i hi => by linarith [hu i hi])
  have hinv := rising_invariant S u hu (by linarith)
  have hsumNonneg : 0 ≤ ∑ i ∈ S, u i := Finset.sum_nonneg hu
  have hprodNonneg : 0 ≤ ∏ i ∈ S, (1 + u i) := le_trans (by norm_num) hlower
  have hprodTwo : (∏ i ∈ S, (1 + u i)) ≤ 2 := by
    nlinarith [mul_nonneg hprodNonneg (sub_nonneg.mpr hsum)]
  refine ⟨hlower, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hprodTwo) hsumNonneg]

end CoefficientTwoPrecision.RationalProducts

#print axioms CoefficientTwoPrecision.RationalProducts.falling_bounds
#print axioms CoefficientTwoPrecision.RationalProducts.rising_bounds
