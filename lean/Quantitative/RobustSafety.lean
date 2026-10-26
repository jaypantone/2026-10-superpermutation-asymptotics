import Quantitative.RobustMatching

/-!
# Every binary-phase cut vector has empty successor cuts

These are the geometric safety inequalities needed by the positive-update
renderer. The same binary phase function is used at every stationary slot.
No requirement on the order or number of previous batches is hidden in the
statement; the exact prefix-count formulas must supply that phase function.
-/

namespace CoefficientTwoPrecision.RobustSafety

open RobustMatching

variable {M : Nat} {Slot : Type} [DecidableEq Slot]

def perturbed (q : Slot → ZMod M) (translation : ZMod M) (phases : Slot → Bool) :
    Slot → ZMod M := fun i => q i + translation + (bit (phases i) : ZMod M)

theorem index_zero_implies_diagonal (i j : Slot) (h : pairIndex i j = none) : i = j := by
  by_contra hne
  simp [pairIndex, hne] at h

/-- Robustness prevents any two perturbed stationary cuts from coinciding. -/
theorem perturbed_injective (q : Slot → ZMod M) (hrobust : Robust q)
    (translation : ZMod M) (phases : Slot → Bool) :
    Function.Injective (perturbed q translation phases) := by
  intro i j hij
  let e : ℤ := bit (phases j) - bit (phases i)
  have hlo : -4 ≤ e := by
    dsimp only [e]
    cases phases i <;> cases phases j <;> norm_num [bit]
  have hhi : e ≤ 4 := by
    dsimp only [e]
    cases phases i <;> cases phases j <;> norm_num [bit]
  apply index_zero_implies_diagonal i j
  apply hrobust (pairIndex i j) none e hlo hhi
  rw [difference_pairIndex]
  simp only [difference, zero_add, e, Int.cast_sub]
  change q i + translation + (bit (phases i) : ZMod M) =
    q j + translation + (bit (phases j) : ZMod M) at hij
  linear_combination hij

/-- The successor of a perturbed stationary cut contains no stationary
resident, even across the last/first background cut. -/
theorem successor_unoccupied (hM : 2 ≤ M) (q : Slot → ZMod M) (hrobust : Robust q)
    (translation : ZMod M) (phases : Slot → Bool) (i j : Slot) :
    perturbed q translation phases i ≠ perturbed q translation phases j + 1 := by
  intro hij
  let e : ℤ := bit (phases j) - bit (phases i) + 1
  have hlo : -4 ≤ e := by
    dsimp only [e]
    cases phases i <;> cases phases j <;> norm_num [bit]
  have hhi : e ≤ 4 := by
    dsimp only [e]
    cases phases i <;> cases phases j <;> norm_num [bit]
  have heq : pairIndex i j = none := by
    apply hrobust (pairIndex i j) none e hlo hhi
    rw [difference_pairIndex]
    simp only [difference, zero_add, e, Int.cast_add, Int.cast_sub, Int.cast_one]
    change q i + translation + (bit (phases i) : ZMod M) =
      q j + translation + (bit (phases j) : ZMod M) + 1 at hij
    linear_combination hij
  have hijSlots := index_zero_implies_diagonal i j heq
  subst j
  have hone : (1 : ZMod M) = 0 := by linear_combination -hij
  have hMone := ZMod.one_eq_zero_iff.mp hone
  omega

end CoefficientTwoPrecision.RobustSafety

#print axioms CoefficientTwoPrecision.RobustSafety.perturbed_injective
#print axioms CoefficientTwoPrecision.RobustSafety.successor_unoccupied
