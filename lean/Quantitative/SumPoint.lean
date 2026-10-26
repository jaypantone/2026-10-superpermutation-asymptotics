import Quantitative.RobustMatching

/-!
# Uniqueness of the sum point

Two possible sum points in the same anchored set would have equal doubles.
Robustness excludes this even when the modulus is even: their two opposite
ordered differences would otherwise coincide.
-/

namespace CoefficientTwoPrecision.SumPoint

open RobustMatching

theorem double_injective_on_robust {M : Nat} {Slot : Type} [DecidableEq Slot]
    (q : Slot → ZMod M) (hrobust : Robust q) (i j : Slot)
    (hdouble : 2 * q i = 2 * q j) : i = j := by
  by_contra hne
  have hdiff : q i - q j = q j - q i := by linear_combination hdouble
  have hind := hrobust (pairIndex i j) (pairIndex j i) 0 (by norm_num) (by norm_num)
    (by simpa only [difference_pairIndex, Int.cast_zero, add_zero] using hdiff)
  exact hne (pairIndex_equal_diagonal i j j i hne hind).1

theorem sum_point_unique {M : Nat} {Slot : Type} [DecidableEq Slot]
    (q : Slot → ZMod M) (hrobust : Robust q) (total : ZMod M) (i j : Slot)
    (hi : total = 2 * q i) (hj : total = 2 * q j) : i = j :=
  double_injective_on_robust q hrobust i j (hi.symm.trans hj)

end CoefficientTwoPrecision.SumPoint

#print axioms CoefficientTwoPrecision.SumPoint.sum_point_unique
