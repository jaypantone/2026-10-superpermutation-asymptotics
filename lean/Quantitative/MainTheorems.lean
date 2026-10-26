import Quantitative.SparseFamilyConstruction
import Quantitative.ActualWordBound

/-!
# The quantitative superpermutation theorem

The source families are constructed in SparseFamilyConstruction. The
actual Stage iteration and word assembly therefore have no remaining
family-existence hypothesis. Covers, both versions of F3, and the minimum
length L are the original definitions supplied with the project.
-/

namespace CoefficientTwoPrecision

open Asymptotics

/-- The finite bound for an actual covering word, with the stated
absolute constant and no source-family hypothesis. -/
theorem finite_covering_word (n r : Nat) (hr : 6 ≤ r) (_hdiv : 6 ∣ r)
    (hn : (8 * 10 ^ 12 * 352 ^ 4) * r ^ 61 ≤ n) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * SuperpermutationUpperBound.F3 n +
        (2 * r + 74) * (n - 4).factorial :=
  ActualWordBound.finite_word n r hr hn (SparseFamilyConstruction.supplier r hr)

theorem original_finite_bound : OriginalWordFiniteBound61 := by
  intro r hr hdiv n hn
  exact finite_covering_word n r hr hdiv hn

/-- An explicit error estimate for the original minimum covering length.
The lower side uses the rebuilt original lower-bound theorem. -/
theorem shortest_length_error (n : Nat)
    (hn : transferConstant * 6 ^ 61 ≤ n) (hn8 : 8 ≤ n) :
    |((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
        ((n - 4).factorial : ℝ) - 2| ≤
      remainderConstant * (n : ℝ) ^ (-1 / 61 : ℝ) :=
  conditional_normalized_error_bound original_finite_bound n hn hn8

/-- The requested two-sided error term with exponent 1/61. -/
theorem shortest_length_asymptotic :
    (fun n : Nat => (ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ) -
      2 * ((n - 4).factorial : ℝ)) =O[Filter.atTop]
      (fun n : Nat => ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 61 : ℝ)) :=
  conditional_asymptotic_61 original_finite_bound

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.SparseFamilyConstruction.supplier
#print axioms CoefficientTwoPrecision.finite_covering_word
#print axioms CoefficientTwoPrecision.original_finite_bound
#print axioms CoefficientTwoPrecision.shortest_length_error
#print axioms CoefficientTwoPrecision.shortest_length_asymptotic
