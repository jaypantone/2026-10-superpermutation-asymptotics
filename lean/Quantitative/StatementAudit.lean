import Quantitative.MainTheorems

/-!
# Elaborated final statements and their original definitions

The explicit @ checks expose every argument of the final declarations.
In particular the asymptotic theorem has no supplier or finite-bound
premise. The definition prints identify the original coverage predicate,
minimum length and natural/rational three-factorial functions.
-/

#check @CoefficientTwoPrecision.SparseFamilyConstruction.supplier
#check @CoefficientTwoPrecision.finite_covering_word
#check @CoefficientTwoPrecision.original_finite_bound
#check @CoefficientTwoPrecision.shortest_length_error
#check @CoefficientTwoPrecision.shortest_length_asymptotic
#print SuperpermutationBounds.Covers
#print SuperpermutationUpperBound.F3
#print SuperpermutationBounds.F3
#print ConstAsym.L
#print CoefficientTwoPrecision.transferConstant
#print axioms CoefficientTwoPrecision.finite_covering_word
#print axioms CoefficientTwoPrecision.shortest_length_asymptotic
