-- Superpermutation Almanac batch: the coefficient of (n-4)! and its polynomial error.
import AlmanacDefs
import AlmanacAdapter

/-! The released theorem gives `S(n) = n! + (n-1)! + (n-2)! + 2(n-4)! + O((n-4)! n^(-1/61))`.
With the listed lower bound `AsymptoticLowerAt 4 2`, the first statement makes the
coefficient of `(n-4)!` exactly 2. The second states the explicit error bound. -/
namespace AlmanacSubmission

/-- For every ε > 0 and all large n, S(n) ≤ n! + (n-1)! + (n-2)! + (2 + ε)(n-4)!. -/
theorem asymptotic_upper_four : Almanac.AsymptoticUpperAt 4 2 :=
  AlmanacAdapter.asymptotic_upper_four

/-- For every n ≥ 8·10¹²·352⁴·6⁶¹,
|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 400 (n-4)! n^(-1/61). -/
theorem explicit_error : AlmanacAdapter.ExplicitError := AlmanacAdapter.explicit_error

end AlmanacSubmission
