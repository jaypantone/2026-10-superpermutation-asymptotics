import Quantitative.FiniteRoleExecution
import Quantitative.LabelCompletion

/-!
# The role assignments in two equal cyclic source bases

Once every shared stationary control has been proved to occupy the same
physical slot, there are only two possibilities. Equal mobiles give equal
assignments. Different mobiles give one exchange between the mobile and
a unique stationary slot. This is a consequence of actual bijectivity.
-/

namespace CoefficientTwoPrecision.FiniteRoles

variable {k : Nat} {α : Type}

theorem stationary_eq_unless_target (first second : Role k ≃ α)
    (hdiag : ∀ i j, Matches first second i j → i = j)
    (i : Fin k) (hne : first (some i) ≠ second none) :
    first (some i) = second (some i) := by
  obtain ⟨role, hrole⟩ := second.surjective (first (some i))
  cases role with
  | none => exact False.elim (hne hrole.symm)
  | some j =>
    have hij : i = j := hdiag i j hrole.symm
    simpa only [hij] using hrole.symm

theorem equal_of_diagonal_matches_of_mobile_eq (first second : Role k ≃ α)
    (hdiag : ∀ i j, Matches first second i j → i = j)
    (hmobile : first none = second none) : first = second := by
  apply Equiv.ext
  intro role
  cases role with
  | none => exact hmobile
  | some i =>
    apply stationary_eq_unless_target first second hdiag i
    intro h
    have himpossible := first.injective (h.trans hmobile.symm)
    cases himpossible

theorem exchange_of_diagonal_matches_of_mobile_ne (first second : Role k ≃ α)
    (hdiag : ∀ i j, Matches first second i j → i = j)
    (hmobile : first none ≠ second none) :
    ∃ target : Fin k, second = update target first ∧
      first (some target) = second none ∧ second (some target) = first none ∧
      (∀ i, i ≠ target → first (some i) = second (some i)) := by
  obtain ⟨role, hrole⟩ := first.surjective (second none)
  cases role with
  | none => exact False.elim (hmobile hrole)
  | some target =>
    have hother (i : Fin k) (hi : i ≠ target) :
        first (some i) = second (some i) := by
      apply stationary_eq_unless_target first second hdiag i
      intro h
      exact hi (Option.some.inj (first.injective (h.trans hrole.symm)))
    have heq : update target first = second := by
      apply LabelCompletion.equiv_eq_of_agree_except_one _ _ (some target)
      intro p hp
      cases p with
      | none => simpa only [update_mobile] using hrole
      | some i =>
        have hi : i ≠ target := by simpa only [ne_eq, Option.some.injEq] using hp
        rw [update_other target i first hi]
        exact hother i hi
    refine ⟨target, heq.symm, hrole, ?_, hother⟩
    rw [← heq, update_target]

theorem exchange_target_unique (first second : Role k ≃ α) (i j : Fin k)
    (hi : second = update i first) (hj : second = update j first) : i = j := by
  have hm := congrArg (fun e : Role k ≃ α => e none) (hi.symm.trans hj)
  simp only [update_mobile] at hm
  exact Option.some.inj (first.injective hm)

end CoefficientTwoPrecision.FiniteRoles

#print axioms CoefficientTwoPrecision.FiniteRoles.equal_of_diagonal_matches_of_mobile_eq
#print axioms CoefficientTwoPrecision.FiniteRoles.exchange_of_diagonal_matches_of_mobile_ne
