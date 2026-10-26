import Quantitative.LabelCompletion
import Quantitative.CyclicMatching

/-!
# At most two initial assignments for one cyclic positional matching

The matching fixes all stationary labels except the omitted one. The other
unfixed role is the mobile role. A fixed joint-state action is a bijection,
so passing from current assignments back to initial assignments introduces
no further multiplicity.
-/

namespace CoefficientTwoPrecision.CyclicLabelCount

open FiniteRoles

variable {n : Nat}

noncomputable def candidates (source : Equiv.Perm (Role (n + 1)))
    (targetAction : Equiv.Perm (Role (n + 1)))
    (omitted other : Fin (n + 1)) (offset : Fin n) :
    Finset (Equiv.Perm (Role (n + 1))) := by
  classical
  exact Finset.univ.filter (fun initial => ∀ i : Fin n,
    source (some (omitted.succAbove (i + offset))) =
      (targetAction.trans initial) (some (other.succAbove i)))

theorem candidates_card (source : Equiv.Perm (Role (n + 1)))
    (targetAction : Equiv.Perm (Role (n + 1)))
    (omitted other : Fin (n + 1)) (offset : Fin n) :
    (candidates source targetAction omitted other offset).card ≤ 2 := by
  classical
  let S := candidates source targetAction omitted other offset
  rcases S.eq_empty_or_nonempty with hnil | ⟨reference, href⟩
  · change S.card ≤ 2
    rw [hnil, Finset.card_empty]
    omega
  · let T := Finset.univ.filter (fun current : Equiv.Perm (Role (n + 1)) =>
      ∀ x, x ≠ none → x ≠ some other → current x = (targetAction.trans reference) x)
    have hmap : Set.MapsTo (fun initial : Equiv.Perm (Role (n + 1)) => targetAction.trans initial)
        (S : Set (Equiv.Perm (Role (n + 1)))) (T : Set (Equiv.Perm (Role (n + 1)))) := by
      intro initial hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro role hnone hother
      cases role with
      | none => exact False.elim (hnone rfl)
      | some j =>
        have hj : j ≠ other := fun h => hother (congrArg some h)
        obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
        exact ((Finset.mem_filter.mp hi).2 i).symm.trans ((Finset.mem_filter.mp href).2 i)
    have hinj : (S : Set (Equiv.Perm (Role (n + 1)))).InjOn
        (fun initial => targetAction.trans initial) := by
      intro first _ second _ heq
      apply Equiv.ext
      intro role
      have h := congrArg (fun f : Equiv.Perm (Role (n + 1)) => f (targetAction.symm role)) heq
      simpa only [Equiv.trans_apply, targetAction.apply_symm_apply] using h
    exact (Finset.card_le_card_of_injOn _ hmap hinj).trans
      (LabelCompletion.extensions_card_le_two (targetAction.trans reference) none (some other))

end CoefficientTwoPrecision.CyclicLabelCount

#print axioms CoefficientTwoPrecision.CyclicLabelCount.candidates_card
