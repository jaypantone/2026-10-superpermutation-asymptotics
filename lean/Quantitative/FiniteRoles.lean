import Quantitative.JointStates
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Card

/-!
# Finite assignments and the shared stationary controls

There are k stationary roles and one mobile role. Two bijective assignments
have at least k-1 controls stationary on both sides, even when their mobile
controls differ. This count concerns the named controls, not unlabelled cuts.
-/

namespace CoefficientTwoPrecision.FiniteRoles

abbrev Role (k : Nat) := Option (Fin k)

variable {k : Nat} {α : Type}

/-- Extend a finite assignment to the target-word engine. Targets outside
the actual stationary range are never updated; the extension gives them
the mobile value merely to define a total function. -/
def lift (assignment : Role k ≃ α) : Option Nat → α
  | none => assignment none
  | some i => if h : i < k then assignment (some ⟨i, h⟩) else assignment none

@[simp] theorem lift_mobile (assignment : Role k ≃ α) :
    lift assignment none = assignment none := rfl

@[simp] theorem lift_stationary (assignment : Role k ≃ α) (i : Fin k) :
    lift assignment (some i.val) = assignment (some i) := by simp [lift]

theorem residents_injective (assignment : Role k ≃ α) :
    Function.Injective (fun i : Fin k => lift assignment (some i.val)) := by
  intro i j hij
  simpa only [lift_stationary, assignment.injective.eq_iff, Option.some.injEq] using hij

theorem mobile_ne_resident (assignment : Role k ≃ α) (i : Fin k) :
    lift assignment none ≠ lift assignment (some i.val) := by
  simp only [lift_mobile, lift_stationary, assignment.injective.ne_iff, ne_eq,
    reduceCtorEq, not_false_eq_true]

def Matches (first second : Role k ≃ α) (i j : Fin k) : Prop :=
  first (some i) = second (some j)

noncomputable def matchedSources (first second : Role k ≃ α) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j, Matches first second i j)

theorem unmatched_is_mobile (first second : Role k ≃ α) (i : Fin k)
    (h : ¬ ∃ j, Matches first second i j) : first (some i) = second none := by
  obtain ⟨role, hrole⟩ := second.surjective (first (some i))
  cases role with
  | none => exact hrole.symm
  | some j => exact False.elim (h ⟨j, hrole.symm⟩)

theorem matchedSources_card (first second : Role k ≃ α) :
    k ≤ (matchedSources first second).card + 1 := by
  classical
  let omitted := Finset.univ.filter (fun i : Fin k => ¬ ∃ j, Matches first second i j)
  have hone : omitted.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    apply Option.some.inj
    apply first.injective
    exact (unmatched_is_mobile first second i (Finset.mem_filter.mp hi).2).trans
      (unmatched_is_mobile first second j (Finset.mem_filter.mp hj).2).symm
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k))) (fun i => ∃ j, Matches first second i j)
  have heq : (matchedSources first second).card + omitted.card = k := by
    simpa only [matchedSources, omitted, Finset.card_univ, Fintype.card_fin] using hsplit
  omega

theorem two_matches (hk : 3 ≤ k) (first second : Role k ≃ α) :
    ∃ i j i' j' : Fin k, i ≠ i' ∧ Matches first second i j ∧
      Matches first second i' j' := by
  classical
  have hcard := matchedSources_card first second
  have htwo : 1 < (matchedSources first second).card := by omega
  obtain ⟨i, hi, i', hi', hne⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨j', hj'⟩ := (Finset.mem_filter.mp hi').2
  exact ⟨i, j, i', j', hne, hj, hj'⟩

theorem matches_target_unique (first second : Role k ≃ α) (i j j' : Fin k)
    (h : Matches first second i j) (h' : Matches first second i j') : j = j' :=
  Option.some.inj (second.injective (h.symm.trans h'))

theorem matches_source_unique (first second : Role k ≃ α) (i i' j : Fin k)
    (h : Matches first second i j) (h' : Matches first second i' j) : i = i' :=
  Option.some.inj (first.injective (h.trans h'.symm))

end CoefficientTwoPrecision.FiniteRoles

#print axioms CoefficientTwoPrecision.FiniteRoles.matchedSources_card
#print axioms CoefficientTwoPrecision.FiniteRoles.two_matches
