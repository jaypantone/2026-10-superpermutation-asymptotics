import Quantitative.FiniteRoleExecution
import Quantitative.NormalContour
import Quantitative.LiteralEnvelope

/-!
# The joint catalogue acts by actual finite role permutations

The finite target word below has exactly the same normal and parking
prefix as a catalogue index. Its action is a bijection on the k stationary
roles and the mobile role. It agrees with the symbolic action used in the
literal envelope on every active role. Thus reconstructing current labels
also reconstructs initial labels through a fixed finite permutation.
-/

namespace CoefficientTwoPrecision.FiniteJointStates

open PositiveParking JointStates NormalContour

def swapFirstTwo {α : Type} : List α → List α
  | a :: b :: rest => b :: a :: rest
  | word => word

theorem map_swapFirstTwo (k : Nat) (word : List (Fin k)) :
    (swapFirstTwo word).map Fin.val = JointStates.swapFirstTwo (word.map Fin.val) := by
  cases word with
  | nil => rfl
  | cons a rest => cases rest <;> rfl

def finiteMenu (k : Nat) : Bool → List (Fin k)
  | false => List.finRange k
  | true => swapFirstTwo (List.finRange k)

theorem finiteMenu_map (k : Nat) (choice : Bool) :
    (finiteMenu k choice).map Fin.val = menu (List.range k) choice := by
  cases choice
  · exact map_finRange_val k
  · simp only [finiteMenu, map_swapFirstTwo, map_finRange_val, menu]

def targetWord (k : Nat) (index : Index k) : List (Fin k) :=
  repeatWord index.1.val (List.finRange k) ++
    ((finiteMenu k index.2.1) ++ (finiteMenu k index.2.1).reverse).take index.2.2.val

theorem targetWord_map (k : Nat) (index : Index k) :
    (targetWord k index).map Fin.val =
      repeatWord index.1.val (List.range k) ++
        pairPrefix (menu (List.range k) index.2.1) index.2.2.val := by
  simp only [targetWord, List.map_append, repeatWord_map, map_finRange_val,
    List.map_take, List.map_reverse, finiteMenu_map, pairPrefix]

def action (k : Nat) (index : Index k) : Equiv.Perm (FiniteRoles.Role k) :=
  FiniteRoles.execute (targetWord k index) (Equiv.refl _)

theorem execute_trans {k : Nat} {α β : Type} (word : List (Fin k))
    (assignment : FiniteRoles.Role k ≃ α) (rename : α ≃ β) :
    FiniteRoles.execute word (assignment.trans rename) =
      (FiniteRoles.execute word assignment).trans rename := by
  induction word generalizing assignment with
  | nil => rfl
  | cons target word ih => exact ih (FiniteRoles.update target assignment)

theorem execute_action {k : Nat} {α : Type} (index : Index k)
    (assignment : FiniteRoles.Role k ≃ α) :
    FiniteRoles.execute (targetWord k index) assignment = (action k index).trans assignment := by
  exact execute_trans (targetWord k index) (Equiv.refl _) assignment

theorem action_agrees {k : Nat} {α : Type} (index : Index k)
    (assignment : FiniteRoles.Role k ≃ α) :
    FiniteRoles.Agrees
      (fun p => FiniteRoles.lift assignment ((interpret k (List.range k) index).labels p))
      ((action k index).trans assignment) := by
  have hroles : execute updateLabels ((targetWord k index).map Fin.val) (id : Assignment) =
      (interpret k (List.range k) index).labels := by
    rw [targetWord_map, execute_append]
    rfl
  have hlabels : PositiveSchedule.executeLabels (targetWord k index) (FiniteRoles.lift assignment) =
      fun p => FiniteRoles.lift assignment ((interpret k (List.range k) index).labels p) := by
    rw [PositiveSchedule.executeLabels_eq_execute]
    have h := LiteralEnvelope.execute_pullback ((targetWord k index).map Fin.val)
      (FiniteRoles.lift assignment) (id : Assignment)
    rw [hroles] at h
    exact h
  have h := FiniteRoles.execute_lift_agrees (targetWord k index) assignment
  rw [hlabels, execute_action] at h
  exact h

end CoefficientTwoPrecision.FiniteJointStates

#print axioms CoefficientTwoPrecision.FiniteJointStates.action_agrees
