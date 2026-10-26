import Quantitative.FiniteRoles
import Quantitative.PositiveSchedule

/-!
# Finite role assignments throughout an actual target word

The literal engine uses a total function on optional natural numbers.
Only the mobile role and the first k stationary roles are relevant. Agreement
on those roles is preserved by every update and hence by every target prefix.
This supplies a finite bijective assignment at each actual schedule time.
-/

namespace CoefficientTwoPrecision.FiniteRoles

open PositiveParking

variable {k : Nat} {α : Type}

def update (target : Fin k) (assignment : Role k ≃ α) : Role k ≃ α :=
  (Equiv.swap none (some target)).trans assignment

def Agrees (labels : Option Nat → α) (assignment : Role k ≃ α) : Prop :=
  labels none = assignment none ∧
    ∀ i : Fin k, labels (some i.val) = assignment (some i)

theorem lift_agrees (assignment : Role k ≃ α) : Agrees (lift assignment) assignment :=
  ⟨rfl, lift_stationary assignment⟩

@[simp] theorem update_mobile (target : Fin k) (assignment : Role k ≃ α) :
    update target assignment none = assignment (some target) := by
  simp [update]

@[simp] theorem update_target (target : Fin k) (assignment : Role k ≃ α) :
    update target assignment (some target) = assignment none := by
  simp [update]

theorem update_other (target i : Fin k) (assignment : Role k ≃ α) (hi : i ≠ target) :
    update target assignment (some i) = assignment (some i) := by
  simp [update, Equiv.swap_apply_of_ne_of_ne, hi]

theorem update_agrees (target : Fin k) (labels : Option Nat → α)
    (assignment : Role k ≃ α) (h : Agrees labels assignment) :
    Agrees (updateLabels target.val labels) (update target assignment) := by
  constructor
  · simpa only [updateLabels, star_mobile, update_mobile] using h.2 target
  · intro i
    by_cases hi : i = target
    · subst i
      simpa only [updateLabels, star_target, update_target] using h.1
    · have hval : i.val ≠ target.val := fun hv => hi (Fin.ext hv)
      simpa only [updateLabels, star_other target.val i.val hval,
        update_other target i assignment hi] using h.2 i

def execute : List (Fin k) → (Role k ≃ α) → Role k ≃ α
  | [], assignment => assignment
  | target :: rest, assignment => execute rest (update target assignment)

theorem execute_agrees (word : List (Fin k)) (labels : Option Nat → α)
    (assignment : Role k ≃ α) (h : Agrees labels assignment) :
    Agrees (PositiveSchedule.executeLabels word labels) (execute word assignment) := by
  induction word generalizing labels assignment with
  | nil => exact h
  | cons target rest ih => exact ih _ _ (update_agrees target labels assignment h)

/-- The actual label function obtained at every target prefix is the
restriction of a finite bijection on all control roles. -/
theorem execute_lift_agrees (word : List (Fin k)) (assignment : Role k ≃ α) :
    Agrees (PositiveSchedule.executeLabels word (lift assignment)) (execute word assignment) :=
  execute_agrees word _ assignment (lift_agrees assignment)

end CoefficientTwoPrecision.FiniteRoles

#print axioms CoefficientTwoPrecision.FiniteRoles.execute_lift_agrees
