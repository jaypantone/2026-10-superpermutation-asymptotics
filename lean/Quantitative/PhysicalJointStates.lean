import Quantitative.FiniteJointStates
import Quantitative.RobustMatching
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Option

/-!
# Joint states expressed in increasing physical cut order

The target engine numbers positions by their descending normal-order ranks.
The frame reconstruction numbers them by increasing cut value. Reversing
the stationary indices, while fixing the mobile role, conjugates the finite
role action and reverses the phase coordinates. The same joint index is used
for both parts of this change of coordinates.
-/

namespace CoefficientTwoPrecision.PhysicalJointStates

open FiniteRoles JointStates

def reverseRoles (k : Nat) : Equiv.Perm (FiniteRoles.Role k) :=
  Equiv.optionCongr Fin.revPerm

@[simp] theorem reverseRoles_none (k : Nat) : reverseRoles k none = none := rfl

@[simp] theorem reverseRoles_some {k : Nat} (i : Fin k) :
    reverseRoles k (some i) = some i.rev := rfl

def action (k : Nat) (index : Index k) : Equiv.Perm (FiniteRoles.Role k) :=
  ((reverseRoles k).trans (FiniteJointStates.action k index)).trans (reverseRoles k)

def phase (k : Nat) (index : Index k) (i : Fin k) : Bool :=
  decide ((interpret k (List.range k) index).phases i.rev.val = 1)

theorem phase_le_one (k : Nat) (index : Index k) (i : Fin k) :
    (interpret k (List.range k) index).phases i.rev.val ≤ 1 := by
  apply JointStates.phase_le_one
  exact (MacroCatalogue.menu_perm k index.2.1).nodup_iff.mpr List.nodup_range

theorem phase_value {M k : Nat} (index : Index k) (i : Fin k) :
    ((interpret k (List.range k) index).phases i.rev.val : ZMod M) =
      (RobustMatching.bit (phase k index i) : ZMod M) := by
  have h := phase_le_one k index i
  have hcases : (interpret k (List.range k) index).phases i.rev.val = 0 ∨
      (interpret k (List.range k) index).phases i.rev.val = 1 := by omega
  rcases hcases with hzero | hone
  · unfold phase
    rw [hzero]
    norm_num [RobustMatching.bit]
  · unfold phase
    rw [hone]
    norm_num [RobustMatching.bit]

theorem mobile_label {k : Nat} {Control : Type} (index : Index k)
    (initial : FiniteRoles.Role k ≃ Control) :
    FiniteRoles.lift ((reverseRoles k).trans initial)
      ((interpret k (List.range k) index).labels none) =
      ((action k index).trans initial) none := by
  have h := (FiniteJointStates.action_agrees index ((reverseRoles k).trans initial)).1
  simpa only [action, Equiv.trans_apply, reverseRoles_none] using h

theorem stationary_label {k : Nat} {Control : Type} (index : Index k)
    (initial : FiniteRoles.Role k ≃ Control) (i : Fin k) :
    FiniteRoles.lift ((reverseRoles k).trans initial)
      ((interpret k (List.range k) index).labels (some i.rev.val)) =
      ((action k index).trans initial) (some i) := by
  have h := (FiniteJointStates.action_agrees index ((reverseRoles k).trans initial)).2 i.rev
  simpa only [action, Equiv.trans_apply, reverseRoles_some] using h

end CoefficientTwoPrecision.PhysicalJointStates

#print axioms CoefficientTwoPrecision.PhysicalJointStates.phase_value
#print axioms CoefficientTwoPrecision.PhysicalJointStates.stationary_label
