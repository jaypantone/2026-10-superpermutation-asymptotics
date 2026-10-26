import Quantitative.CandidateEvents
import Quantitative.CompiledEventAvoidance
import Quantitative.FiniteJointStates

/-!
# Physical forbidden pairs in the target engine's initial role coordinates

The schedule numbers slots in reverse physical order. A forbidden named
control is represented by its initial engine role, and its physical slot
is reversed. This injective conversion preserves the event set and its
circular separation. Literal natural-role avoidance then implies avoidance
for the actual finite role assignment executed by the target word.
-/

namespace CoefficientTwoPrecision.EventLabelTransport

open PositiveParking JointStates RepairAvoidance CyclicRepairSchedule

variable {k : Nat}

def encodeRole (role : FiniteRoles.Role k) : Option Nat := role.map Fin.val

theorem encodeRole_injective : Function.Injective (encodeRole (k := k)) := by
  intro p q he
  cases p with
  | none => cases q <;> simpa [encodeRole] using he
  | some i =>
      cases q with
      | none => simpa [encodeRole] using he
      | some j => exact congrArg some (Fin.ext (Option.some.inj he))

theorem encodeRole_bound (role : FiniteRoles.Role k) : roleIndex (encodeRole role) ≤ k := by
  cases role with
  | none => simp [encodeRole, roleIndex]
  | some i => simp only [encodeRole, Option.map_some, roleIndex]; have hi := i.isLt; omega

theorem star_encode (target : Fin k) (role : FiniteRoles.Role k) :
    encodeRole ((Equiv.swap none (some target)) role) = star target.val (encodeRole role) := by
  cases role with
  | none => simp [encodeRole]
  | some i =>
      by_cases hi : i = target
      · subst i
        simp [encodeRole]
      · have hv : i.val ≠ target.val := fun he => hi (Fin.ext he)
        simp [encodeRole, Equiv.swap_apply_of_ne_of_ne, hi, hv, PositiveParking.star]

theorem execute_encoded (word : List (Fin k))
    (labels : Option Nat → Option Nat) (assignment : Equiv.Perm (FiniteRoles.Role k))
    (hagrees : ∀ p, labels (encodeRole p) = encodeRole (assignment p)) :
    ∀ p, (execute updateLabels (word.map Fin.val) labels) (encodeRole p) =
      encodeRole (FiniteRoles.execute word assignment p) := by
  induction word generalizing labels assignment with
  | nil => exact hagrees
  | cons target rest ih =>
      apply ih (updateLabels target.val labels) (FiniteRoles.update target assignment)
      intro p
      change labels (star target.val (encodeRole p)) =
        encodeRole (assignment ((Equiv.swap none (some target)) p))
      rw [← star_encode, hagrees]

/-- The conclusion is about the actual finite assignment, with the
natural-role theorem used only through the proved encoding identity. -/
theorem finite_avoidance {Control : Type} (word : List (Fin k))
    (initial : FiniteRoles.Role k ≃ Control) (control : Control) (slot : Fin k)
    (havoid : (execute updateLabels (word.map Fin.val) id) (some slot.val) ≠
      encodeRole (initial.symm control)) :
    FiniteRoles.execute word initial (some slot) ≠ control := by
  intro he
  have htrans := FiniteJointStates.execute_trans word (Equiv.refl _) initial
  change FiniteRoles.execute word initial =
    (FiniteRoles.execute word (Equiv.refl _)).trans initial at htrans
  rw [htrans] at he
  have hrole : FiniteRoles.execute word (Equiv.refl _) (some slot) = initial.symm control := by
    apply initial.injective
    exact he.trans (initial.apply_symm_apply control).symm
  have hencoded := execute_encoded word id (Equiv.refl _) (fun _ => rfl) (some slot)
  rw [hrole] at hencoded
  exact havoid hencoded

def encodePair {Control : Type} (initial : FiniteRoles.Role k ≃ Control)
    (pair : Control × Fin k) : ForbiddenPair :=
  (encodeRole (initial.symm pair.1), pair.2.rev.val)

theorem encodePair_injective {Control : Type} (initial : FiniteRoles.Role k ≃ Control) :
    Function.Injective (encodePair initial) := by
  intro p q he
  apply Prod.ext
  · exact initial.symm.injective (encodeRole_injective (congrArg Prod.fst he))
  · exact Fin.rev_injective (Fin.ext (congrArg Prod.snd he))

theorem encodePair_role {Control : Type} (initial : FiniteRoles.Role k ≃ Control)
    (pair : Control × Fin k) : roleIndex (encodePair initial pair).1 ≤ k :=
  encodeRole_bound _

noncomputable def mapEvents {M : Nat} {Label Label' : Type}
    [DecidableEq Label] [DecidableEq Label'] (f : Label → Label')
    (events : Finset (ZMod M × Label)) : Finset (ZMod M × Label') := by
  classical
  exact events.image (fun event => (event.1, f event.2))

theorem mapEvents_card {M : Nat} {Label Label' : Type}
    [DecidableEq Label] [DecidableEq Label'] (f : Label → Label')
    (events : Finset (ZMod M × Label)) : (mapEvents f events).card ≤ events.card :=
  Finset.card_image_le

theorem mapEvents_separated {M L : Nat} {Label Label' : Type}
    [DecidableEq Label] [DecidableEq Label'] (f : Label → Label')
    (events : Finset (ZMod M × Label)) (hsep : Separated events L) :
    Separated (mapEvents f events) L := by
  classical
  intro x hx y hy delta hd he
  obtain ⟨sourceX, hxSource, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨sourceY, hySource, rfl⟩ := Finset.mem_image.mp hy
  exact congrArg f (hsep sourceX hxSource sourceY hySource delta hd he)

theorem encoded_label_bounds {M : Nat} {Control : Type} [DecidableEq Control]
    (initial : FiniteRoles.Role k ≃ Control) (events : Finset (ZMod M × (Control × Fin k)))
    (event : ZMod M × ForbiddenPair) (hevent : event ∈ mapEvents (encodePair initial) events) :
    roleIndex event.2.1 ≤ k ∧ event.2.2 < k := by
  classical
  obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp hevent
  exact ⟨encodePair_role initial source.2, source.2.2.rev.isLt⟩

end CoefficientTwoPrecision.EventLabelTransport

#print axioms CoefficientTwoPrecision.EventLabelTransport.finite_avoidance
#print axioms CoefficientTwoPrecision.EventLabelTransport.encodePair_injective
#print axioms CoefficientTwoPrecision.EventLabelTransport.mapEvents_separated
