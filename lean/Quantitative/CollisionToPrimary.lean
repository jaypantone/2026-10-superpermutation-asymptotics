import Quantitative.CollisionGeometry
import Quantitative.PrimaryCatalogue
import Quantitative.StationaryWeightTransport

/-!
# Literal cross-block collisions belong to the primary catalogue

Filtering the two full cyclic rows identifies the original cut of their
shared stationary control. Every other foreign stationary control is a
named guard of the current block. These identifications transport the
foreign affine relation to the current guard variables and the actual
current slot and time. The resulting congruence is a catalogue entry.
-/

namespace CoefficientTwoPrecision.CollisionToPrimary

open GuardCatalogue GridBackground NeighbourGeometry PhysicalOldCuts
open CollisionGeometry StationaryRelations GuardEvents ActiveSlotEvents PrimaryCatalogue

private theorem relation_of_offsets {m G d : Nat}
    (hm : 0 < m) (hd : 2 ≤ d) (assignment : Assignment d)
    (x : Fin (d + 2) → Fin m) (localCuts : Fin (d + 2) → Fin (m + G))
    (hoffset : ∀ i, ∃ e ≤ G, (localCuts i).val = (x i).val + e)
    (q : Fin (d + 2) → Int) (phase : Fin (d + 2) → Fin 2) (t : Int)
    (hq : Int.ModEq ((m + G : Nat) : Int) (∑ i, weight assignment i * q i) 0)
    (hlocal : ∀ i, Int.ModEq ((m + G : Nat) : Int) (localCuts i).val
      (q i + t + (phase i).val)) :
    ∃ b : Int, b.natAbs ≤ stationaryOffsetBound d G ∧
      Int.ModEq (m : Int) (∑ i, weight assignment i * (x i).val) b := by
  choose e he hxe using hoffset
  have hsum := weight_abs_sum hd assignment
  have hphase (i : Fin (d + 2)) :
      0 ≤ ((phase i).val : Int) ∧ ((phase i).val : Int) ≤ 1 := by
    have hi := (phase i).isLt
    omega
  have hframe := frame_relation ((m + G : Nat) : Int) t (weight assignment) q
    (fun i => ((phase i).val : Int)) (fun i => ((localCuts i).val : Int))
    (weight_sum assignment) hq hlocal
  obtain ⟨ell, hell, hrel⟩ := bounded_winding (m + G) (2 * d) (by omega)
    (weight assignment) (fun i => ((localCuts i).val : Int))
    (fun i => ((phase i).val : Int)) hsum
    (fun i => by have hi := (localCuts i).isLt; omega) hphase hframe
  have hph := weighted_abs_bound (weight assignment)
    (fun i => ((phase i).val : Int)) 1 (fun i => by have hi := hphase i; omega)
  rw [hsum, Nat.mul_one] at hph
  exact old_relation_of_offsets m G d (weight assignment)
    (fun i => ((x i).val : Int)) (fun i => (e i : Int))
    (fun i => ((localCuts i).val : Int)) ell
    (∑ i, weight assignment i * (phase i).val) hsum
    (fun i => by simpa only [Int.natAbs_natCast] using he i)
    (fun i => by exact_mod_cast hxe i) (by omega) hph
    (by simpa only [Nat.cast_add] using hrel)

private theorem stationary_slot {d : Nat}
    (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3)) (row : Fin (d + 3))
    (hne : role none ≠ row) : ∃ j, role (some j) = row := by
  cases h : role.symm row with
  | none =>
      have he := role.apply_symm_apply row
      rw [h] at he
      exact False.elim (hne he)
  | some j =>
      exact ⟨j, by simpa only [h] using role.apply_symm_apply row⟩

variable {m d A : Nat} {α : Type} [DecidableEq α]
variable (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A)
variable (old : Fin m → α) (ho : Function.Injective old)
variable (label : Physical d A → α) (hl : Function.Injective label)
variable (hcross : ∀ p i, label p ≠ old i)

include hm hd

/-- A collision of the two actual cyclic rows gives an event at the
current time. Its current slot carries the actual shared control. -/
theorem collision_event (active : Active d A) (foreign : Neighbour d A hA active)
    (guardCutsL guardCutsR : Fin (guardNumber d A) ↪ Fin m)
    (hgoodL : guardCutsL ∈ goodEmbeddings m d A hA active)
    (hgoodR : guardCutsR ∈ goodEmbeddings m d A hA foreign.val)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (hframeL : HasFrame localL) (hframeR : HasFrame localR)
    (qL : Fin (d + 2) → Fin (m + guardNumber d A))
    (time : Fin (m + guardNumber d A)) (phaseL : Fin (d + 2) → Fin 2)
    (hlocalL : ∀ j, (localL j).val =
      ((qL j).val + time.val + (phaseL j).val) % (m + guardNumber d A))
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign.val guardCutsR roleR localR gapR)) :
    ∃ event : Event d A hA active, event.1 = foreign ∧
      residentControl hA active roleL (slot hA active event) = shared hA active foreign ∧
      time ∈ times m hA active guardCutsL qL event := by
  classical
  have hmobileR := foreign_mobile_not_shared hm hd hA old ho label hl hcross
    active foreign guardCutsL guardCutsR hgoodL roleL roleR localL localR gapL gapR hframeR hcyclic
  have hmobileL := current_mobile_not_shared hm hd hA old ho label hl hcross
    active foreign guardCutsL guardCutsR hgoodR roleL roleR localL localR gapL gapR hframeL hcyclic
  let mobile : Mobile hA active foreign := ⟨roleR none, hmobileR⟩
  let sharedSlot := sharedIndex hA active foreign mobile
  obtain ⟨slotsR, hslotsR⟩ := slotEquiv_exists roleR
  obtain ⟨targetL, htargetL⟩ := stationary_slot roleL (shared hA active foreign).1 hmobileL
  have hcontrolL : residentControl hA active roleL targetL = shared hA active foreign := by
    change activeControl d A hA active (roleL (some targetL)) = _
    rw [htargetL, shared_in_current_row]
  have hcontrolR : residentControl hA foreign.val roleR (slotsR sharedSlot) =
      shared hA active foreign := by
    change activeControl d A hA foreign.val (roleR (some (slotsR sharedSlot))) = _
    rw [hslotsR]
    exact sharedIndex_control hA active foreign mobile
  obtain ⟨commonCut, eL, heL, eR, heR, hposL, hposR⟩ :=
    common_resident_offsets hA old ho label hl hcross active foreign.val
      guardCutsL guardCutsR roleL roleR localL localR gapL gapR targetL (slotsR sharedSlot)
      (hcontrolL.trans hcontrolR.symm) hcyclic
  obtain ⟨error, hlo, hhi, herror, hshared⟩ := active_slot_offset m (guardNumber d A) hm
    (qL targetL) time (localL targetL) (phaseL targetL) commonCut eL heL hposL (hlocalL targetL)
  let x : Fin (d + 2) → Fin m := fun i =>
    if hi : i = sharedSlot then commonCut
    else guardCutsL (guardIndex hA active foreign mobile ⟨i, hi⟩)
  have hxShared : x sharedSlot = commonCut := by simp only [x, dif_pos rfl]
  have hoffset : ∀ i, ∃ e ≤ guardNumber d A,
      (localR (slotsR i)).val = (x i).val + e := by
    intro i
    by_cases hi : i = sharedSlot
    · subst i
      exact ⟨eR, heR, by simpa only [hxShared] using hposR⟩
    · have htracked : guardLabel d A hA active (guardIndex hA active foreign mobile ⟨i, hi⟩) =
          residentControl hA foreign.val roleR (slotsR i) := by
        rw [guardIndex_label]
        change activeControl d A hA foreign.val (mobile.val.succAbove i) =
          activeControl d A hA foreign.val (roleR (some (slotsR i)))
        rw [hslotsR]
      obtain ⟨e, he, hpos⟩ := PhysicalOldCuts.resident_guard_offset hA old ho label hl hcross
        active foreign.val guardCutsL guardCutsR roleL roleR localL localR gapL gapR
        (guardIndex hA active foreign mobile ⟨i, hi⟩) (slotsR i) htracked hcyclic
      exact ⟨e, he, by simpa only [x, dif_neg hi] using hpos⟩
  obtain ⟨sumSlot, qR, phaseR, tR, hsumR, hqR, hlocalR⟩ := hframeR
  obtain ⟨assignment, hweights, hphysical⟩ := StationaryWeightTransport.physical_relation
    ((m + guardNumber d A : Nat) : Int) sumSlot hsumR slotsR qR hqR
  obtain ⟨b, hb, hforeign⟩ := relation_of_offsets hm hd assignment x
    (fun i => localR (slotsR i)) hoffset (fun i => qR (slotsR i))
    (fun i => phaseR (slotsR i)) tR hphysical (fun i => hlocalR (slotsR i))
  have hshared' : Int.ModEq (m : Int) ((x sharedSlot).val : Int)
      ((qL targetL).val + (time.val : Int) + error) := by
    simpa only [hxShared] using hshared
  obtain ⟨b1, hb1, hprimary⟩ := primary_relation m (guardNumber d A) hd assignment sharedSlot
    (fun i => ((x i).val : Int)) (qL targetL).val time.val error b hforeign hb hshared' herror
  let offset : Fin (2 * primaryOffsetBound d (guardNumber d A) + 1) :=
    ⟨(b1 + primaryOffsetBound d (guardNumber d A)).toNat, by omega⟩
  let event : Event d A hA active := ⟨foreign, mobile, assignment, targetL, offset⟩
  have hrhs : rhs hA active event = b1 := by
    change ((b1 + primaryOffsetBound d (guardNumber d A)).toNat : Int) -
      primaryOffsetBound d (guardNumber d A) = b1
    omega
  have hremaining : remainingSum assignment sharedSlot (fun i => ((x i).val : Int)) =
      guardSum hA active event guardCutsL := by
    have he := Fintype.sum_eq_add_sum_subtype_ne
      (fun i => weight assignment i * ((x i).val : Int)) sharedSlot
    rw [split_shared] at he
    have he' := add_left_cancel he
    calc
      remainingSum assignment sharedSlot (fun i => ((x i).val : Int)) =
          ∑ i : {i : Fin (d + 2) // i ≠ sharedSlot},
            weight assignment i.val * ((x i.val).val : Int) := he'
      _ = guardSum hA active event guardCutsL := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [x, dif_neg i.property]
        rfl
  refine ⟨event, rfl, hcontrolL, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change Int.ModEq (m : Int)
    (weight assignment sharedSlot * ((qL targetL).val + (time.val : Int)) +
      guardSum hA active event guardCutsL) (rhs hA active event)
  rw [hrhs, ← hremaining]
  exact hprimary

end CoefficientTwoPrecision.CollisionToPrimary

#print axioms CoefficientTwoPrecision.CollisionToPrimary.collision_event
