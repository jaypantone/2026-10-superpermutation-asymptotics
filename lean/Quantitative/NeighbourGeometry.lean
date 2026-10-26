import Quantitative.GridBackground

/-!
# The actual shared control and foreign guard indices

Neighbouring active grid blocks have exactly one common physical control.
Its first coordinate identifies its row in both blocks. If the foreign
mobile is not this control, exactly one foreign stationary index denotes
the shared control; all other stationary controls are actual guards of
the current block.
-/

namespace CoefficientTwoPrecision.NeighbourGeometry

open ActiveGrid ActiveIncidence GuardCatalogue GridBackground

variable {d A : Nat}

abbrev Neighbour (d A : Nat) (hA : 0 < A) (active : Active d A) :=
  {foreign : Active d A // foreign ∈ neighbours (d + 3) A (by omega) hA active}

theorem neighbour_card (d A : Nat) (hA : 0 < A) (active : Active d A) :
    Fintype.card (Neighbour d A hA active) = (d + 3) * (A - 1) := by
  rw [Fintype.card_coe, neighbours_card]

theorem neighbour_ne (hA : 0 < A) (active : Active d A) (foreign : Neighbour d A hA active) :
    foreign.val ≠ active :=
  ((mem_neighbours (d + 3) A (by omega) hA active foreign.val).mp foreign.property).1

noncomputable def shared (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) : Physical d A :=
  Classical.choose (((mem_neighbours (d + 3) A (by omega) hA active foreign.val).mp foreign.property).2)

theorem shared_mem (hA : 0 < A) (active : Active d A) (foreign : Neighbour d A hA active) :
    shared hA active foreign ∈ activeBlock (d + 3) A (by omega) hA active ∩
      activeBlock (d + 3) A (by omega) hA foreign.val :=
  Classical.choose_spec (((mem_neighbours (d + 3) A (by omega) hA active foreign.val).mp foreign.property).2)

theorem intersection_eq_shared (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (p : Physical d A)
    (hp : p ∈ activeBlock (d + 3) A (by omega) hA active ∩
      activeBlock (d + 3) A (by omega) hA foreign.val) : p = shared hA active foreign := by
  have hcard := activeBlock_inter_card (d + 3) A (by omega) hA active foreign.val
    (neighbour_ne hA active foreign).symm
  exact Finset.card_le_one.mp hcard p hp _ (shared_mem hA active foreign)

theorem activeControl_of_mem (hA : 0 < A) (active : Active d A) (p : Physical d A)
    (hp : p ∈ activeBlock (d + 3) A (by omega) hA active) :
    activeControl d A hA active p.1 = p := by
  have hcolumn := (mem_activeBlock (d + 3) A (by omega) hA active p).mp hp
  apply Prod.ext
  · rfl
  · apply Fin.ext
    exact hcolumn.symm

theorem shared_in_current_row (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) :
    activeControl d A hA active (shared hA active foreign).1 = shared hA active foreign :=
  activeControl_of_mem hA active _ (Finset.mem_inter.mp (shared_mem hA active foreign)).1

theorem shared_in_foreign_row (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) :
    activeControl d A hA foreign.val (shared hA active foreign).1 = shared hA active foreign :=
  activeControl_of_mem hA foreign.val _ (Finset.mem_inter.mp (shared_mem hA active foreign)).2

abbrev Mobile (hA : 0 < A) (active : Active d A) (foreign : Neighbour d A hA active) :=
  {mobile : Fin (d + 3) // mobile ≠ (shared hA active foreign).1}

theorem mobile_card (hA : 0 < A) (active : Active d A) (foreign : Neighbour d A hA active) :
    Fintype.card (Mobile hA active foreign) = d + 2 := by
  rw [Fintype.card_subtype_compl]
  simp

noncomputable def sharedIndex (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign) : Fin (d + 2) :=
  Classical.choose (Fin.exists_succAbove_eq mobile.property.symm)

theorem sharedIndex_row (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign) :
    mobile.val.succAbove (sharedIndex hA active foreign mobile) = (shared hA active foreign).1 :=
  Classical.choose_spec (Fin.exists_succAbove_eq mobile.property.symm)

theorem sharedIndex_control (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign) :
    foreignControl d A hA foreign.val mobile.val (sharedIndex hA active foreign mobile) =
      shared hA active foreign := by
  change activeControl d A hA foreign.val (mobile.val.succAbove _) = _
  rw [sharedIndex_row, shared_in_foreign_row]

theorem other_stationary_is_guard (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign)
    (i : Fin (d + 2)) (hi : i ≠ sharedIndex hA active foreign mobile) :
    foreignControl d A hA foreign.val mobile.val i ∉ activeBlock (d + 3) A (by omega) hA active := by
  intro hmem
  have hforeign : foreignControl d A hA foreign.val mobile.val i ∈
      activeBlock (d + 3) A (by omega) hA foreign.val :=
    activeControl_mem d A hA foreign.val (mobile.val.succAbove i)
  have he := intersection_eq_shared hA active foreign _ (Finset.mem_inter.mpr ⟨hmem, hforeign⟩)
  have hs := sharedIndex_control hA active foreign mobile
  exact hi (foreignControl_injective d A hA foreign.val mobile.val (he.trans hs.symm))

noncomputable def guardIndex (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign)
    (i : {i : Fin (d + 2) // i ≠ sharedIndex hA active foreign mobile}) : Fin (guardNumber d A) :=
  guardEquiv d A hA active ⟨foreignControl d A hA foreign.val mobile.val i.val,
    other_stationary_is_guard hA active foreign mobile i.val i.property⟩

theorem guardIndex_injective (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign) :
    Function.Injective (guardIndex hA active foreign mobile) := by
  intro i j hij
  have hsub := (guardEquiv d A hA active).injective hij
  apply Subtype.ext
  exact foreignControl_injective d A hA foreign.val mobile.val (congrArg Subtype.val hsub)

theorem guardIndex_label (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign)
    (i : {i : Fin (d + 2) // i ≠ sharedIndex hA active foreign mobile}) :
    guardLabel d A hA active (guardIndex hA active foreign mobile i) =
      foreignControl d A hA foreign.val mobile.val i.val := by
  simp only [guardLabel, guardIndex, Equiv.symm_apply_apply]

end CoefficientTwoPrecision.NeighbourGeometry

#print axioms CoefficientTwoPrecision.NeighbourGeometry.sharedIndex_control
#print axioms CoefficientTwoPrecision.NeighbourGeometry.other_stationary_is_guard
#print axioms CoefficientTwoPrecision.NeighbourGeometry.guardIndex_injective
