import Quantitative.NeighbourGeometry

/-!
# Actual guard supports and the private-guard rank cases

The foreign stationary set contains one shared control and d+1 guards.
Distinct foreign blocks have at most one common control, so one of those
guards is private. Within the same foreign block, different mobiles also
leave a private guard: the second mobile is stationary in the first set.
-/

namespace CoefficientTwoPrecision.ForeignGuardSets

open ActiveGrid GuardCatalogue GridBackground NeighbourGeometry

variable {d A : Nat}

noncomputable def guardSet (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign) :
    Finset (Fin (guardNumber d A)) := by
  classical
  exact Finset.univ.image (guardIndex hA active foreign mobile)

theorem guardSet_card (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign) :
    (guardSet hA active foreign mobile).card = d + 1 := by
  classical
  rw [guardSet, Finset.card_image_of_injective _ (guardIndex_injective hA active foreign mobile),
    Finset.card_univ, Fintype.card_subtype_compl]
  simp

theorem mem_guardSet_iff (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign)
    (u : Fin (guardNumber d A)) :
    u ∈ guardSet hA active foreign mobile ↔
      guardLabel d A hA active u ∈ activeBlock (d + 3) A (by omega) hA foreign.val ∧
      guardLabel d A hA active u ≠ activeControl d A hA foreign.val mobile.val := by
  classical
  constructor
  · intro hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    rw [guardIndex_label]
    refine ⟨activeControl_mem d A hA foreign.val (mobile.val.succAbove i.val), ?_⟩
    intro he
    have hrow : mobile.val.succAbove i.val = mobile.val := congrArg Prod.fst he
    exact Fin.succAbove_ne mobile.val i.val hrow
  · rintro ⟨hforeign, hmobile⟩
    let p := guardLabel d A hA active u
    have hp : activeControl d A hA foreign.val p.1 = p :=
      activeControl_of_mem hA foreign.val p hforeign
    have hrow : p.1 ≠ mobile.val := by
      intro he
      apply hmobile
      exact hp.symm.trans (congrArg (activeControl d A hA foreign.val) he)
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hrow
    have hcontrol : foreignControl d A hA foreign.val mobile.val i = p := by
      change activeControl d A hA foreign.val (mobile.val.succAbove i) = p
      rw [hi]
      exact hp
    have his : i ≠ sharedIndex hA active foreign mobile := by
      intro he
      rw [he, sharedIndex_control] at hcontrol
      have hs := (Finset.mem_inter.mp (shared_mem hA active foreign)).1
      have hpMem : p ∈ activeBlock (d + 3) A (by omega) hA active := by
        rw [← hcontrol]
        exact hs
      exact guardLabel_not_mem d A hA active u hpMem
    refine Finset.mem_image.mpr ⟨⟨i, his⟩, Finset.mem_univ _, ?_⟩
    apply guardLabel_injective d A hA active
    rw [guardIndex_label]
    exact hcontrol

theorem private_guard_different_blocks (hd : 1 ≤ d) (hA : 0 < A) (active : Active d A)
    (first second : Neighbour d A hA active) (hne : first.val ≠ second.val)
    (mobileFirst : Mobile hA active first) (mobileSecond : Mobile hA active second) :
    ∃ u ∈ guardSet hA active first mobileFirst, u ∉ guardSet hA active second mobileSecond := by
  classical
  apply Finset.not_subset.mp
  intro hsubset
  have hcard : (guardSet hA active first mobileFirst).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    have hu1 := ((mem_guardSet_iff hA active first mobileFirst u).mp hu).1
    have hu2 := ((mem_guardSet_iff hA active second mobileSecond u).mp (hsubset hu)).1
    have hv1 := ((mem_guardSet_iff hA active first mobileFirst v).mp hv).1
    have hv2 := ((mem_guardSet_iff hA active second mobileSecond v).mp (hsubset hv)).1
    have hinter := activeBlock_inter_card (d + 3) A (by omega) hA first.val second.val hne
    have he := Finset.card_le_one.mp hinter _ (Finset.mem_inter.mpr ⟨hu1, hu2⟩)
      _ (Finset.mem_inter.mpr ⟨hv1, hv2⟩)
    exact guardLabel_injective d A hA active he
  rw [guardSet_card] at hcard
  omega

theorem mobile_is_guard (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign) :
    activeControl d A hA foreign.val mobile.val ∉ activeBlock (d + 3) A (by omega) hA active := by
  intro hmem
  have he := intersection_eq_shared hA active foreign _
    (Finset.mem_inter.mpr ⟨hmem, activeControl_mem d A hA foreign.val mobile.val⟩)
  exact mobile.property (congrArg Prod.fst he)

theorem private_guard_different_mobiles (hA : 0 < A) (active : Active d A)
    (foreign : Neighbour d A hA active) (first second : Mobile hA active foreign)
    (hne : first ≠ second) :
    ∃ u ∈ guardSet hA active foreign first, u ∉ guardSet hA active foreign second := by
  classical
  let p := activeControl d A hA foreign.val second.val
  let u := guardEquiv d A hA active ⟨p, mobile_is_guard hA active foreign second⟩
  have hlabel : guardLabel d A hA active u = p := by
    simp only [guardLabel, u, Equiv.symm_apply_apply]
  refine ⟨u, ?_, ?_⟩
  · apply (mem_guardSet_iff hA active foreign first u).mpr
    rw [hlabel]
    refine ⟨activeControl_mem d A hA foreign.val second.val, ?_⟩
    intro he
    apply hne
    apply Subtype.ext
    exact (activeControl_injective d A hA foreign.val he).symm
  · intro hu
    have hn := ((mem_guardSet_iff hA active foreign second u).mp hu).2
    exact hn hlabel

end CoefficientTwoPrecision.ForeignGuardSets

#print axioms CoefficientTwoPrecision.ForeignGuardSets.guardSet_card
#print axioms CoefficientTwoPrecision.ForeignGuardSets.private_guard_different_blocks
#print axioms CoefficientTwoPrecision.ForeignGuardSets.private_guard_different_mobiles
