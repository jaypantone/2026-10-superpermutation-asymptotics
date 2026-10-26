import Quantitative.SameBlockCollision
import Quantitative.SourceProjection

/-!
# Assigning the actual alphabet to the control grid

The old letters are indexed in their given order. A bijection indexes
the control list by the physical grid. For each active block, its
complement supplies the guard letters in the background. Their union
with the active letters is exactly the prescribed alphabet.
-/

namespace CoefficientTwoPrecision.GridAlphabet

open GuardCatalogue GridBackground ActiveGrid StationaryCircle StationaryUpdate
open SuperpermutationUpperBound SourceProjection

variable {m d A : Nat}

def oldSymbol (old : List Nat) (hlen : old.length = m) (i : Fin m) : Nat :=
  old[i.val]'(by omega)

theorem oldSymbol_injective (old : List Nat) (hlen : old.length = m) (hnd : old.Nodup) :
    Function.Injective (oldSymbol old hlen) := by
  intro i j hij
  apply Fin.ext
  exact hnd.getElem_inj_iff.mp hij

theorem oldSymbol_mem (old : List Nat) (hlen : old.length = m) (i : Fin m) :
    oldSymbol old hlen i ∈ old := List.getElem_mem _

theorem oldSymbol_range (old : List Nat) (hlen : old.length = m) (a : Nat) :
    a ∈ old ↔ ∃ i, oldSymbol old hlen i = a := by
  constructor
  · intro ha
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
    exact ⟨⟨i, by omega⟩, he⟩
  · rintro ⟨i, rfl⟩
    exact oldSymbol_mem old hlen i

theorem oldSymbol_word (old : List Nat) (hlen : old.length = m) :
    (List.finRange m).map (oldSymbol old hlen) = old := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_finRange, oldSymbol, Fin.val_cast, Fin.val_mk]

noncomputable def gridIndex (controls : List Nat)
    (hlen : controls.length = (d + 3) * ((d + 3) * A)) :
    Physical d A ≃ Fin controls.length :=
  Fintype.equivFinOfCardEq ((controls_card (d + 3) A).trans hlen.symm)

noncomputable def label (controls : List Nat)
    (hlen : controls.length = (d + 3) * ((d + 3) * A)) (p : Physical d A) : Nat :=
  controls.get (gridIndex controls hlen p)

theorem label_injective (controls : List Nat)
    (hlen : controls.length = (d + 3) * ((d + 3) * A)) (hnd : controls.Nodup) :
    Function.Injective (label controls hlen) :=
  hnd.injective_get.comp (gridIndex controls hlen).injective

theorem label_mem (controls : List Nat)
    (hlen : controls.length = (d + 3) * ((d + 3) * A)) (p : Physical d A) :
    label controls hlen p ∈ controls := List.get_mem _ _

theorem label_range (controls : List Nat)
    (hlen : controls.length = (d + 3) * ((d + 3) * A)) (a : Nat) :
    a ∈ controls ↔ ∃ p, label controls hlen p = a := by
  constructor
  · intro ha
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    refine ⟨(gridIndex controls hlen).symm i, ?_⟩
    simpa only [label, Equiv.apply_symm_apply] using hi
  · rintro ⟨p, rfl⟩
    exact label_mem controls hlen p

theorem labels_disjoint (controls old : List Nat)
    (hw : controls.length = (d + 3) * ((d + 3) * A)) (hm : old.length = m)
    (hnd : (controls ++ old).Nodup) (p : Physical d A) (i : Fin m) :
    label controls hw p ≠ oldSymbol old hm i := by
  exact (List.nodup_append.mp hnd).2.2 _ (label_mem controls hw p)
    _ (oldSymbol_mem old hm i)

theorem exists_labels (controls old : List Nat)
    (hw : controls.length = (d + 3) * ((d + 3) * A)) (hm : old.length = m)
    (hnd : (controls ++ old).Nodup) :
    ∃ oldMap : Fin m → Nat, ∃ physical : Physical d A → Nat,
      Function.Injective oldMap ∧ Function.Injective physical ∧
      (∀ p i, physical p ≠ oldMap i) ∧
      (List.finRange m).map oldMap = old ∧
      (∀ a, a ∈ controls ↔ ∃ p, physical p = a) ∧
      (∀ a, a ∈ old ↔ ∃ i, oldMap i = a) := by
  exact ⟨oldSymbol old hm, label controls hw,
    oldSymbol_injective old hm (List.nodup_append.mp hnd).2.1,
    label_injective controls hw (List.nodup_append.mp hnd).1,
    labels_disjoint controls old hw hm hnd, oldSymbol_word old hm,
    label_range controls hw, oldSymbol_range old hm⟩

section Background

variable (hA : 0 < A) (old : Fin m → Nat) (ho : Function.Injective old)
variable (physical : Physical d A → Nat) (hl : Function.Injective physical)
variable (hcross : ∀ p i, physical p ≠ old i)

theorem background_range (active : Active d A)
    (cuts : Fin (guardNumber d A) → Fin m) (a : Nat) :
    (∃ i, background hA old ho physical hl hcross active cuts i = a) ↔
      (∃ i, old i = a) ∨ ∃ j, physical (guardLabel d A hA active j) = a := by
  have hmem : (∃ i, background hA old ho physical hl hcross active cuts i = a) ↔
      a ∈ (List.finRange (m + guardNumber d A)).map
        (background hA old ho physical hl hcross active cuts) := by simp
  rw [hmem, background_word]
  exact mem_render old _ cuts a

theorem alphabet_support (controls oldWord : List Nat)
    (hold : ∀ a, a ∈ oldWord ↔ ∃ i, old i = a)
    (hcontrol : ∀ a, a ∈ controls ↔ ∃ p, physical p = a)
    (active : Active d A) (cuts : Fin (guardNumber d A) → Fin m) (a : Nat) :
    a ∈ controls ++ oldWord ↔
      (∃ i, background hA old ho physical hl hcross active cuts i = a) ∨
      ∃ c, physical (activeControl d A hA active c) = a := by
  rw [List.mem_append, hcontrol, hold, background_range]
  constructor
  · rintro (⟨p, hp⟩ | ho)
    · by_cases ha : p ∈ activeBlock (d + 3) A (by omega) hA active
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
        exact Or.inr ⟨i, congrArg physical hi |>.trans hp⟩
      · refine Or.inl (Or.inr ⟨guardEquiv d A hA active ⟨p, ha⟩, ?_⟩)
        simpa only [guardLabel, Equiv.symm_apply_apply] using hp
    · exact Or.inl (Or.inl ho)
  · rintro ((ho | ⟨j, hj⟩) | ⟨i, hi⟩)
    · exact Or.inr ho
    · exact Or.inl ⟨_, hj⟩
    · exact Or.inl ⟨_, hi⟩

theorem background_projection (controls oldWord : List Nat)
    (hword : (List.finRange m).map old = oldWord)
    (hkeep : ∀ i, old i ∉ controls) (hdelete : ∀ p, physical p ∈ controls)
    (active : Active d A) (cuts : Fin (guardNumber d A) → Fin m) :
    (((List.finRange (m + guardNumber d A)).map
      (background hA old ho physical hl hcross active cuts)).filter
        (fun a => decide (a ∉ controls))) = oldWord := by
  rw [background_word]
  rw [render_projection old _ cuts (fun a => decide (a ∉ controls))
    (fun j => by simp [hdelete])]
  calc
    ((List.finRange m).map old).filter (fun a => decide (a ∉ controls)) =
        (List.finRange m).map old := by
      apply List.filter_eq_self.mpr
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      simp [hkeep i]
    _ = oldWord := hword

theorem background_data (controls oldWord : List Nat) (hpositive : 0 < oldWord.length)
    (hnd : (controls ++ oldWord).Nodup)
    (hword : (List.finRange m).map old = oldWord)
    (hold : ∀ a, a ∈ oldWord ↔ ∃ i, old i = a)
    (hcontrol : ∀ a, a ∈ controls ↔ ∃ p, physical p = a)
    (active : Active d A) (cuts : Fin (guardNumber d A) → Fin m) :
    Function.Injective (background hA old ho physical hl hcross active cuts) ∧
      Function.Injective (fun c => physical (activeControl d A hA active c)) ∧
      (∀ c i, physical (activeControl d A hA active c) ≠
        background hA old ho physical hl hcross active cuts i) ∧
      (∀ a, a ∈ controls ++ oldWord ↔
        (∃ i, background hA old ho physical hl hcross active cuts i = a) ∨
        ∃ c, physical (activeControl d A hA active c) = a) ∧
      (∀ c, physical (activeControl d A hA active c) ∈ controls) ∧
      CyclicEq oldWord (((List.finRange (m + guardNumber d A)).map
        (background hA old ho physical hl hcross active cuts)).filter
          (fun a => decide (a ∉ controls))) := by
  have hdelete (p : Physical d A) : physical p ∈ controls :=
    (hcontrol _).mpr ⟨p, rfl⟩
  have hkeep (i : Fin m) : old i ∉ controls := by
    intro hi
    exact (List.nodup_append.mp hnd).2.2 _ hi _ ((hold _).mpr ⟨i, rfl⟩) rfl
  refine ⟨SameBlockCollision.background_injective hA old ho physical hl hcross active cuts,
    hl.comp (activeControl_injective d A hA active),
    active_ne_background hA old ho physical hl hcross active cuts,
    alphabet_support hA old ho physical hl hcross controls oldWord hold hcontrol active cuts,
    fun c => hdelete _, ?_⟩
  rw [background_projection hA old ho physical hl hcross controls oldWord hword hkeep hdelete]
  exact CyclicEq.refl (List.length_pos_iff.mp hpositive)

end Background

end CoefficientTwoPrecision.GridAlphabet

#print axioms CoefficientTwoPrecision.GridAlphabet.alphabet_support
#print axioms CoefficientTwoPrecision.GridAlphabet.background_projection
#print axioms CoefficientTwoPrecision.GridAlphabet.exists_labels
#print axioms CoefficientTwoPrecision.GridAlphabet.background_data
