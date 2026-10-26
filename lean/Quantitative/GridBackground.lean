import Quantitative.GuardCatalogue
import Quantitative.ActualMatching

/-!
# Concrete grid-labelled backgrounds and active controls

The finite background map is obtained by indexing the actual guard-rendered
list. Its length and word equality are proved, rather than supplied as
certificate fields. Active and guard labels are separated by membership
in the fixed active grid block. A role bijection also gives the exact
permutation between physical nonmobile rows and stationary slot indices.
-/

namespace CoefficientTwoPrecision.GridBackground

open ActiveGrid GuardCatalogue GuardBackgrounds StationaryCircle StationaryUpdate

variable {m d A : Nat} {α : Type} [DecidableEq α]

def activeControl (d A : Nat) (hA : 0 < A) (active : Active d A) : Fin (d + 3) → Physical d A :=
  controlAt (d + 3) A (by omega) hA active

theorem activeControl_injective (d A : Nat) (hA : 0 < A) (active : Active d A) :
    Function.Injective (activeControl d A hA active) := by
  intro i j h
  exact congrArg Prod.fst h

theorem activeControl_mem (d A : Nat) (hA : 0 < A) (active : Active d A) (i : Fin (d + 3)) :
    activeControl d A hA active i ∈ activeBlock (d + 3) A (by omega) hA active :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem guardLabel_not_mem (d A : Nat) (hA : 0 < A) (active : Active d A)
    (j : Fin (guardNumber d A)) :
    guardLabel d A hA active j ∉ activeBlock (d + 3) A (by omega) hA active :=
  ((guardEquiv d A hA active).symm j).property

theorem activeControl_ne_guardLabel (d A : Nat) (hA : 0 < A) (active : Active d A)
    (i : Fin (d + 3)) (j : Fin (guardNumber d A)) :
    activeControl d A hA active i ≠ guardLabel d A hA active j := by
  intro h
  exact guardLabel_not_mem d A hA active j (h ▸ activeControl_mem d A hA active i)

noncomputable def guardWord (hA : 0 < A) (old : Fin m → α) (label : Physical d A → α)
    (active : Active d A) (cuts : Fin (guardNumber d A) → Fin m) : List α :=
  render old (fun j => label (guardLabel d A hA active j)) cuts

theorem guardWord_length (hA : 0 < A) (old : Fin m → α) (ho : Function.Injective old)
    (label : Physical d A → α) (hl : Function.Injective label)
    (hcross : ∀ p i, label p ≠ old i)
    (active : Active d A) (cuts : Fin (guardNumber d A) → Fin m) :
    (guardWord hA old label active cuts).length = m + guardNumber d A :=
  render_length old _ cuts ho (hl.comp (guardLabel_injective d A hA active)) (fun j i => hcross _ i)

noncomputable def background (hA : 0 < A) (old : Fin m → α) (ho : Function.Injective old)
    (label : Physical d A → α) (hl : Function.Injective label)
    (hcross : ∀ p i, label p ≠ old i)
    (active : Active d A) (cuts : Fin (guardNumber d A) → Fin m)
    (i : Fin (m + guardNumber d A)) : α :=
  (guardWord hA old label active cuts)[i.val]'(by
    rw [guardWord_length hA old ho label hl hcross active cuts]
    exact i.isLt)

theorem background_word (hA : 0 < A) (old : Fin m → α) (ho : Function.Injective old)
    (label : Physical d A → α) (hl : Function.Injective label)
    (hcross : ∀ p i, label p ≠ old i)
    (active : Active d A) (cuts : Fin (guardNumber d A) → Fin m) :
    (List.finRange (m + guardNumber d A)).map (background hA old ho label hl hcross active cuts) =
      render old (fun j => label (guardLabel d A hA active j)) cuts := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange]
    exact (guardWord_length hA old ho label hl hcross active cuts).symm
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_finRange, background, Fin.val_mk, Fin.val_cast,
      guardWord]

theorem active_ne_background (hA : 0 < A) (old : Fin m → α) (ho : Function.Injective old)
    (label : Physical d A → α) (hl : Function.Injective label)
    (hcross : ∀ p i, label p ≠ old i)
    (active : Active d A) (cuts : Fin (guardNumber d A) → Fin m)
    (p : Fin (d + 3)) (i : Fin (m + guardNumber d A)) :
    label (activeControl d A hA active p) ≠ background hA old ho label hl hcross active cuts i := by
  intro he
  have hmem : background hA old ho label hl hcross active cuts i ∈
      guardWord hA old label active cuts := List.getElem_mem _
  have hm : label (activeControl d A hA active p) ∈ guardWord hA old label active cuts :=
    he.symm ▸ hmem
  rcases (mem_render old (fun j => label (guardLabel d A hA active j)) cuts _).mp hm with
    ⟨j, hj⟩ | ⟨j, hj⟩
  · exact hcross _ j hj.symm
  · exact activeControl_ne_guardLabel d A hA active p j (hl hj).symm

/-- The canonical one-control projection predicate is determined solely
by the common old alphabet and the retained physical control. -/
theorem keep_physical (old : Fin m → α) (label : Physical d A → α)
    (hl : Function.Injective label) (hcross : ∀ p i, label p ≠ old i)
    (tracked p : Physical d A) :
    keepGuard old (label tracked) (label p) = decide (p = tracked) := by
  have hnone : ¬ ∃ i, old i = label p := by
    rintro ⟨i, hi⟩
    exact hcross p i hi.symm
  simp only [keepGuard, hnone, or_false, hl.eq_iff]

theorem slotEquiv_exists (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3)) :
    ∃ slots : Fin (d + 2) ≃ Fin (d + 2),
      ∀ i, role (some (slots i)) = (role none).succAbove i := by
  have hslot (i : Fin (d + 2)) : ∃ slot : Fin (d + 2),
      role (some slot) = (role none).succAbove i := by
    have he := role.apply_symm_apply ((role none).succAbove i)
    cases hv : role.symm ((role none).succAbove i) with
    | none =>
      rw [hv] at he
      exact False.elim (Fin.succAbove_ne (role none) i he.symm)
    | some slot =>
      exact ⟨slot, by rwa [hv] at he⟩
  choose f hf using hslot
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.succAbove_right_injective (p := role none)
    rw [← hf i, ← hf j, hij]
  let slots := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  exact ⟨slots, hf⟩

end CoefficientTwoPrecision.GridBackground

#print axioms CoefficientTwoPrecision.GridBackground.background_word
#print axioms CoefficientTwoPrecision.GridBackground.active_ne_background
#print axioms CoefficientTwoPrecision.GridBackground.slotEquiv_exists
