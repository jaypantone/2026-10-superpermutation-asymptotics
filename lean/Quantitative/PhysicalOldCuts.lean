import Quantitative.GridBackground
import Quantitative.OldCircleProjection

/-!
# Automatic original-cut projections for physical grid rows

The canonical one-control predicates below require no filter table as an
input. Membership in the active block separates its controls from guards,
and the role bijection separates the resident controls and mobile. Equal
cyclic rows therefore identify a common original cut for shared residents,
or identify a resident's original cut with a named guard's prescribed cut.
-/

namespace CoefficientTwoPrecision.PhysicalOldCuts

open GuardCatalogue GridBackground GuardBackgrounds GuardCoordinates OldCircleProjection
open StationaryCircle

variable {m d A : Nat} {α : Type} [DecidableEq α]
variable (hA : 0 < A) (old : Fin m → α) (ho : Function.Injective old)
variable (label : Physical d A → α) (hl : Function.Injective label)
variable (hcross : ∀ p i, label p ≠ old i)

def residentControl (active : Active d A)
    (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3)) (j : Fin (d + 2)) : Physical d A :=
  activeControl d A hA active (role (some j))

noncomputable def rowBase (active : Active d A)
    (guardCuts : Fin (guardNumber d A) → Fin m)
    (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localCuts : Fin (d + 2) → Fin (m + guardNumber d A)) (gap : Nat) : List α :=
  ActualMatching.base (background hA old ho label hl hcross active guardCuts)
    (fun row => label (activeControl d A hA active row)) role localCuts gap

theorem resident_projection (active : Active d A)
    (guardCuts : Fin (guardNumber d A) → Fin m)
    (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localCuts : Fin (d + 2) → Fin (m + guardNumber d A)) (gap : Nat) (target : Fin (d + 2)) :
    ∃ cut : Fin m, ∃ offset : Nat,
      offset < (block old (fun j => label (guardLabel d A hA active j)) guardCuts cut).length ∧
      (localCuts target).val = blockStart old (fun j => label (guardLabel d A hA active j)) guardCuts cut + offset ∧
      ((rowBase hA old ho label hl hcross active guardCuts role localCuts gap).filter
        (keepGuard old (label (residentControl hA active role target)))).IsRotated
          (SuperpermutationUpperBound.Transport.insertLetter ((List.finRange m).map old)
            (label (residentControl hA active role target)) cut.val) := by
  let embed := fun row => label (activeControl d A hA active row)
  let keep := keepGuard old (label (residentControl hA active role target))
  have hkeep (p : Physical d A) : keep (label p) = decide (p = residentControl hA active role target) :=
    keep_physical old label hl hcross _ p
  have hguard (j : Fin (guardNumber d A)) : keep (label (guardLabel d A hA active j)) = false := by
    rw [hkeep]
    exact decide_eq_false_iff_not.mpr (activeControl_ne_guardLabel d A hA active (role (some target)) j).symm
  have hresident (j : Fin (d + 2)) :
      keep (ActualMatching.resident embed role j) = decide (j = target) := by
    change keep (label (activeControl d A hA active (role (some j)))) = _
    rw [hkeep]
    simp only [residentControl, (activeControl_injective d A hA active).eq_iff,
      role.injective.eq_iff, Option.some.injEq]
  have hmobile : keep (embed (role none)) = false := by
    change keep (label (activeControl d A hA active (role none))) = false
    rw [hkeep]
    simp only [residentControl, (activeControl_injective d A hA active).eq_iff,
      role.injective.eq_iff, reduceCtorEq, decide_false]
  exact OldCircleProjection.resident_mobile_projection old _ guardCuts
    (background hA old ho label hl hcross active guardCuts)
    (background_word hA old ho label hl hcross active guardCuts)
    (ActualMatching.resident embed role)
    (ActualMatching.resident_injective embed (hl.comp (activeControl_injective d A hA active)) role)
    (fun j i => active_ne_background hA old ho label hl hcross active guardCuts (role (some j)) i)
    localCuts target (embed (role none)) gap keep (keepGuard_old old _) hguard hresident hmobile

theorem guard_projection (active : Active d A)
    (guardCuts : Fin (guardNumber d A) → Fin m)
    (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localCuts : Fin (d + 2) → Fin (m + guardNumber d A)) (gap : Nat)
    (target : Fin (guardNumber d A)) :
    ((rowBase hA old ho label hl hcross active guardCuts role localCuts gap).filter
      (keepGuard old (label (guardLabel d A hA active target)))).IsRotated
        (SuperpermutationUpperBound.Transport.insertLetter ((List.finRange m).map old)
          (label (guardLabel d A hA active target)) (guardCuts target).val) := by
  let embed := fun row => label (activeControl d A hA active row)
  let guard := fun j => label (guardLabel d A hA active j)
  let keep := keepGuard old (guard target)
  have hkeep (p : Physical d A) : keep (label p) = decide (p = guardLabel d A hA active target) :=
    keep_physical old label hl hcross _ p
  have hresident (j : Fin (d + 2)) : keep (ActualMatching.resident embed role j) = false := by
    change keep (label (activeControl d A hA active (role (some j)))) = false
    rw [hkeep]
    exact decide_eq_false_iff_not.mpr (activeControl_ne_guardLabel d A hA active (role (some j)) target)
  have hmobile : keep (embed (role none)) = false := by
    change keep (label (activeControl d A hA active (role none))) = false
    rw [hkeep]
    exact decide_eq_false_iff_not.mpr (activeControl_ne_guardLabel d A hA active (role none) target)
  exact OldCircleProjection.guard_mobile_projection old guard guardCuts
    (background hA old ho label hl hcross active guardCuts)
    (background_word hA old ho label hl hcross active guardCuts)
    (ActualMatching.resident embed role) localCuts target (embed (role none)) gap keep
    (keepGuard_old old _) (keepGuard_guard old guard
      (hl.comp (guardLabel_injective d A hA active)) (fun j i => hcross _ i) target)
    hresident hmobile

theorem resident_guard_offset (active foreign : Active d A)
    (guardCutsL guardCutsR : Fin (guardNumber d A) → Fin m)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (guardTarget : Fin (guardNumber d A)) (residentTarget : Fin (d + 2))
    (htracked : guardLabel d A hA active guardTarget = residentControl hA foreign roleR residentTarget)
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign guardCutsR roleR localR gapR)) :
    ∃ e ≤ guardNumber d A,
      (localR residentTarget).val = (guardCutsL guardTarget).val + e := by
  have hleft := guard_projection hA old ho label hl hcross active guardCutsL roleL localL gapL guardTarget
  obtain ⟨cut, offset, hoff, hpos, hright⟩ := resident_projection hA old ho label hl hcross
    foreign guardCutsR roleR localR gapR residentTarget
  rw [htracked] at hleft
  have hcut := same_old_cut old ho (label (residentControl hA foreign roleR residentTarget))
    (hcross _) _ _ _ hcyclic (guardCutsL guardTarget) cut hleft hright
  obtain ⟨e, he, hcoordinate⟩ := coordinate_offset old _ guardCutsR ho
    (hl.comp (guardLabel_injective d A hA foreign)) (fun j i => hcross _ i) cut offset hoff
  exact ⟨e, he, by simpa only [← hcut] using hpos.trans hcoordinate⟩

theorem common_resident_offsets (active foreign : Active d A)
    (guardCutsL guardCutsR : Fin (guardNumber d A) → Fin m)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (targetL targetR : Fin (d + 2))
    (htracked : residentControl hA active roleL targetL = residentControl hA foreign roleR targetR)
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign guardCutsR roleR localR gapR)) :
    ∃ cut : Fin m, ∃ eL ≤ guardNumber d A, ∃ eR ≤ guardNumber d A,
      (localL targetL).val = cut.val + eL ∧ (localR targetR).val = cut.val + eR := by
  obtain ⟨cutL, offsetL, hoffL, hposL, hleft⟩ := resident_projection hA old ho label hl hcross
    active guardCutsL roleL localL gapL targetL
  obtain ⟨cutR, offsetR, hoffR, hposR, hright⟩ := resident_projection hA old ho label hl hcross
    foreign guardCutsR roleR localR gapR targetR
  rw [htracked] at hleft
  have hcut := same_old_cut old ho (label (residentControl hA foreign roleR targetR))
    (hcross _) _ _ _ hcyclic cutL cutR hleft hright
  obtain ⟨eL, heL, hcoordL⟩ := coordinate_offset old _ guardCutsL ho
    (hl.comp (guardLabel_injective d A hA active)) (fun j i => hcross _ i) cutL offsetL hoffL
  obtain ⟨eR, heR, hcoordR⟩ := coordinate_offset old _ guardCutsR ho
    (hl.comp (guardLabel_injective d A hA foreign)) (fun j i => hcross _ i) cutR offsetR hoffR
  exact ⟨cutL, eL, heL, eR, heR, hposL.trans hcoordL,
    by simpa only [← hcut] using hposR.trans hcoordR⟩

end CoefficientTwoPrecision.PhysicalOldCuts

#print axioms CoefficientTwoPrecision.PhysicalOldCuts.resident_guard_offset
#print axioms CoefficientTwoPrecision.PhysicalOldCuts.common_resident_offsets
