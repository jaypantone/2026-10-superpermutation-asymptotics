import Quantitative.OldCirclePrefix
import Quantitative.CutExtraction

/-!
# Literal old-circle projections of full source rows

For a stationary resident, first delete the other residents and then the
background guards. The retained control is inserted at the original old
cut recovered from its own background. A guard of another candidate has
the analogous projection at its prescribed guard cut. Equality of full
cyclic rows identifies these cuts even when the two backgrounds differ.
-/

namespace CoefficientTwoPrecision.OldCircleProjection

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open LiteralState StationaryCircle StationaryUpdate GuardBackgrounds GuardCoordinates GuardPositions
open OldCirclePrefix CutExtraction

variable {m G M k : Nat} {α : Type} [DecidableEq α]

/-- Keeping one resident and any subset of the background is the same as
filtering its literal single insertion into that background. -/
theorem single_resident_filter (background : Fin M → α) (resident : Fin k → α)
    (hresident : Function.Injective resident)
    (hcross : ∀ j i, resident j ≠ background i)
    (cuts : Fin k → Fin M) (target : Fin k) (keep : α → Bool)
    (hkeep : ∀ j, keep (resident j) = decide (j = target)) :
    (render background resident cuts).filter keep =
      (insertLetter ((List.finRange M).map background) (resident target) (cuts target).val).filter keep := by
  let keepAll := keepGuard background (resident target)
  have hAllBackground := keepGuard_old background (resident target)
  have hAllResident := keepGuard_guard background resident hresident hcross target
  have hfirst := filter_single_guard background resident cuts target keepAll hAllBackground hAllResident
  have habsorb : ((render background resident cuts).filter keepAll).filter keep =
      (render background resident cuts).filter keep := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro a ha
    rcases (mem_render background resident cuts a).mp ha with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · simp only [keepAll, hAllBackground, Bool.true_and, Bool.and_true]
    · simp only [keepAll, hAllResident, hkeep, Bool.and_self]
  exact habsorb.symm.trans (congrArg (List.filter keep) hfirst)

theorem all_residents_filter (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (keep : α → Bool) (hresident : ∀ j, keep (resident j) = false) :
    (render background resident cuts).filter keep = ((List.finRange M).map background).filter keep := by
  have hcontrols (cut : Fin M) : ((controlsAt cuts cut).map resident).filter keep = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    simp [hresident j]
  have hblock (cut : Fin M) :
      (block background resident cuts cut).filter keep = [background cut].filter keep := by
    simp only [block, List.filter_append, hcontrols, List.nil_append]
  rw [render, List.filter_flatMap]
  simp only [hblock]
  rw [List.map_eq_flatMap, List.filter_flatMap]

theorem mobile_projection (stationary : List α) (mobile : α) (gap : Nat)
    (keep : α → Bool) (hmobile : keep mobile = false) :
    ((stationary.rotateLeft gap ++ [mobile]).filter keep).IsRotated (stationary.filter keep) := by
  have h := (filter_rotate stationary keep gap).symm
  simpa [List.filter_append, hmobile, LiteralState.rotateLeft_eq_rotate] using h

/-- A retained resident is projected using its own background's local
cut, with the original old-cut block exhibited explicitly. -/
theorem resident_projection (old : Fin m → α) (guard : Fin G → α)
    (guardCuts : Fin G → Fin m) (background : Fin M → α)
    (hbackground : (List.finRange M).map background = render old guard guardCuts)
    (resident : Fin k → α) (hresident : Function.Injective resident)
    (hcross : ∀ j i, resident j ≠ background i)
    (cuts : Fin k → Fin M) (target : Fin k) (keep : α → Bool)
    (hold : ∀ i, keep (old i) = true) (hguard : ∀ j, keep (guard j) = false)
    (hkeep : ∀ j, keep (resident j) = decide (j = target)) :
    ∃ cut : Fin m, ∃ offset : Nat,
      offset < (block old guard guardCuts cut).length ∧
      (cuts target).val = blockStart old guard guardCuts cut + offset ∧
      (render background resident cuts).filter keep =
        insertLetter ((List.finRange m).map old) (resident target) cut.val := by
  have hlength : M = (render old guard guardCuts).length := by
    simpa using congrArg List.length hbackground
  have hp : (cuts target).val < (render old guard guardCuts).length := by
    rw [← hlength]
    exact (cuts target).isLt
  obtain ⟨cut, offset, hoff, hpos⟩ := position_has_cut old guard guardCuts (cuts target).val hp
  have hfirst := single_resident_filter background resident hresident hcross cuts target keep hkeep
  rw [hbackground, hpos] at hfirst
  have htracked : keep (resident target) = true := by simpa using hkeep target
  exact ⟨cut, offset, hoff, hpos, hfirst.trans
    (insertion_filter old guard guardCuts keep hold hguard (resident target) htracked cut offset hoff)⟩

theorem resident_mobile_projection (old : Fin m → α) (guard : Fin G → α)
    (guardCuts : Fin G → Fin m) (background : Fin M → α)
    (hbackground : (List.finRange M).map background = render old guard guardCuts)
    (resident : Fin k → α) (hresident : Function.Injective resident)
    (hcross : ∀ j i, resident j ≠ background i)
    (cuts : Fin k → Fin M) (target : Fin k) (mobile : α) (gap : Nat) (keep : α → Bool)
    (hold : ∀ i, keep (old i) = true) (hguard : ∀ j, keep (guard j) = false)
    (hkeep : ∀ j, keep (resident j) = decide (j = target)) (hmobile : keep mobile = false) :
    ∃ cut : Fin m, ∃ offset : Nat,
      offset < (block old guard guardCuts cut).length ∧
      (cuts target).val = blockStart old guard guardCuts cut + offset ∧
      (((render background resident cuts).rotateLeft gap ++ [mobile]).filter keep).IsRotated
        (insertLetter ((List.finRange m).map old) (resident target) cut.val) := by
  obtain ⟨cut, offset, hoff, hpos, hprojection⟩ := resident_projection old guard guardCuts
    background hbackground resident hresident hcross cuts target keep hold hguard hkeep
  have h := mobile_projection (render background resident cuts) mobile gap keep hmobile
  rw [hprojection] at h
  exact ⟨cut, offset, hoff, hpos, h⟩

/-- A retained background guard projects to its prescribed old cut after
all active residents and the current mobile are deleted. -/
theorem guard_mobile_projection (old : Fin m → α) (guard : Fin G → α)
    (guardCuts : Fin G → Fin m) (background : Fin M → α)
    (hbackground : (List.finRange M).map background = render old guard guardCuts)
    (resident : Fin k → α) (cuts : Fin k → Fin M) (target : Fin G)
    (mobile : α) (gap : Nat) (keep : α → Bool)
    (hold : ∀ i, keep (old i) = true)
    (hguard : ∀ j, keep (guard j) = decide (j = target))
    (hresident : ∀ j, keep (resident j) = false) (hmobile : keep mobile = false) :
    (((render background resident cuts).rotateLeft gap ++ [mobile]).filter keep).IsRotated
      (insertLetter ((List.finRange m).map old) (guard target) (guardCuts target).val) := by
  have hfirst := all_residents_filter background resident cuts keep hresident
  rw [hbackground, filter_single_guard old guard guardCuts target keep hold hguard] at hfirst
  have h := mobile_projection (render background resident cuts) mobile gap keep hmobile
  rwa [hfirst] at h

private theorem cyclicEq_of_isRotated {a b : List α} (ha : 0 < a.length)
    (hab : a.IsRotated b) : CyclicEq a b := by
  obtain ⟨n, hn⟩ := hab
  refine ⟨⟨n % a.length, Nat.mod_lt _ ha⟩, ?_⟩
  change rot a (n % a.length) = b
  rw [rot_mod]
  change a.rotateLeft n = b
  rw [LiteralState.rotateLeft_eq_rotate]
  exact hn

/-- Full cyclic equality identifies the projected old cuts, without
requiring the two local guard backgrounds or mobiles to agree. -/
theorem same_old_cut (old : Fin m → α) (ho : Function.Injective old)
    (tracked : α) (hfresh : ∀ i, tracked ≠ old i) (keep : α → Bool)
    (first second : List α) (hcyclic : first.IsRotated second) (left right : Fin m)
    (hleft : (first.filter keep).IsRotated
      (insertLetter ((List.finRange m).map old) tracked left.val))
    (hright : (second.filter keep).IsRotated
      (insertLetter ((List.finRange m).map old) tracked right.val)) : left = right := by
  have hrot := hleft.symm.trans ((filter_isRotated first second keep hcyclic).trans hright)
  have hcyc := cyclicEq_of_isRotated (by simp :
    0 < (insertLetter ((List.finRange m).map old) tracked left.val).length) hrot
  have hnd : ((List.finRange m).map old).Nodup := (List.nodup_finRange m).map ho
  have hnot : tracked ∉ (List.finRange m).map old := by
    intro hmem
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hmem
    exact hfresh i he.symm
  apply Fin.ext
  exact (insertLetter_cyclicEq_iff_index_eq hnd hnot
    (by simpa using left.isLt) (by simpa using right.isLt)).mp hcyc

end CoefficientTwoPrecision.OldCircleProjection

#print axioms CoefficientTwoPrecision.OldCircleProjection.resident_mobile_projection
#print axioms CoefficientTwoPrecision.OldCircleProjection.guard_mobile_projection
#print axioms CoefficientTwoPrecision.OldCircleProjection.same_old_cut
