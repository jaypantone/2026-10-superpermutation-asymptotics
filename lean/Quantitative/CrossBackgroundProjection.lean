import Quantitative.OldCircleProjection
import Quantitative.GuardEvents

/-!
# Original-cut identification across different guard backgrounds

The retained symbol is a guard in the first row and a stationary resident
in the second. Both rows are actual rendered mobile bases. Filtering their
full cyclic equality identifies its two original old-circle insertions.
The local coordinate used below is the second row's own background cut.
-/

namespace CoefficientTwoPrecision.CrossBackgroundProjection

open StationaryCircle GuardCoordinates GuardEvents OldCircleProjection

variable {m leftGuards rightGuards ML MR kL kR : Nat} {α : Type} [DecidableEq α]

theorem resident_guard_offset
    (old : Fin m → α) (ho : Function.Injective old)
    (guardL : Fin leftGuards → α) (guardCutsL : Fin leftGuards → Fin m)
    (backgroundL : Fin ML → α)
    (hbackgroundL : (List.finRange ML).map backgroundL = render old guardL guardCutsL)
    (residentL : Fin kL → α) (cutsL : Fin kL → Fin ML) (mobileL : α) (gapL : Nat)
    (guardR : Fin rightGuards → α) (guardCutsR : Fin rightGuards → Fin m)
    (hgR : Function.Injective guardR) (hguardOldR : ∀ j i, guardR j ≠ old i)
    (backgroundR : Fin MR → α)
    (hbackgroundR : (List.finRange MR).map backgroundR = render old guardR guardCutsR)
    (residentR : Fin kR → α) (hrR : Function.Injective residentR)
    (hresidentBackgroundR : ∀ j i, residentR j ≠ backgroundR i)
    (cutsR : Fin kR → Fin MR) (mobileR : α) (gapR : Nat)
    (guardTarget : Fin leftGuards) (residentTarget : Fin kR)
    (htracked : residentR residentTarget = guardL guardTarget)
    (hfresh : ∀ i, guardL guardTarget ≠ old i)
    (keep : α → Bool) (hold : ∀ i, keep (old i) = true)
    (hguardL : ∀ j, keep (guardL j) = decide (j = guardTarget))
    (hresidentL : ∀ j, keep (residentL j) = false) (hmobileL : keep mobileL = false)
    (hguardR : ∀ j, keep (guardR j) = false)
    (hresidentR : ∀ j, keep (residentR j) = decide (j = residentTarget))
    (hmobileR : keep mobileR = false)
    (hcyclic : ((render backgroundL residentL cutsL).rotateLeft gapL ++ [mobileL]).IsRotated
      ((render backgroundR residentR cutsR).rotateLeft gapR ++ [mobileR])) :
    ∃ e ≤ rightGuards, (cutsR residentTarget).val = (guardCutsL guardTarget).val + e := by
  have hleft := guard_mobile_projection old guardL guardCutsL backgroundL hbackgroundL
    residentL cutsL guardTarget mobileL gapL keep hold hguardL hresidentL hmobileL
  obtain ⟨cut, offset, hoff, hpos, hright⟩ := resident_mobile_projection old guardR guardCutsR
    backgroundR hbackgroundR residentR hrR hresidentBackgroundR cutsR residentTarget
    mobileR gapR keep hold hguardR hresidentR hmobileR
  rw [htracked] at hright
  have hcut := same_old_cut old ho (guardL guardTarget) hfresh keep _ _ hcyclic
    (guardCutsL guardTarget) cut hleft hright
  obtain ⟨e, he, hcoordinate⟩ := coordinate_offset old guardR guardCutsR ho hgR hguardOldR
    cut offset hoff
  exact ⟨e, he, by simpa only [← hcut] using hpos.trans hcoordinate⟩

/-- Once actual cyclic rows identify the old cuts, the foreign relation
is a congruence in the first candidate's prescribed guard variables. -/
theorem foreign_relation_of_offsets {G d : Nat}
    (hm : 0 < m) (hd : 2 ≤ d) (assignment : StationaryRelations.Assignment d)
    (currentGuardCuts : Fin G → Fin m) (index : Fin (d + 2) → Fin G)
    (foreignLocalCuts : Fin (d + 2) → Fin (m + G))
    (hoffset : ∀ i, ∃ e ≤ G,
      (foreignLocalCuts i).val = (currentGuardCuts (index i)).val + e)
    (q : Fin (d + 2) → Int) (phase : Fin (d + 2) → Fin 2) (t : Int)
    (hq : Int.ModEq ((m + G : Nat) : Int)
      (∑ i, StationaryRelations.weight assignment i * q i) 0)
    (hlocal : ∀ i, Int.ModEq ((m + G : Nat) : Int) (foreignLocalCuts i).val
      (q i + t + (phase i).val)) :
    ∃ b : Int, b.natAbs ≤ stationaryOffsetBound d G ∧
      Int.ModEq (m : Int)
        (∑ i, StationaryRelations.weight assignment i * (currentGuardCuts (index i)).val) b := by
  choose e he hxe using hoffset
  have hsum := StationaryRelations.weight_abs_sum hd assignment
  have hphase (i : Fin (d + 2)) :
      0 ≤ ((phase i).val : Int) ∧ ((phase i).val : Int) ≤ 1 := by
    have hi := (phase i).isLt
    omega
  have hframe := frame_relation ((m + G : Nat) : Int) t
    (StationaryRelations.weight assignment) q (fun i => ((phase i).val : Int))
    (fun i => ((foreignLocalCuts i).val : Int))
    (StationaryRelations.weight_sum assignment) hq hlocal
  obtain ⟨ell, hell, hrel⟩ := bounded_winding (m + G) (2 * d) (by omega)
    (StationaryRelations.weight assignment) (fun i => ((foreignLocalCuts i).val : Int))
    (fun i => ((phase i).val : Int)) hsum
    (fun i => by have hi := (foreignLocalCuts i).isLt; omega) hphase hframe
  have hph := weighted_abs_bound (StationaryRelations.weight assignment)
    (fun i => ((phase i).val : Int)) 1 (fun i => by have hi := hphase i; omega)
  rw [hsum, Nat.mul_one] at hph
  exact old_relation_of_offsets m G d (StationaryRelations.weight assignment)
    (fun i => ((currentGuardCuts (index i)).val : Int)) (fun i => (e i : Int))
    (fun i => ((foreignLocalCuts i).val : Int)) ell
    (∑ i, StationaryRelations.weight assignment i * (phase i).val) hsum
    (fun i => by simpa only [Int.natAbs_natCast] using he i)
    (fun i => by exact_mod_cast hxe i) (by omega) hph (by simpa only [Nat.cast_add] using hrel)

end CoefficientTwoPrecision.CrossBackgroundProjection

#print axioms CoefficientTwoPrecision.CrossBackgroundProjection.resident_guard_offset
#print axioms CoefficientTwoPrecision.CrossBackgroundProjection.foreign_relation_of_offsets
