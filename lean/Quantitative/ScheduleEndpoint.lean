import Quantitative.PositiveSchedule

/-!
# The last target fixes the literal endpoint of a positive schedule

This module retains the first stationary symbol after the last short move.
Together with returned cut and role assignments, that symbol fixes the
literal endpoint; equality of cyclic classes alone would not suffice.
-/

namespace CoefficientTwoPrecision.ScheduleEndpoint

open PositiveParking JointStates LiteralState StationaryCircle StationaryUpdate
open StationarySuccessor LiteralSchedule LiteralTrail PositiveSchedule

variable {M k : Nat} {α : Type}

/-- At a positive update endpoint, the new stationary word begins with
the old mobile, which is precisely the new resident at the last target. -/
theorem positive_update_head (pre : List α) (resident crossed mobile : α) :
    (shortStep (pre ++ [resident, crossed, mobile])).dropLast.head? = some mobile := by
  rw [(shortStep_post_update_data pre resident crossed mobile).2]
  rfl

/-- A strengthened actual schedule witness records the final target's
resident as the first stationary symbol. -/
theorem realize_targets_with_head (hM : 2 ≤ M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (hcuts : Function.Injective cuts) (gap : Nat)
    (hsafe : SafeTargets (by omega) word cuts) :
    ∃ sweeps : List Nat, ∃ finalGap : Nat,
      sweeps.length = word.length ∧
      SuffixSchedule sweeps ((render background (residents labels) cuts).rotateLeft gap ++ [labels none]) ∧
      scheduleEnd sweeps ((render background (residents labels) cuts).rotateLeft gap ++ [labels none]) =
        (render background (residents (executeLabels word labels))
          (executeCuts (by omega) word cuts)).rotateLeft finalGap ++ [executeLabels word labels none] ∧
      (∀ target, word.getLast? = some target →
        ((render background (residents (executeLabels word labels))
          (executeCuts (by omega) word cuts)).rotateLeft finalGap).head? =
            some (residents (executeLabels word labels) target)) := by
  induction word generalizing labels cuts gap with
  | nil =>
    refine ⟨[], gap, rfl, True.intro, rfl, ?_⟩
    intro target h
    simp at h
  | cons target word ih =>
    let newCuts := advanceCuts (show 0 < M by omega) target cuts
    let newLabels := updateLabels target.val labels
    obtain ⟨moves, hmoves, nextGap, pre, hpre, hstep⟩ :=
      positive_update_with_suffix hM background (residents labels) cuts hcuts target (labels none) gap hsafe.1
    have hnext : updateEnd moves
        ((render background (residents labels) cuts).rotateLeft gap ++ [labels none]) =
        (render background (residents newLabels) newCuts).rotateLeft nextGap ++ [newLabels none] := by
      simpa only [updateEnd, newLabels, newCuts, updateLabels_residents,
        updateLabels_mobile, advanceCuts] using hstep
    have hnewCuts : Function.Injective newCuts :=
      moveCut_injective cuts hcuts target _ hsafe.1
    obtain ⟨sweeps, finalGap, hlength, hvalid, hend, hhead⟩ :=
      ih newLabels newCuts hnewCuts nextGap hsafe.2
    refine ⟨moves :: sweeps, finalGap, by simp [hlength], ?_, ?_, ?_⟩
    · refine ⟨⟨(render background (residents labels) cuts).rotateLeft gap,
        labels none, rfl, ?_⟩, ?_, ?_⟩
      · have hlen := render_length_ge_background background (residents labels) cuts
        rw [LiteralState.rotateLeft_eq_rotate, List.length_rotate]
        omega
      · exact ⟨pre, residents labels target, background (cuts target), labels none, hpre⟩
      · rw [hnext]
        exact hvalid
    · change scheduleEnd sweeps (updateEnd moves _) = _
      rw [hnext]
      exact hend
    · intro last hlast
      cases word with
      | nil =>
        have hlastEq : last = target := by simpa using hlast.symm
        subst last
        have hsweeps : sweeps = [] := by
          apply List.length_eq_zero_iff.mp
          simpa using hlength
        subst sweeps
        have hfinal :
            (render background (residents newLabels) newCuts).rotateLeft nextGap ++ [newLabels none] =
            (render background (residents newLabels) newCuts).rotateLeft finalGap ++ [newLabels none] := hend
        have hrot : (render background (residents newLabels) newCuts).rotateLeft nextGap =
            (render background (residents newLabels) newCuts).rotateLeft finalGap :=
          List.append_cancel_right hfinal
        have hshortHead := positive_update_head pre (residents labels target)
          (background (cuts target)) (labels none)
        have hendpoint : shortStep (pre ++ [residents labels target, background (cuts target), labels none]) =
            (render background (residents newLabels) newCuts).rotateLeft nextGap ++ [newLabels none] := by
          simpa only [updateEnd, hpre] using hnext
        rw [hendpoint, List.dropLast_concat, hrot] at hshortHead
        simpa only [executeLabels, executeCuts, newLabels, newCuts, residents,
          updateLabels, star_target] using hshortHead
      | cons next tail =>
        apply hhead last
        simpa using hlast

end CoefficientTwoPrecision.ScheduleEndpoint

#print axioms CoefficientTwoPrecision.ScheduleEndpoint.positive_update_head
#print axioms CoefficientTwoPrecision.ScheduleEndpoint.realize_targets_with_head
