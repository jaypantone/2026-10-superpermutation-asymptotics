import Quantitative.ClosedPositive
import Quantitative.LiteralEnvelope

/-!
# One constructed witness carries closure and literal containment

The bounded trace, endpoint equality, original ClosedTrail, and catalogue
containment below refer to the same actual sweep lengths and row list.
No separate existential constructions are silently identified.
-/

namespace CoefficientTwoPrecision.ClosedTrace

open JointStates LiteralState StationaryCircle StationaryUpdate StationarySuccessor
open LiteralSchedule LiteralTrail PositiveSchedule ScheduleEndpoint ClosedPositive
open RobustMatching BatchSafety TargetTrace LiteralEnvelope MacroCatalogue
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type}

theorem trace_last_head (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace hM background word labels cuts gap sweeps finalGap)
    (target : Fin k) (hlast : word.getLast? = some target) :
    ((render background (residents (executeLabels word labels))
      (executeCuts hM word cuts)).rotateLeft finalGap).head? =
        some (residents (executeLabels word labels) target) := by
  induction word generalizing labels cuts gap sweeps with
  | nil => simp at hlast
  | cons first word ih =>
    obtain ⟨moves, rest, nextGap, pre, rfl, _, hpre, hnext, hrest⟩ := htrace
    cases word with
    | nil =>
      obtain ⟨rfl, rfl⟩ := hrest
      have htarget : target = first := by simpa using hlast.symm
      subst target
      have hhead := positive_update_head pre (residents labels first)
        (background (cuts first)) (labels none)
      have hendpoint :
          shortStep (pre ++ [residents labels first, background (cuts first), labels none]) =
          renderedBase background (PositiveParking.updateLabels first.val labels)
            (advanceCuts hM first cuts) finalGap := by
        simpa only [updateEnd, hpre] using hnext
      rw [hendpoint, renderedBase, List.dropLast_concat] at hhead
      simpa only [executeLabels, executeCuts, residents, PositiveParking.updateLabels,
        PositiveParking.star_target] using hhead
    | cons next tail =>
      apply ih (PositiveParking.updateLabels first.val labels) (advanceCuts hM first cuts)
        nextGap rest hrest
      simpa using hlast

/-- Robust complete batches with returned role/count data give a single
literally closed bounded trace. -/
theorem closed_complete_trace (hM : 2 ≤ M) (background : Fin M → α)
    (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (hbackground : Function.Injective background)
    (hresident : Function.Injective (residents (k := k) labels))
    (hcross : ∀ (j : Fin k) (i : Fin M), residents labels j ≠ background i)
    (hrobust : Robust (fun j => cutValue (cuts j)))
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (hcounts : ∀ j, batches.flatten.count j = M)
    (hlabels : executeLabels batches.flatten labels = labels)
    (lastTarget : Fin k) (hlast : batches.flatten.getLast? = some lastTarget)
    (satellite : α) :
    ∃ gap sweeps finalGap,
      Trace (by omega) background batches.flatten labels cuts gap sweeps finalGap ∧
      scheduleEnd sweeps (renderedBase background labels cuts gap) =
        renderedBase background labels cuts gap ∧
      ClosedTrail (scheduleRows satellite sweeps (renderedBase background labels cuts gap)) := by
  have hcuts : Function.Injective cuts := by
    intro i j hij
    apply robust_injective _ hrobust
    exact congrArg cutValue hij
  have hrep : Represents (fun j => cutValue (cuts j)) 0 (fun _ => false) cuts := by
    intro j
    simp [RobustSafety.perturbed, bit]
  have hsafe := complete_batches_safe hM (fun j => cutValue (cuts j)) hrobust
    batches horders 0 cuts hrep
  obtain ⟨gap, hgap⟩ := initial_gap_exists background (residents labels) cuts lastTarget
  obtain ⟨sweeps, finalGap, htrace⟩ := exists_trace hM background batches.flatten labels cuts hcuts gap hsafe
  have hlength := trace_length (show 0 < M by omega) background batches.flatten labels cuts gap
    sweeps finalGap htrace
  have hvalid := trace_suffixSchedule hM background batches.flatten labels cuts gap sweeps finalGap htrace
  have hend := trace_endpoint (show 0 < M by omega) background batches.flatten labels cuts gap
    sweeps finalGap htrace
  have hhead := trace_last_head (show 0 < M by omega) background batches.flatten labels cuts gap
    sweeps finalGap htrace lastTarget hlast
  have hcutReturn := executeCuts_closed (show 0 < M by omega) batches.flatten cuts hcounts
  have hfinalHead : ((render background (residents labels) cuts).rotateLeft finalGap).head? =
      some (residents labels lastTarget) := by
    simpa only [hlabels, hcutReturn] using hhead
  have hnodup := render_nodup background (residents labels) cuts hbackground hresident hcross
  have hne : render background (residents labels) cuts ≠ [] := by
    have hlen := render_length_ge_background background (residents labels) cuts
    intro hnil
    simp [hnil] at hlen
    omega
  have hbaseEq := post_update_base_unique (render background (residents labels) cuts)
    hnodup hne (labels none) (residents labels lastTarget) finalGap gap hfinalHead hgap
  have hclosed : scheduleEnd sweeps (renderedBase background labels cuts gap) =
      renderedBase background labels cuts gap := by
    rw [hend, hlabels, hcutReturn]
    exact hbaseEq
  have hsweepsNe : sweeps ≠ [] := by
    intro hnil
    have hzero : batches.flatten.length = 0 := by simpa only [hnil, List.length_nil] using hlength.symm
    have hwordNil := List.length_eq_zero_iff.mp hzero
    simp [hwordNil] at hlast
  exact ⟨gap, sweeps, finalGap, htrace, hclosed,
    scheduleRows_closed satellite sweeps _ hsweepsNe hvalid hclosed⟩

/-- The same closed literal contour lies in the joint envelope whenever
its target word is a permitted normal/parking program. -/
theorem closed_trace_envelope (hM : 2 ≤ M) (background : Fin M → α)
    (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (hbackground : Function.Injective background)
    (hresident : Function.Injective (residents (k := k) labels))
    (hcross : ∀ (j : Fin k) (i : Fin M), residents labels j ≠ background i)
    (hrobust : Robust (fun j => cutValue (cuts j)))
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (hcounts : ∀ j, batches.flatten.count j = M)
    (hlabels : executeLabels batches.flatten labels = labels)
    (lastTarget : Fin k) (hlast : batches.flatten.getLast? = some lastTarget)
    (program : List Macro) (hprogram : batches.flatten.map Fin.val = programWord k program)
    (satellite : α) :
    ∃ gap sweeps finalGap,
      Trace (by omega) background batches.flatten labels cuts gap sweeps finalGap ∧
      scheduleEnd sweeps (renderedBase background labels cuts gap) = renderedBase background labels cuts gap ∧
      ClosedTrail (scheduleRows satellite sweeps (renderedBase background labels cuts gap)) ∧
      ∀ row ∈ scheduleRows satellite sweeps (renderedBase background labels cuts gap),
        Envelope background labels cuts row.base := by
  obtain ⟨gap, sweeps, finalGap, htrace, hend, hclosed⟩ :=
    closed_complete_trace hM background labels cuts hbackground hresident hcross hrobust
      batches horders hcounts hlabels lastTarget hlast satellite
  refine ⟨gap, sweeps, finalGap, htrace, hend, hclosed, ?_⟩
  intro row hrow
  exact actual_row_mem (by omega) background program batches.flatten hprogram labels cuts gap
    sweeps finalGap htrace satellite row hrow

end CoefficientTwoPrecision.ClosedTrace

#print axioms CoefficientTwoPrecision.ClosedTrace.closed_complete_trace
#print axioms CoefficientTwoPrecision.ClosedTrace.closed_trace_envelope
