import Quantitative.CandidateConstruction
import Quantitative.CanonicalRowState
import Quantitative.CandidateCollision
import Quantitative.BatchTime

/-!
# The same constructed row has canonical coordinates and event avoidance

Both conclusions are obtained from the recorded repaired trace. The
proper target prefix fixes its physical role assignment and canonical
batch time. Its event, transported through the retained origin, belongs
to the actual compiled parking group, so the forbidden pair is absent.
-/

namespace CoefficientTwoPrecision.CandidateRowState

open SuperpermutationUpperBound GuardCatalogue GridBackground PhysicalOldCuts NeighbourGeometry
open CandidateSpace LabelledReconstruction PrimaryCatalogue ProximityCatalogue ProximitySurvivors
open CandidateConstruction RepairGroups RepairProgram RepairAvoidance CyclicRepairSchedule
open SourceAlphabet OriginTransport LiteralSchedule TargetTrace SourceFamilyAdapter
open ActualCyclicMatching BatchSafety SortedFrameSupply PhysicalJointStates

variable {m d A : Nat} [NeZero (m + guardNumber d A)]
variable (hA : 0 < A) (old : Fin m → Nat) (ho : Function.Injective old)
variable (physical : Physical d A → Nat) (hl : Function.Injective physical)
variable (hcross : ∀ p i, physical p ≠ old i)
variable {controls oldWord : List Nat}
variable (rowIndex : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
variable {candidate : Candidate m d A} {hMpos : 0 < m + guardNumber d A}
variable (C : Witness hA old ho physical hl hcross controls oldWord rowIndex candidate hMpos)

theorem program_count : MacroCatalogue.batchCount (program (m := m) (A := A) C.groups) =
    m + guardNumber d A := by
  have hfirst : ∀ G ∈ C.groups, d + 3 ≤ G.first := by
    intro G hG
    have h := (C.bounds G hG).1
    omega
  have hfit : ∀ G ∈ C.groups, groupEnd (d + 3) (groupPhase (d + 2)) G < m + guardNumber d A := by
    intro G hG
    obtain ⟨_, _, _, _, hend, _⟩ := RepairIntervals.rounded_repair_interval (d + 3)
      (groupPhase (d + 2) G) G.first G.last (by omega)
      (mobilePhase_lt _ _) (C.bounds G hG).1 G.first_le_last
    exact hend.trans_lt (C.bounds G hG).2
  exact (constructed_program_counts (d + 3) (m + guardNumber d A)
    (groupPhase (d + 2)) (groupChoice (d + 2)) C.groups (by omega) hMpos
    (fun G _ => mobilePhase_lt _ _) hfirst hfit C.before).1

theorem literal_envelope (row : Row Nat) (hrow : row ∈ C.contour.rows) :
    LiteralPacking.InEnvelope (canonicalBackground hA old ho physical hl hcross candidate)
      (fun c => physical (activeControl d A hA candidate.1 (rowIndex c))) candidate.2.2 row.base := by
  have he := C.envelope row hrow
  have hlabels : (fun p => physical (activeControl d A hA candidate.1
      (rowIndex (FiniteRoles.lift ((reverseRoles (d + 2)).trans candidate.2.2.2) p)))) =
      engineLabels (activeEmbed hA physical candidate) (initial rowIndex candidate.2.2) := by
    funext p
    cases p with
    | none => rfl
    | some i =>
        by_cases hi : i < d + 2 <;>
          simp only [FiniteRoles.lift, hi, dite_true, dite_false, engineLabels, initial,
            Equiv.trans_apply, activeEmbed]
  change LiteralEnvelope.Envelope _ _ _ _
  rw [hlabels]
  exact he

theorem row_state (hd : 3 ≤ d)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ labelledFrames (m + guardNumber d A) d)
    (hcandidate : candidate ∈ survivors m d A hA S)
    (row : Row Nat) (hrow : row ∈ C.contour.rows) :
    ∃ role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3),
    ∃ localCuts : Fin (d + 2) → Fin (m + guardNumber d A), ∃ gap : Nat,
    ∃ time : Fin (m + guardNumber d A), ∃ phase : Fin (d + 2) → Fin 2,
      row.base = rowBase hA old ho physical hl hcross candidate.1 candidate.2.1 role localCuts gap ∧
      CollisionGeometry.HasFrame localCuts ∧
      (∀ j, (localCuts j).val =
        ((candidate.2.2.1 j).val + time.val + (phase j).val) % (m + guardNumber d A)) ∧
      ∀ event : Event d A hA candidate.1,
        time ∈ times m hA candidate.1 candidate.2.1 candidate.2.2.1 event →
        role (some (slot hA candidate.1 event)) ≠ (shared hA candidate.1 event.1).1 := by
  have hframe := (Finset.mem_product.mp (hS ((mem_survivors hA S candidate).mp hcandidate).1)).1
  let batches := FiniteProgram.batches (d + 2) (program (m := m) (A := A) C.groups)
  have horders : ∀ order ∈ batches, order.Perm (List.finRange (d + 2)) :=
    FiniteProgram.batches_orders _ _
  have hnumber : batches.length = m + guardNumber d A :=
    (FiniteProgram.batches_length _ _).trans (program_count hA old ho physical hl hcross rowIndex C)
  have hrowTrace : row ∈ scheduleRows 9 C.sweeps
      (renderedBase
        (shiftedBackground (canonicalBackground hA old ho physical hl hcross candidate) (translationCut C.cut))
        (engineLabels (activeEmbed hA physical candidate) (initial rowIndex candidate.2.2))
        (fun rank => candidate.2.2.1 rank.rev) C.gap) := by
    rwa [← C.rows_eq]
  obtain ⟨n, hn, gap, localCuts, time, phase, hbase, htime, hlocal, hhasFrame, htake⟩ :=
    CanonicalRowState.actual_row_state hMpos
      (canonicalBackground hA old ho physical hl hcross candidate)
      (activeEmbed hA physical candidate) (initial rowIndex candidate.2.2)
      candidate.2.2.1 hframe (translationCut C.cut) batches horders C.gap C.sweeps C.finalGap
      C.trace 9 row hrowTrace
  let role := (reverseRoles (d + 2)).trans
    (FiniteRoles.execute (batches.flatten.take n) (initial rowIndex candidate.2.2))
  refine ⟨role, localCuts, gap, time, phase, hbase, hhasFrame, hlocal, ?_⟩
  intro event hevent
  have hbatch : n / (d + 2) < m + guardNumber d A :=
    BatchTime.batch_time_lt (by omega) batches horders hnumber n hn
  have hfirst : ∀ G ∈ C.groups, d + 3 ≤ G.first := by
    intro G hG
    have h := (C.bounds G hG).1
    omega
  have hmem : (C.cut + (n / (d + 2) : Nat), forbiddenPair hA candidate.1 event) ∈
      CandidateEvents.events hA candidate := by
    have he := CandidateEvents.event_mem hA candidate event time hevent
    rw [translationCut_value] at htime
    change (time.val : ZMod (m + guardNumber d A)) = C.cut + (n / (d + 2) : Nat) at htime
    rwa [← htime]
  have havoid := CanonicalEventAvoidance.canonical_prefix_avoids (by omega : 2 ≤ d + 2)
    (initial rowIndex candidate.2.2) (CandidateEvents.events hA candidate) C.cut C.groups
    C.grouped hfirst C.before n hbatch (forbiddenPair hA candidate.1 event) hmem
  exact havoid

end CoefficientTwoPrecision.CandidateRowState

#print axioms CoefficientTwoPrecision.CandidateRowState.literal_envelope
#print axioms CoefficientTwoPrecision.CandidateRowState.row_state
