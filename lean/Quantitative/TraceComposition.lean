import Quantitative.TargetTrace
import Quantitative.BatchSafety

/-!
# Splitting and composing actual bounded traces

These lemmas retain the exact middle rendered base. They support cyclic
rotation of a literally closed schedule without identifying unrelated
existential constructions of sweep lengths.
-/

namespace CoefficientTwoPrecision.TraceComposition

open PositiveParking LiteralSchedule PositiveSchedule TargetTrace BatchSafety
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type}

theorem executeLabels_append (first last : List (Fin k)) (labels : Option Nat → α) :
    executeLabels (first ++ last) labels = executeLabels last (executeLabels first labels) := by
  induction first generalizing labels with
  | nil => rfl
  | cons target rest ih => exact ih (updateLabels target.val labels)

theorem scheduleEnd_append (first last : List Nat) (base : List α) :
    scheduleEnd (first ++ last) base = scheduleEnd last (scheduleEnd first base) := by
  induction first generalizing base with
  | nil => rfl
  | cons moves rest ih => exact ih (updateEnd moves base)

theorem scheduleRows_append (satellite : α) (first last : List Nat) (base : List α) :
    scheduleRows satellite (first ++ last) base =
      scheduleRows satellite first base ++ scheduleRows satellite last (scheduleEnd first base) := by
  induction first generalizing base with
  | nil => rfl
  | cons moves rest ih =>
    simp only [List.cons_append, scheduleRows, scheduleEnd, ih, List.append_assoc]

theorem trace_append (hM : 0 < M) (background : Fin M → α)
    (first last : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (firstSweeps lastSweeps : List Nat) (middleGap finalGap : Nat)
    (hfirst : Trace hM background first labels cuts gap firstSweeps middleGap)
    (hlast : Trace hM background last (executeLabels first labels) (executeCuts hM first cuts)
      middleGap lastSweeps finalGap) :
    Trace hM background (first ++ last) labels cuts gap (firstSweeps ++ lastSweeps) finalGap := by
  induction first generalizing labels cuts gap firstSweeps with
  | nil =>
    obtain ⟨rfl, rfl⟩ := hfirst
    exact hlast
  | cons target rest ih =>
    obtain ⟨moves, sweeps, nextGap, pre, rfl, hmoves, hpre, hnext, hrest⟩ := hfirst
    refine ⟨moves, sweeps ++ lastSweeps, nextGap, pre, rfl, hmoves, hpre, hnext, ?_⟩
    exact ih (updateLabels target.val labels) (advanceCuts hM target cuts) nextGap sweeps hrest hlast

theorem trace_split (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap n : Nat)
    (htrace : Trace hM background word labels cuts gap sweeps finalGap) :
    ∃ middleGap,
      Trace hM background (word.take n) labels cuts gap (sweeps.take n) middleGap ∧
      Trace hM background (word.drop n) (executeLabels (word.take n) labels)
        (executeCuts hM (word.take n) cuts) middleGap (sweeps.drop n) finalGap := by
  induction n generalizing word labels cuts gap sweeps with
  | zero => exact ⟨gap, ⟨rfl, rfl⟩, htrace⟩
  | succ n ih =>
    cases word with
    | nil =>
      obtain ⟨rfl, rfl⟩ := htrace
      exact ⟨finalGap, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    | cons target word =>
      obtain ⟨moves, rest, nextGap, pre, rfl, hmoves, hpre, hnext, hrest⟩ := htrace
      obtain ⟨middleGap, hfirst, hlast⟩ := ih word (updateLabels target.val labels)
        (advanceCuts hM target cuts) nextGap rest hrest
      refine ⟨middleGap, ?_, hlast⟩
      exact ⟨moves, rest.take n, nextGap, pre, rfl, hmoves, hpre, hnext, hfirst⟩

/-- Equal literal initial bases may use different numerical rotation
indices. A nonempty trace depends on the base, not on that choice. -/
theorem trace_start_congr (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (hword : word ≠ []) (labels : Option Nat → α)
    (cuts : Fin k → Fin M) (firstGap lastGap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (hbase : renderedBase background labels cuts firstGap = renderedBase background labels cuts lastGap)
    (htrace : Trace hM background word labels cuts firstGap sweeps finalGap) :
    Trace hM background word labels cuts lastGap sweeps finalGap := by
  cases word with
  | nil => exact False.elim (hword rfl)
  | cons target word =>
    obtain ⟨moves, rest, nextGap, pre, hsweeps, hmoves, hpre, hnext, hrest⟩ := htrace
    refine ⟨moves, rest, nextGap, pre, hsweeps, hmoves, ?_, ?_, hrest⟩
    · rw [← hbase]
      exact hpre
    · rw [← hbase]
      exact hnext

/-- Splitting sweeps at a target index splits the actual row list at
the exact rendered middle state supplied by the same trace. -/
theorem rows_at_split (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (middleGap n : Nat) (satellite : α)
    (hfirst : Trace hM background (word.take n) labels cuts gap (sweeps.take n) middleGap) :
    scheduleRows satellite sweeps (renderedBase background labels cuts gap) =
      scheduleRows satellite (sweeps.take n) (renderedBase background labels cuts gap) ++
      scheduleRows satellite (sweeps.drop n)
        (renderedBase background (executeLabels (word.take n) labels)
          (executeCuts hM (word.take n) cuts) middleGap) := by
  have hend := trace_endpoint hM background (word.take n) labels cuts gap (sweeps.take n) middleGap hfirst
  have heq := scheduleRows_append satellite (sweeps.take n) (sweeps.drop n)
    (renderedBase background labels cuts gap)
  rw [List.take_append_drop, hend] at heq
  exact heq

end CoefficientTwoPrecision.TraceComposition

#print axioms CoefficientTwoPrecision.TraceComposition.trace_append
#print axioms CoefficientTwoPrecision.TraceComposition.trace_split
#print axioms CoefficientTwoPrecision.TraceComposition.rows_at_split
