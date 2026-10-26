import Quantitative.TraceLocalSimplicity
import Quantitative.SafeConnectors

/-!
# Literal full runs at actual source occurrence indices

Every full sweep in the trace is a consecutive list of original full
rows. The index at which it starts is the length of the actual preceding
row list. This module supplies the stronger LiteralFRun predicate used
by connector extraction, rather than merely counting full rows.
-/

namespace CoefficientTwoPrecision.ActualFullRun

open LiteralState LiteralSchedule TargetTrace TraceComposition TraceSteps TraceLocalSimplicity
open SuperpermutationUpperBound SuperpermutationUpperBound.Certificates.CircleBase
open SafeConnectors

theorem updateRows_full_run (satellite : Nat) (H : List Nat) (mobile moves : Nat)
    (before after : List (Row Nat)) :
    LiteralFRun (before ++ updateRows satellite moves (H ++ [mobile]) ++ after)
      before.length moves H mobile := by
  constructor
  · simp only [List.length_append, updateRows_length]
    omega
  · intro j hj
    have hindex :
        rowAt (before ++ updateRows satellite moves (H ++ [mobile]) ++ after) (before.length + j) =
          fullRow (fullIterate j (H ++ [mobile])) satellite := by
      unfold rowAt
      rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left (by rw [updateRows_length]; omega)]
      rw [updateRows, List.getElem?_append_left (by simp only [List.length_map, List.length_range]; exact hj),
        List.getElem?_map, List.getElem?_eq_getElem (by simpa only [List.length_range] using hj),
        List.getElem_range]
      rfl
    rw [hindex]
    exact ⟨fullIterate_formula H mobile j, rfl⟩

theorem schedule_block_split (satellite : Nat) (sweeps : List Nat) (base : List Nat)
    (n : Nat) (hn : n < sweeps.length) :
    scheduleRows satellite sweeps base =
      scheduleRows satellite (sweeps.take n) base ++
        updateRows satellite (movesAt sweeps n) (baseAt sweeps base n) ++
          scheduleRows satellite (sweeps.drop (n + 1))
            (updateEnd (movesAt sweeps n) (baseAt sweeps base n)) := by
  have hsplit : sweeps = sweeps.take n ++ sweeps[n] :: sweeps.drop (n + 1) := by
    conv_lhs => rw [← List.take_append_drop n sweeps, List.drop_eq_getElem_cons hn]
  have hmoves : movesAt sweeps n = sweeps[n] := by
    simp only [movesAt, List.getElem?_eq_getElem hn, Option.getD_some]
  conv_lhs => rw [hsplit, scheduleRows_append]
  simp only [scheduleRows, ← hmoves, baseAt, List.append_assoc]

theorem indexed_full_run {M k : Nat} (hM : 2 ≤ M) (h : Nat)
    (background : Fin M → Nat) (word : List (Fin k)) (labels : Option Nat → Nat)
    (cuts : Fin k → Fin M) (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background word labels cuts gap sweeps finalGap)
    (hnd : (renderedBase background labels cuts gap).Nodup)
    (hlen : (renderedBase background labels cuts gap).length = h + 1)
    (satellite n : Nat) (hn : n < word.length) :
    ∃ H mobile start,
      H.length = h ∧ H.Nodup ∧ movesAt sweeps n < h ∧
      LiteralFRun (scheduleRows satellite sweeps (renderedBase background labels cuts gap))
        start (movesAt sweeps n) H mobile := by
  obtain ⟨middleGap, pre, hbase, hbound, hsuffix⟩ :=
    trace_step (show 0 < M by omega) background word labels cuts gap sweeps finalGap n htrace hn
  let H := (StationaryCircle.render background
    (residents (PositiveSchedule.executeLabels (word.take n) labels))
    (executeCuts (show 0 < M by omega) (word.take n) cuts)).rotateLeft middleGap
  let mobile := PositiveSchedule.executeLabels (word.take n) labels none
  change baseAt sweeps (renderedBase background labels cuts gap) n = H ++ [mobile] at hbase
  have hperm := baseAt_perm hM background word labels cuts gap sweeps finalGap n htrace
  have hcurrentNodup := hperm.nodup_iff.mpr hnd
  have hcurrentLength := hperm.length_eq.trans hlen
  rw [hbase] at hcurrentNodup hcurrentLength
  have hHlength : H.length = h := by
    simp only [List.length_append, List.length_singleton] at hcurrentLength
    omega
  have hmove : movesAt sweeps n < h := by
    have hH : H.length = (StationaryCircle.render background
        (residents (PositiveSchedule.executeLabels (word.take n) labels))
        (executeCuts (show 0 < M by omega) (word.take n) cuts)).length := by
      simp only [H, LiteralState.rotateLeft_eq_rotate, List.length_rotate]
    omega
  have hnsweeps : n < sweeps.length := by
    rw [trace_length (show 0 < M by omega) background word labels cuts gap sweeps finalGap htrace]
    exact hn
  refine ⟨H, mobile, (scheduleRows satellite (sweeps.take n) (renderedBase background labels cuts gap)).length,
    hHlength, (List.nodup_append.mp hcurrentNodup).1, hmove, ?_⟩
  rw [schedule_block_split satellite sweeps _ n hnsweeps, hbase]
  exact updateRows_full_run satellite H mobile (movesAt sweeps n) _ _

theorem exists_maximum (word : List Nat) (hne : word ≠ []) :
    ∃ m ∈ word, ∀ x ∈ word, x ≤ m := by
  induction word with
  | nil => contradiction
  | cons first word ih =>
    by_cases htail : word = []
    · subst word
      exact ⟨first, by simp, by simp⟩
    · obtain ⟨m, hm, hmax⟩ := ih htail
      by_cases hfirst : first ≤ m
      · refine ⟨m, by simp [hm], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hfirst
        · exact hmax x hx
      · refine ⟨first, by simp, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · exact le_trans (hmax x hx) (by omega)

theorem sum_le_length_mul (word : List Nat) (bound : Nat) (hbound : ∀ x ∈ word, x ≤ bound) :
    word.sum ≤ word.length * bound := by
  induction word with
  | nil => simp
  | cons first word ih =>
    have hfirst := hbound first (by simp)
    have htail := ih (fun x hx => hbound x (by simp [hx]))
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem exists_large_index (word : List Nat) (hne : word ≠ []) :
    ∃ n, n < word.length ∧ word.sum ≤ word.length * movesAt word n := by
  obtain ⟨m, hm, hmax⟩ := exists_maximum word hne
  obtain ⟨n, hn, heq⟩ := List.mem_iff_getElem.mp hm
  refine ⟨n, hn, ?_⟩
  have hsum := sum_le_length_mul word m hmax
  simpa only [movesAt, List.getElem?_eq_getElem hn, Option.getD_some, heq] using hsum

end CoefficientTwoPrecision.ActualFullRun

#print axioms CoefficientTwoPrecision.ActualFullRun.indexed_full_run
#print axioms CoefficientTwoPrecision.ActualFullRun.exists_large_index
