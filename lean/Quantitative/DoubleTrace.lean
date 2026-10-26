import Quantitative.TraceSteps

/-!
# Two executions of the same literally closed trace

The second copy uses the same sweep lengths and the same initial finite
role assignment. Literal closure identifies its bases with the original
bases. Comparing across the cyclic join is thus an ordinary comparison
between consecutive batches of this doubled execution.
-/

namespace CoefficientTwoPrecision.DoubleTrace

open LiteralSchedule PositiveSchedule TargetTrace TraceComposition TraceSteps

variable {M k : Nat} {α : Type}

theorem double_closed_trace (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (hword : word ≠ []) (labels : Option Nat → α)
    (cuts : Fin k → Fin M) (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace hM background word labels cuts gap sweeps finalGap)
    (hlabels : executeLabels word labels = labels) (hcuts : executeCuts hM word cuts = cuts)
    (hclosed : scheduleEnd sweeps (renderedBase background labels cuts gap) =
      renderedBase background labels cuts gap) :
    Trace hM background (word ++ word) labels cuts gap (sweeps ++ sweeps) finalGap := by
  have hend := trace_endpoint hM background word labels cuts gap sweeps finalGap htrace
  rw [hlabels, hcuts] at hend
  have hbase : renderedBase background labels cuts gap =
      renderedBase background labels cuts finalGap := hclosed.symm.trans hend
  have hsecond := trace_start_congr hM background word hword labels cuts gap finalGap sweeps finalGap hbase htrace
  apply trace_append hM background word word labels cuts gap sweeps sweeps finalGap finalGap htrace
  simpa only [hlabels, hcuts] using hsecond

theorem baseAt_double_left (sweeps : List Nat) (initial : List α) (n : Nat) (hn : n ≤ sweeps.length) :
    baseAt (sweeps ++ sweeps) initial n = baseAt sweeps initial n := by
  unfold baseAt
  rw [List.take_append_of_le_length hn]

theorem baseAt_double_right (sweeps : List Nat) (initial : List α) (n : Nat)
    (hclosed : scheduleEnd sweeps initial = initial) :
    baseAt (sweeps ++ sweeps) initial (sweeps.length + n) = baseAt sweeps initial n := by
  unfold baseAt
  rw [List.take_length_add_append, scheduleEnd_append, hclosed]

theorem blockAt_double_left (satellite : α) (sweeps : List Nat) (initial : List α)
    (n : Nat) (hn : n < sweeps.length) :
    blockAt satellite (sweeps ++ sweeps) initial n = blockAt satellite sweeps initial n := by
  unfold blockAt movesAt
  rw [List.getElem?_append_left hn, baseAt_double_left sweeps initial n hn.le]

theorem blockAt_double_right (satellite : α) (sweeps : List Nat) (initial : List α) (n : Nat)
    (hclosed : scheduleEnd sweeps initial = initial) :
    blockAt satellite (sweeps ++ sweeps) initial (sweeps.length + n) =
      blockAt satellite sweeps initial n := by
  unfold blockAt movesAt
  rw [List.getElem?_append_right (by omega : sweeps.length ≤ sweeps.length + n),
    Nat.add_sub_cancel_left, baseAt_double_right sweeps initial n hclosed]

theorem doubled_rows (satellite : α) (sweeps : List Nat) (initial : List α)
    (hclosed : scheduleEnd sweeps initial = initial) :
    scheduleRows satellite (sweeps ++ sweeps) initial =
      scheduleRows satellite sweeps initial ++ scheduleRows satellite sweeps initial := by
  rw [scheduleRows_append, hclosed]

end CoefficientTwoPrecision.DoubleTrace

#print axioms CoefficientTwoPrecision.DoubleTrace.double_closed_trace
#print axioms CoefficientTwoPrecision.DoubleTrace.blockAt_double_right
