import Quantitative.TraceComposition

/-!
# Rotating the same literal closed trace

Split a nonempty prefix from a trace whose roles, cuts, and literal base
return. Execute the suffix and then that prefix from the actual middle
base. The resulting trace uses exactly the same sweep lengths in cyclic
order, is literally closed, and its row list is a cyclic rotation of the
original row list.
-/

namespace CoefficientTwoPrecision.TraceRotation

open LiteralSchedule PositiveSchedule TargetTrace BatchSafety TraceComposition
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type}

theorem rotate_closed_trace (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap n : Nat)
    (hnpos : 0 < n) (hn : n ≤ word.length)
    (htrace : Trace hM background word labels cuts gap sweeps finalGap)
    (hlabels : executeLabels word labels = labels) (hcuts : executeCuts hM word cuts = cuts)
    (hclosed : scheduleEnd sweeps (renderedBase background labels cuts gap) =
      renderedBase background labels cuts gap) (satellite : α) :
    ∃ middleGap,
      Trace hM background (word.drop n ++ word.take n)
        (executeLabels (word.take n) labels) (executeCuts hM (word.take n) cuts)
        middleGap (sweeps.drop n ++ sweeps.take n) middleGap ∧
      scheduleEnd (sweeps.drop n ++ sweeps.take n)
        (renderedBase background (executeLabels (word.take n) labels)
          (executeCuts hM (word.take n) cuts) middleGap) =
        renderedBase background (executeLabels (word.take n) labels)
          (executeCuts hM (word.take n) cuts) middleGap ∧
      (scheduleRows satellite sweeps (renderedBase background labels cuts gap)).IsRotated
        (scheduleRows satellite (sweeps.drop n ++ sweeps.take n)
          (renderedBase background (executeLabels (word.take n) labels)
            (executeCuts hM (word.take n) cuts) middleGap)) := by
  obtain ⟨middleGap, hfirst, hlast⟩ :=
    trace_split hM background word labels cuts gap sweeps finalGap n htrace
  have hprefixNe : word.take n ≠ [] := by
    intro hnil
    have hlength := List.length_take_of_le hn
    rw [hnil, List.length_nil] at hlength
    omega
  have hlabelsTail : executeLabels (word.drop n) (executeLabels (word.take n) labels) = labels := by
    rw [← executeLabels_append, List.take_append_drop, hlabels]
  have hcutsTail : executeCuts hM (word.drop n) (executeCuts hM (word.take n) cuts) = cuts := by
    rw [← executeCuts_append, List.take_append_drop, hcuts]
  have hend := trace_endpoint hM background word labels cuts gap sweeps finalGap htrace
  rw [hlabels, hcuts] at hend
  have hbaseFinal : renderedBase background labels cuts gap =
      renderedBase background labels cuts finalGap := hclosed.symm.trans hend
  have hfirst' := trace_start_congr hM background (word.take n) hprefixNe labels cuts gap finalGap
    (sweeps.take n) middleGap hbaseFinal hfirst
  have hfirstAfter : Trace hM background (word.take n)
      (executeLabels (word.drop n) (executeLabels (word.take n) labels))
      (executeCuts hM (word.drop n) (executeCuts hM (word.take n) cuts))
      finalGap (sweeps.take n) middleGap := by
    simpa only [hlabelsTail, hcutsTail] using hfirst'
  have hrotated := trace_append hM background (word.drop n) (word.take n)
    (executeLabels (word.take n) labels) (executeCuts hM (word.take n) cuts)
    middleGap (sweeps.drop n) (sweeps.take n) finalGap middleGap hlast hfirstAfter
  have hrotatedLabels : executeLabels (word.drop n ++ word.take n)
      (executeLabels (word.take n) labels) = executeLabels (word.take n) labels := by
    rw [executeLabels_append, hlabelsTail]
  have hrotatedCuts : executeCuts hM (word.drop n ++ word.take n)
      (executeCuts hM (word.take n) cuts) = executeCuts hM (word.take n) cuts := by
    rw [executeCuts_append, hcutsTail]
  have hrotatedEnd := trace_endpoint hM background (word.drop n ++ word.take n)
    (executeLabels (word.take n) labels) (executeCuts hM (word.take n) cuts)
    middleGap (sweeps.drop n ++ sweeps.take n) middleGap hrotated
  rw [hrotatedLabels, hrotatedCuts] at hrotatedEnd
  refine ⟨middleGap, hrotated, hrotatedEnd, ?_⟩
  have hrows := rows_at_split hM background word labels cuts gap sweeps middleGap n satellite hfirst
  have htailEnd := trace_endpoint hM background (word.drop n)
    (executeLabels (word.take n) labels) (executeCuts hM (word.take n) cuts)
    middleGap (sweeps.drop n) finalGap hlast
  rw [hlabelsTail, hcutsTail, ← hbaseFinal] at htailEnd
  have hrowsRotated := scheduleRows_append satellite (sweeps.drop n) (sweeps.take n)
    (renderedBase background (executeLabels (word.take n) labels)
      (executeCuts hM (word.take n) cuts) middleGap)
  rw [htailEnd] at hrowsRotated
  rw [hrows, hrowsRotated]
  exact List.isRotated_append

end CoefficientTwoPrecision.TraceRotation

#print axioms CoefficientTwoPrecision.TraceRotation.rotate_closed_trace
