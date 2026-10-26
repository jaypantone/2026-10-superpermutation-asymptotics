import Quantitative.TraceComposition

/-!
# Exact indexed update blocks of a literal trace

The base at update index n is computed by executing the first n actual
sweep lengths. Each block is the actual full/short row list at that base.
Flattening these indexed blocks reproduces the original row list exactly.
The trace supplies its finite-prefix cut and role state, its proper sweep
bound, and its actual short suffix at every valid index.
-/

namespace CoefficientTwoPrecision.TraceSteps

open LiteralSchedule PositiveSchedule TargetTrace TraceComposition
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type}

def baseAt (sweeps : List Nat) (initial : List α) (n : Nat) : List α :=
  scheduleEnd (sweeps.take n) initial

def movesAt (sweeps : List Nat) (n : Nat) : Nat := (sweeps[n]?).getD 0

def blockAt (satellite : α) (sweeps : List Nat) (initial : List α) (n : Nat) : List (Row α) :=
  updateRows satellite (movesAt sweeps n) (baseAt sweeps initial n)

theorem baseAt_succ (sweeps : List Nat) (initial : List α) (n : Nat) (hn : n < sweeps.length) :
    baseAt sweeps initial (n + 1) = updateEnd (movesAt sweeps n) (baseAt sweeps initial n) := by
  unfold baseAt
  rw [List.take_succ_eq_append_getElem hn, scheduleEnd_append]
  simp only [scheduleEnd, movesAt, List.getElem?_eq_getElem hn, Option.getD_some]

theorem baseAt_cons_succ (moves : Nat) (sweeps : List Nat) (initial : List α) (n : Nat) :
    baseAt (moves :: sweeps) initial (n + 1) = baseAt sweeps (updateEnd moves initial) n := rfl

theorem blockAt_cons_zero (satellite : α) (moves : Nat) (sweeps : List Nat) (initial : List α) :
    blockAt satellite (moves :: sweeps) initial 0 = updateRows satellite moves initial := rfl

theorem blockAt_cons_succ (satellite : α) (moves : Nat) (sweeps : List Nat)
    (initial : List α) (n : Nat) :
    blockAt satellite (moves :: sweeps) initial (n + 1) =
      blockAt satellite sweeps (updateEnd moves initial) n := rfl

/-- The indexed blocks are the actual emitted row occurrences. -/
theorem rows_eq_blocks (satellite : α) (sweeps : List Nat) (initial : List α) :
    scheduleRows satellite sweeps initial =
      (List.range sweeps.length).flatMap (blockAt satellite sweeps initial) := by
  induction sweeps generalizing initial with
  | nil => rfl
  | cons moves sweeps ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Function.comp_def, blockAt_cons_zero, blockAt_cons_succ, scheduleRows]
    rw [ih]

/-- Every valid update index has the concrete state and suffix used in
the positive-update construction. -/
theorem trace_step (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap n : Nat)
    (htrace : Trace hM background word labels cuts gap sweeps finalGap)
    (hn : n < word.length) :
    ∃ middleGap pre,
      baseAt sweeps (renderedBase background labels cuts gap) n =
        renderedBase background (executeLabels (word.take n) labels)
          (executeCuts hM (word.take n) cuts) middleGap ∧
      movesAt sweeps n < (StationaryCircle.render background
        (residents (executeLabels (word.take n) labels)) (executeCuts hM (word.take n) cuts)).length ∧
      LiteralState.fullIterate (movesAt sweeps n)
        (baseAt sweeps (renderedBase background labels cuts gap) n) =
          pre ++ [residents (executeLabels (word.take n) labels) word[n],
            background (executeCuts hM (word.take n) cuts word[n]), executeLabels (word.take n) labels none] := by
  obtain ⟨middleGap, hfirst, hlast⟩ :=
    trace_split hM background word labels cuts gap sweeps finalGap n htrace
  have hbase := trace_endpoint hM background (word.take n) labels cuts gap (sweeps.take n) middleGap hfirst
  rw [List.drop_eq_getElem_cons hn] at hlast
  obtain ⟨moves, rest, nextGap, pre, hsweeps, hmoves, hpre, _, _⟩ := hlast
  have hget : sweeps[n]? = some moves := by
    have h := congrArg List.head? hsweeps
    simpa only [List.head?_drop, List.head?_cons] using h
  have hmovesAt : movesAt sweeps n = moves := by simp only [movesAt, hget, Option.getD_some]
  refine ⟨middleGap, pre, hbase, ?_, ?_⟩
  · rw [hmovesAt]
    exact hmoves
  · change LiteralState.fullIterate (movesAt sweeps n)
      (scheduleEnd (sweeps.take n) (renderedBase background labels cuts gap)) = _
    rw [hmovesAt, hbase]
    exact hpre

/-- Every row in one indexed block has that block's actual state and an
explicit proper full-gap index, including the final short source row. -/
theorem block_row (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap n : Nat)
    (htrace : Trace hM background word labels cuts gap sweeps finalGap) (hn : n < word.length)
    (satellite : α) (row : Row α)
    (hrow : row ∈ blockAt satellite sweeps (renderedBase background labels cuts gap) n) :
    ∃ i ≤ movesAt sweeps n,
      row.base = LiteralState.fullIterate i (baseAt sweeps (renderedBase background labels cuts gap) n) := by
  exact updateRows_base satellite (movesAt sweeps n) _ row hrow

end CoefficientTwoPrecision.TraceSteps

#print axioms CoefficientTwoPrecision.TraceSteps.rows_eq_blocks
#print axioms CoefficientTwoPrecision.TraceSteps.trace_step
