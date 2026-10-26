import Quantitative.TraceLocalSimplicity
import Quantitative.OneUpdateSimplicity

/-!
# Consecutive actual update blocks have disjoint cyclic bases

The earlier row is moved, within its stationary circle, to a full-gap
description relative to the actual short source. The later row starts at
that short source's actual endpoint. The stronger stopping bound excludes
the only gap at which the two cyclic bases could agree.
-/

namespace CoefficientTwoPrecision.AdjacentBlocks

open LiteralState StationaryCircle LiteralSchedule PositiveSchedule TargetTrace
open TraceSteps TraceLocalSimplicity RowValidity RobustMatching BatchSafety
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type} [DecidableEq α]

theorem adjacent_blocks_disjoint (hM : 3 ≤ M) (hk : 0 < k)
    (background : Fin M → α) (hbackground : Function.Injective background)
    (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (hrobust : Robust (fun j => cutValue (cuts j)))
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (gap : Nat) (sweeps : List Nat) (finalGap n : Nat)
    (htrace : Trace (by omega) background batches.flatten labels cuts gap sweeps finalGap)
    (hn : n + 1 < batches.flatten.length)
    (hnodup : (renderedBase background labels cuts gap).Nodup)
    (satellite : α) (first last : Row α)
    (hfirst : first ∈ blockAt satellite sweeps (renderedBase background labels cuts gap) n)
    (hlast : last ∈ blockAt satellite sweeps (renderedBase background labels cuts gap) (n + 1)) :
    ¬ first.base.IsRotated last.base := by
  let word := batches.flatten
  have hnword : n + 1 < word.length := hn
  let initial := renderedBase background labels cuts gap
  let target : Fin k := word[n]'(by omega)
  let currentLabels := executeLabels (word.take n) labels
  let currentCuts := executeCuts (show 0 < M by omega) (word.take n) cuts
  obtain ⟨middleGap, pre, hbase, hmoves, hsuffix⟩ :=
    trace_step (show 0 < M by omega) background word labels cuts gap sweeps finalGap n htrace (by omega)
  let stationary := (render background (residents currentLabels) currentCuts).rotateLeft middleGap
  let mobile := currentLabels none
  let resident := residents currentLabels target
  let crossed := background (currentCuts target)
  have hbase' : baseAt sweeps initial n = stationary ++ [mobile] := hbase
  have hsuffix' : fullIterate (movesAt sweeps n) (baseAt sweeps initial n) =
      pre ++ [resident, crossed, mobile] := hsuffix
  have hstationaryLength : M ≤ stationary.length := by
    dsimp only [stationary]
    rw [LiteralState.rotateLeft_eq_rotate, List.length_rotate]
    exact render_length_ge_background background (residents currentLabels) currentCuts
  have hndBase := (baseAt_perm (by omega) background word labels cuts gap sweeps finalGap n htrace).nodup_iff.mpr
    hnodup
  have hsourcePerm := fullIterate_perm stationary mobile (movesAt sweeps n)
  rw [← hbase', hsuffix'] at hsourcePerm
  have hsourceNodup : (pre ++ [resident, crossed, mobile]).Nodup := hsourcePerm.nodup_iff.mpr hndBase
  have hpreLength : 0 < pre.length := by
    have hlength := hsourcePerm.length_eq
    rw [hbase'] at hlength
    simp only [List.length_append, List.length_cons, List.length_nil] at hlength
    omega
  obtain ⟨i, _, hfirstBase⟩ := updateRows_base satellite (movesAt sweeps n) _ first hfirst
  obtain ⟨j, hj, hlastBase⟩ := updateRows_base satellite (movesAt sweeps (n + 1)) _ last hlast
  obtain ⟨earlierGap, hearlier⟩ := fullIterate_from_any_gap stationary mobile (by omega)
    (movesAt sweeps n) i
  have hfirstEq : first.base = fullIterate earlierGap (pre ++ [resident, crossed, mobile]) := by
    rw [hfirstBase, hbase', hearlier]
    rw [← hbase', hsuffix']
  have hlength := trace_length (show 0 < M by omega) background word labels cuts gap sweeps finalGap htrace
  have hnsw : n < sweeps.length := by omega
  have hnextBase : baseAt sweeps initial (n + 1) = shortStep (pre ++ [resident, crossed, mobile]) := by
    rw [baseAt_succ sweeps initial n hnsw, updateEnd, hsuffix']
  have hlastEq : last.base = fullIterate j (shortStep (pre ++ [resident, crossed, mobile])) := by
    rw [hlastBase, hnextBase]
  have hbound := next_sweep_lt_last_gap hM hk background hbackground labels cuts hrobust batches horders
    gap sweeps finalGap n htrace hn hnodup
  change movesAt sweeps (n + 1) < (baseAt sweeps initial (n + 1)).dropLast.length - 1 at hbound
  have hjlast : j < (baseAt sweeps initial (n + 1)).dropLast.length - 1 := by omega
  rw [hnextBase, (shortStep_post_update_data pre resident crossed mobile).2] at hjlast
  intro hcyclic
  rw [hfirstEq, hlastEq] at hcyclic
  exact OneUpdateSimplicity.no_return_across_one_update pre resident crossed mobile hpreLength
    hsourceNodup earlierGap j hjlast hcyclic

end CoefficientTwoPrecision.AdjacentBlocks

#print axioms CoefficientTwoPrecision.AdjacentBlocks.adjacent_blocks_disjoint
