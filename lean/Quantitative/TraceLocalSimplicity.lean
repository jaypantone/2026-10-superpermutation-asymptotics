import Quantitative.TraceSteps
import Quantitative.BatchPrefixes
import Quantitative.StoppingBound
import Quantitative.FullRunSimplicity
import Quantitative.RowValidity

/-!
# Proper and strictly stopping sweeps at actual trace indices

The alphabet and nodup properties are transported by the actual prefix
trace. Each indexed block is cyclically simple. At consecutive update
indices, the actual preceding suffix supplies the crossed background and
the advanced resident cut required by the stronger stopping theorem.
-/

namespace CoefficientTwoPrecision.TraceLocalSimplicity

open LiteralState StationaryCircle StationaryUpdate StationarySuccessor
open LiteralSchedule PositiveSchedule TargetTrace TraceComposition TraceSteps
open RobustMatching RobustSafety BatchSafety BatchPrefixes RowValidity
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type}

theorem baseAt_perm (hM : 2 ≤ M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap n : Nat)
    (htrace : Trace (by omega) background word labels cuts gap sweeps finalGap) :
    (baseAt sweeps (renderedBase background labels cuts gap) n).Perm
      (renderedBase background labels cuts gap) := by
  obtain ⟨middleGap, hfirst, _⟩ :=
    trace_split (show 0 < M by omega) background word labels cuts gap sweeps finalGap n htrace
  exact scheduleEnd_perm (sweeps.take n) _
    (trace_suffixSchedule hM background (word.take n) labels cuts gap (sweeps.take n) middleGap hfirst)

theorem block_cyclicDistinct (hM : 2 ≤ M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap n : Nat)
    (htrace : Trace (by omega) background word labels cuts gap sweeps finalGap)
    (hn : n < word.length) (hnodup : (renderedBase background labels cuts gap).Nodup)
    (satellite : α) :
    (blockAt satellite sweeps (renderedBase background labels cuts gap) n).Pairwise
      (fun first last => ¬ first.base.IsRotated last.base) := by
  obtain ⟨middleGap, pre, hbase, hmoves, _⟩ :=
    trace_step (show 0 < M by omega) background word labels cuts gap sweeps finalGap n htrace hn
  have hnd := (baseAt_perm hM background word labels cuts gap sweeps finalGap n htrace).nodup_iff.mpr hnodup
  rw [hbase] at hnd
  have hstationary := (List.nodup_append.mp hnd).1
  have hfresh : executeLabels (word.take n) labels none ∉
      (render background (residents (executeLabels (word.take n) labels))
        (executeCuts (show 0 < M by omega) (word.take n) cuts)).rotateLeft middleGap := by
    intro hmem
    exact (List.nodup_append.mp hnd).2.2 _ hmem _ (by simp) rfl
  have hbound : movesAt sweeps n <
      ((render background (residents (executeLabels (word.take n) labels))
        (executeCuts (show 0 < M by omega) (word.take n) cuts)).rotateLeft middleGap).length := by
    rw [LiteralState.rotateLeft_eq_rotate, List.length_rotate]
    exact hmoves
  unfold blockAt
  rw [hbase]
  exact List.pairwise_map.mp
    (FullRunSimplicity.updateRows_cyclicDistinct _ _ satellite hstationary hfresh _ hbound)

/-- Any gap of a stationary circle can be expressed as full moves from
the particular gap that is about to perform its short update. -/
theorem fullIterate_from_any_gap (stationary : List α) (mobile : α)
    (hlen : 0 < stationary.length) (moves i : Nat) :
    ∃ j, fullIterate i (stationary ++ [mobile]) =
      fullIterate j (fullIterate moves (stationary ++ [mobile])) := by
  obtain ⟨j, _, hreach⟩ := rotation_reachable stationary hlen moves i
  refine ⟨j, ?_⟩
  rw [fullIterate_formula, fullIterate_formula, fullIterate_formula, hreach]

/-- The actual next sweep stops before the last gap of its actual
stationary list. No extra stopping assumption is supplied. -/
theorem next_sweep_lt_last_gap (hM : 3 ≤ M) (hk : 0 < k)
    (background : Fin M → α) (hbackground : Function.Injective background)
    (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (hrobust : Robust (fun j => cutValue (cuts j)))
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (gap : Nat) (sweeps : List Nat) (finalGap n : Nat)
    (htrace : Trace (by omega) background batches.flatten labels cuts gap sweeps finalGap)
    (hn : n + 1 < batches.flatten.length)
    (hnodup : (renderedBase background labels cuts gap).Nodup) :
    movesAt sweeps (n + 1) <
      (baseAt sweeps (renderedBase background labels cuts gap) (n + 1)).dropLast.length - 1 := by
  let word := batches.flatten
  have hnword : n + 1 < word.length := hn
  let initial := renderedBase background labels cuts gap
  let previous : Fin k := word[n]'(by omega)
  let target : Fin k := word[n + 1]'hn
  let oldLabels := executeLabels (word.take n) labels
  let oldCuts := executeCuts (show 0 < M by omega) (word.take n) cuts
  let newLabels := executeLabels (word.take (n + 1)) labels
  let newCuts := executeCuts (show 0 < M by omega) (word.take (n + 1)) cuts
  obtain ⟨oldGap, pre, holdBase, _, holdSuffix⟩ :=
    trace_step (show 0 < M by omega) background word labels cuts gap sweeps finalGap n htrace (by omega)
  obtain ⟨newGap, nextPre, hnewBase, hmoves, hnewSuffix⟩ :=
    trace_step (show 0 < M by omega) background word labels cuts gap sweeps finalGap (n + 1) htrace hn
  have hlength := trace_length (show 0 < M by omega) background word labels cuts gap sweeps finalGap htrace
  have hnsw : n < sweeps.length := by omega
  have hrep := represents_prefix (show 0 < M by omega) hk batches horders (n + 1) hn.le cuts
  have hnewCuts : Function.Injective newCuts := by
    intro i j hij
    apply perturbed_injective (fun a => cutValue (cuts a)) hrobust
      ((n + 1) / k : Nat) (prefixPhases batches (n + 1))
    have hc := congrArg cutValue hij
    rw [hrep i, hrep j] at hc
    exact hc
  have hadvance : newCuts = advanceCuts (show 0 < M by omega) previous oldCuts := by
    dsimp only [newCuts, oldCuts, previous]
    rw [List.take_succ_eq_append_getElem (by omega : n < word.length), executeCuts_append]
    rfl
  have hprevious : newCuts previous = successor (by omega) (oldCuts previous) := by
    rw [hadvance]
    simp only [advanceCuts, moveCut, ↓reduceIte]
  have hndBase := (baseAt_perm (by omega) background word labels cuts gap sweeps finalGap (n + 1)
    htrace).nodup_iff.mpr hnodup
  rw [hnewBase] at hndBase
  have hnd : (render background (residents newLabels) newCuts).Nodup := by
    have hs := (List.nodup_append.mp hndBase).1
    rw [LiteralState.rotateLeft_eq_rotate] at hs
    exact List.nodup_rotate.mp hs
  have hlast : ((render background (residents newLabels) newCuts).rotateLeft newGap).getLast? =
      some (background (oldCuts previous)) := by
    have hlastBase : (baseAt sweeps initial (n + 1)).dropLast.getLast? =
        some (background (oldCuts previous)) := by
      rw [baseAt_succ sweeps initial n hnsw, updateEnd, holdSuffix,
        (shortStep_post_update_data pre (residents oldLabels previous)
          (background (oldCuts previous)) (oldLabels none)).2]
      simp only [List.getLast?_cons, List.getLast?_concat, Option.getD_some]
    rw [hnewBase, renderedBase, List.dropLast_concat] at hlastBase
    exact hlastBase
  have hnextSuffix : fullIterate (movesAt sweeps (n + 1))
      ((render background (residents newLabels) newCuts).rotateLeft newGap ++ [newLabels none]) =
      nextPre ++ [residents newLabels target, background (newCuts target), newLabels none] := by
    rw [hnewBase] at hnewSuffix
    exact hnewSuffix
  have hbound := StoppingBound.sweep_lt_last_gap hM background hbackground (residents newLabels)
    newCuts hnewCuts hnd (fun j => cutValue (cuts j)) hrobust ((n + 1) / k : Nat)
    (prefixPhases batches (n + 1)) hrep previous target (oldCuts previous) hprevious
    (newLabels none) newGap (movesAt sweeps (n + 1)) hlast hmoves nextPre hnextSuffix
  rw [hnewBase, renderedBase, List.dropLast_concat, LiteralState.rotateLeft_eq_rotate, List.length_rotate]
  exact hbound

end CoefficientTwoPrecision.TraceLocalSimplicity

#print axioms CoefficientTwoPrecision.TraceLocalSimplicity.block_cyclicDistinct
#print axioms CoefficientTwoPrecision.TraceLocalSimplicity.next_sweep_lt_last_gap
