import Quantitative.NormalExactCount
import Quantitative.ActualFullRun

/-!
# The untouched initial normal batch supplies a genuine long full run

Only the first k targets are used in the average calculation. Everything
after that normal batch may be an arbitrary permitted repair schedule.
The resulting run is exhibited at an actual source occurrence index and
is expressed by the LiteralFRun predicate required by source advancement.
-/

namespace CoefficientTwoPrecision.InitialNormalRun

open PositiveParking LiteralSchedule PositiveSchedule TargetTrace TraceComposition TraceSteps
open NormalExactCount ActualFullRun RobustMatching BatchSafety SafeConnectors

variable {M k : Nat} [NeZero M]

theorem initial_normal_run (hM : 2 ≤ M) (hk : 0 < k)
    (q : Fin k → Fin M) (hmono : StrictMono q)
    (hrobust : Robust (fun i => cutValue (q i))) (hzero : q ⟨0, hk⟩ = 0)
    (background : Fin M → Nat) (labels : Option Nat → Nat)
    (word tail : List (Fin k)) (hword : word = List.finRange k ++ tail)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background word labels (fun rank => q rank.rev) gap sweeps finalGap)
    (hnd : (renderedBase background labels (fun rank => q rank.rev) gap).Nodup)
    (hlen : (renderedBase background labels (fun rank => q rank.rev) gap).length = M + k + 1)
    (hhead : ((StationaryCircle.render background (residents labels) (fun rank => q rank.rev)).rotateLeft gap).head? =
      some (residents (k := k) labels ⟨k - 1, by omega⟩)) (satellite : Nat) :
    ∃ H mobile start runLength,
      H.length = M + k ∧ H.Nodup ∧ 0 < runLength ∧ runLength < M + k ∧
      (k - 1) * M + k * k + 1 ≤ k * runLength ∧
      LiteralFRun (scheduleRows satellite sweeps (renderedBase background labels (fun rank => q rank.rev) gap))
        start runLength H mobile := by
  obtain ⟨middleGap, hfirst, _⟩ := trace_split (show 0 < M by omega) background word labels
    (fun rank => q rank.rev) gap sweeps finalGap k htrace
  have hprefix : word.take k = repeatWord 1 (List.finRange k) := by
    rw [hword, List.take_left' (List.length_finRange)]
    simp [repeatWord]
  rw [hprefix] at hfirst
  have hlength : (sweeps.take k).length = k := by
    simpa only [length_repeatWord, List.length_finRange, Nat.one_mul] using
      trace_length (show 0 < M by omega) background (repeatWord 1 (List.finRange k)) labels
        (fun rank => q rank.rev) gap (sweeps.take k) middleGap hfirst
  obtain ⟨_, _, hsum⟩ := normal_counts hM hk q hmono hrobust hzero background 1 labels
    gap (sweeps.take k) middleGap hfirst hnd hlen hhead satellite
  rw [Nat.one_mul] at hsum
  have hne : sweeps.take k ≠ [] := by intro heq; simp only [heq, List.length_nil] at hlength; omega
  obtain ⟨n, hn, hlarge⟩ := exists_large_index (sweeps.take k) hne
  have hnk : n < k := by omega
  have hmoves : movesAt (sweeps.take k) n = movesAt sweeps n := by
    unfold movesAt
    rw [List.getElem?_take_of_lt hnk]
  rw [hlength, hsum, hmoves] at hlarge
  have hnword : n < word.length := by
    rw [hword, List.length_append, List.length_finRange]
    omega
  obtain ⟨H, mobile, start, hHlength, hHnd, hbound, hrun⟩ :=
    indexed_full_run hM (M + k) background word labels (fun rank => q rank.rev)
      gap sweeps finalGap htrace hnd hlen satellite n hnword
  refine ⟨H, mobile, start, movesAt sweeps n, hHlength, hHnd, ?_, hbound, hlarge, hrun⟩
  by_contra hnot
  have hzeroMoves : movesAt sweeps n = 0 := by omega
  rw [hzeroMoves, Nat.mul_zero] at hlarge
  omega

end CoefficientTwoPrecision.InitialNormalRun

#print axioms CoefficientTwoPrecision.InitialNormalRun.initial_normal_run
