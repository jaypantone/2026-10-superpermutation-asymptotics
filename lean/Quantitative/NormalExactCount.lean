import Quantitative.NormalActualSweeps
import Quantitative.NormalArithmetic

/-!
# Exact row and charge counts of the literal normal contour

The pointwise sweep calculation is now summed for the actual sweep list.
No length or charge estimate is assumed. With total=M batches, the first
identity is N0=M*((k-1)*M+k*(k+1)+1), and the second is B0=2*M*k.
-/

namespace CoefficientTwoPrecision.NormalExactCount

open PositiveParking NormalContour NormalArithmetic NormalActualSweeps
open LiteralSchedule TargetTrace TraceSteps RobustMatching BatchSafety
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type} [NeZero M]

theorem normalCost_sum (hk : 0 < k) (q : Fin k → Fin M) (hzero : q ⟨0, hk⟩ = 0) :
    ((List.finRange k).map (normalCost q)).sum = (k - 1) * M + k * k + 1 := by
  let s : Nat → Nat := fun i => if hi : i < k then normalCost q ⟨i, hi⟩ else 0
  let p : Nat → Nat := fun i => if hi : i < k then (q (⟨i, hi⟩ : Fin k).rev).val else 0
  have hfirst : s 0 = p 0 + k + 1 := by
    simp only [s, p, dif_pos hk, normalCost, Fin.val_mk, dite_true]
  have hlast : p (k - 1) = 0 := by
    have hrev : (⟨k - 1, by omega⟩ : Fin k).rev = ⟨0, hk⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_mk]
      omega
    simp only [p, dif_pos (show k - 1 < k by omega), hrev, hzero, Fin.val_zero]
  have hstep : ∀ i, i + 1 < k → s (i + 1) + p i = M + k + p (i + 1) := by
    intro i hip
    have hi : i < k := by omega
    simp only [s, p, dif_pos hi, dif_pos hip, normalCost, Fin.val_mk,
      dif_neg (show i + 1 ≠ 0 by omega), Nat.add_sub_cancel]
    apply Nat.sub_add_cancel
    have hcut := (q (⟨i, hi⟩ : Fin k).rev).isLt
    omega
  have hsum := batch_sum M k hk s p hfirst hlast hstep
  have hmap : (List.finRange k).map (normalCost q) = (List.range k).map s := by
    rw [← map_finRange_val k, List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_def, s, dif_pos i.isLt]
  rw [hmap]
  exact hsum

/-- These counts concern the actual emitted original Row list and its
actual charge function. -/
theorem normal_counts [DecidableEq α] (hM : 2 ≤ M) (hk : 0 < k)
    (q : Fin k → Fin M) (hmono : StrictMono q)
    (hrobust : Robust (fun i => cutValue (q i))) (hzero : q ⟨0, hk⟩ = 0)
    (background : Fin M → α) (total : Nat) (labels : Option Nat → α)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background (repeatWord total (List.finRange k))
      labels (fun rank => q rank.rev) gap sweeps finalGap)
    (hnodup : (renderedBase background labels (fun rank => q rank.rev) gap).Nodup)
    (hlen : (renderedBase background labels (fun rank => q rank.rev) gap).length = M + k + 1)
    (hhead : ((StationaryCircle.render background (residents labels)
      (fun rank => q rank.rev)).rotateLeft gap).head? =
        some (residents (k := k) labels ⟨k - 1, by omega⟩))
    (satellite : α) :
    (scheduleRows satellite sweeps (renderedBase background labels (fun rank => q rank.rev) gap)).length =
        total * ((k - 1) * M + k * (k + 1) + 1) ∧
      ((scheduleRows satellite sweeps (renderedBase background labels (fun rank => q rank.rev) gap)).map
        Row.charge).sum = 2 * total * k ∧
      sweeps.sum = total * ((k - 1) * M + k * k + 1) := by
  have hlength : sweeps.length = total * k := by
    simpa only [length_repeatWord, List.length_finRange] using
      trace_length (show 0 < M by omega) background (repeatWord total (List.finRange k))
        labels (fun rank => q rank.rev) gap sweeps finalGap htrace
  have hcost : ∀ n, n < sweeps.length → movesAt sweeps n =
      normalCost q ⟨n % k, Nat.mod_lt n hk⟩ := by
    intro n hn
    exact actual_sweep hM hk q hmono hrobust hzero background total labels gap sweeps finalGap
      htrace hnodup hlen hhead n (by omega)
  have hsum := periodic_sweeps_sum k hk total sweeps (normalCost q) hlength hcost
  rw [normalCost_sum hk q hzero] at hsum
  refine ⟨?_, ?_, hsum⟩
  · rw [scheduleRows_length, hsum, hlength]
    ring
  · rw [RowValidity.scheduleRows_charge satellite sweeps _
      (trace_suffixSchedule hM background _ labels _ gap sweeps finalGap htrace)
      (by rw [hlen]; omega), hlength]
    ring

end CoefficientTwoPrecision.NormalExactCount

#print axioms CoefficientTwoPrecision.NormalExactCount.normalCost_sum
#print axioms CoefficientTwoPrecision.NormalExactCount.normal_counts
