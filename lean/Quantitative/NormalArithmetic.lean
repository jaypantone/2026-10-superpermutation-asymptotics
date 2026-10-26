import Quantitative.NormalPrefixes
import Quantitative.TraceSteps
import Quantitative.RowValidity

/-!
# Telescoping the actual normal sweeps

The descending cuts give a cancellation equation at every sweep after
the first. Writing that equation without truncated subtraction makes the
finite sum transparent. A periodic list of actual sweep lengths then has
the claimed exact row count, and its original rows have charge two per
target update.
-/

namespace CoefficientTwoPrecision.NormalArithmetic

open PositiveParking NormalPrefixes LiteralSchedule TraceSteps

theorem telescope (s p : Nat → Nat) (C n : Nat)
    (hstep : ∀ i < n, s (i + 1) + p i = C + p (i + 1)) :
    ((List.range n).map (fun i => s (i + 1))).sum + p 0 = n * C + p n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprevious := ih (fun i hi => hstep i (by omega))
    have hlast := hstep n (by omega)
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [Nat.succ_mul]
    omega

/-- One descending normal batch has this exact number of full moves. -/
theorem batch_sum (M k : Nat) (hk : 0 < k) (s p : Nat → Nat)
    (hfirst : s 0 = p 0 + k + 1) (hlast : p (k - 1) = 0)
    (hstep : ∀ i, i + 1 < k → s (i + 1) + p i = M + k + p (i + 1)) :
    ((List.range k).map s).sum = (k - 1) * M + k * k + 1 := by
  cases k with
  | zero => omega
  | succ n =>
    have ht := telescope s p (M + (n + 1)) n (fun i hi => hstep i (by omega))
    simp only [Nat.add_sub_cancel] at hlast
    rw [hlast] at ht
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def]
    rw [hfirst]
    simp only [Nat.add_sub_cancel]
    nlinarith

theorem sum_repeatWord (total : Nat) (word : List Nat) :
    (repeatWord total word).sum = total * word.sum := by
  induction total with
  | zero => simp [repeatWord]
  | succ total ih =>
    simp only [repeatWord, List.sum_append, ih, Nat.succ_mul]
    omega

/-- A pointwise period on the actual indexed sweep list determines that
list, including every repeated occurrence. -/
theorem sweeps_eq_periodic (k : Nat) (hk : 0 < k) (total : Nat)
    (sweeps : List Nat) (cost : Fin k → Nat)
    (hlength : sweeps.length = total * k)
    (hcost : ∀ n, n < sweeps.length →
      movesAt sweeps n = cost ⟨n % k, Nat.mod_lt n hk⟩) :
    sweeps = (repeatWord total (List.finRange k)).map cost := by
  apply List.ext_getElem
  · simp only [List.length_map, length_repeatWord, List.length_finRange, hlength]
  · intro i hi hj
    have hleft : movesAt sweeps i = sweeps[i] := by
      simp only [movesAt, List.getElem?_eq_getElem hi, Option.getD_some]
    have hright := normal_target_at_index hk total i (by omega)
    rw [List.getElem?_eq_getElem (by
      simpa only [length_repeatWord, List.length_finRange] using (show i < total * k by omega))] at hright
    have htarget := Option.some.inj hright
    rw [List.getElem_map, htarget, ← hleft]
    exact hcost i hi

theorem periodic_sweeps_sum (k : Nat) (hk : 0 < k) (total : Nat)
    (sweeps : List Nat) (cost : Fin k → Nat)
    (hlength : sweeps.length = total * k)
    (hcost : ∀ n, n < sweeps.length →
      movesAt sweeps n = cost ⟨n % k, Nat.mod_lt n hk⟩) :
    sweeps.sum = total * ((List.finRange k).map cost).sum := by
  rw [sweeps_eq_periodic k hk total sweeps cost hlength hcost,
    NormalContour.repeatWord_map, sum_repeatWord]

end CoefficientTwoPrecision.NormalArithmetic

#print axioms CoefficientTwoPrecision.NormalArithmetic.batch_sum
#print axioms CoefficientTwoPrecision.NormalArithmetic.periodic_sweeps_sum
