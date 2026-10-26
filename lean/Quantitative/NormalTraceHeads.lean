import Quantitative.NormalPrefixes
import Quantitative.TraceSteps
import Quantitative.ClosedTrace

/-!
# The actual resident head before every normal update

A completed short update puts the new resident at the head of the
stationary representative. Applying this fact to the actual prefix trace
identifies the head before the next update. At a batch boundary it is the
last engine rank, which is physical cut zero.
-/

namespace CoefficientTwoPrecision.NormalTraceHeads

open PositiveParking NormalPrefixes LiteralState StationaryCircle
open LiteralSchedule PositiveSchedule TargetTrace TraceComposition TraceSteps ClosedTrace

variable {M k : Nat} {α : Type}

def precedingRank (hk : 0 < k) (n : Nat) : Fin k :=
  if n % k = 0 then ⟨k - 1, by omega⟩ else ⟨n % k - 1, by have := Nat.mod_lt n hk; omega⟩

theorem predecessor_mod (hk : 0 < k) (n : Nat) (hn : 0 < n) :
    (n - 1) % k = (precedingRank hk n).val := by
  have hrem := Nat.mod_lt (n - 1) hk
  have hadd : ((n - 1) % k + 1) % k = n % k := by
    rw [Nat.mod_add_mod]
    congr 1
    omega
  unfold precedingRank
  by_cases hwrap : (n - 1) % k + 1 = k
  · rw [hwrap, Nat.mod_self] at hadd
    simp only [← hadd, ↓reduceIte, Fin.val_mk]
    omega
  · have hsmall : (n - 1) % k + 1 < k := by omega
    rw [Nat.mod_eq_of_lt hsmall] at hadd
    have hnonzero : n % k ≠ 0 := by omega
    simp only [if_neg hnonzero, Fin.val_mk]
    omega

theorem normal_prefix_last (hk : 0 < k) (total n : Nat)
    (hn : 0 < n) (hbound : n ≤ total * k) :
    ((repeatWord total (List.finRange k)).take n).getLast? = some (precedingRank hk n) := by
  have htarget := normal_target_at_index hk total (n - 1) (by omega)
  have hrank : (⟨(n - 1) % k, Nat.mod_lt (n - 1) hk⟩ : Fin k) = precedingRank hk n :=
    Fin.ext (predecessor_mod hk n hn)
  rw [hrank] at htarget
  rw [List.getLast?_take, if_neg (by omega), htarget]
  rfl

theorem prefix_base_head (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap n : Nat)
    (htrace : Trace hM background word labels cuts gap sweeps finalGap)
    (target : Fin k) (hlast : (word.take n).getLast? = some target) :
    (baseAt sweeps (renderedBase background labels cuts gap) n).dropLast.head? =
      some (residents (executeLabels (word.take n) labels) target) := by
  obtain ⟨middleGap, hfirst, _⟩ := trace_split hM background word labels cuts gap sweeps finalGap n htrace
  have hend := trace_endpoint hM background (word.take n) labels cuts gap (sweeps.take n) middleGap hfirst
  have hhead := trace_last_head hM background (word.take n) labels cuts gap
    (sweeps.take n) middleGap hfirst target hlast
  change (scheduleEnd (sweeps.take n) (renderedBase background labels cuts gap)).dropLast.head? = _
  rw [hend, renderedBase, List.dropLast_concat]
  exact hhead

/-- The initial head is the same physical-zero resident required at all
later normal batch boundaries. -/
theorem normal_base_head (hM : 0 < M) (hk : 0 < k)
    (background : Fin M → α) (total : Nat) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap n : Nat)
    (htrace : Trace hM background (repeatWord total (List.finRange k)) labels cuts gap sweeps finalGap)
    (hbound : n ≤ total * k)
    (hhead : ((render background (residents labels) cuts).rotateLeft gap).head? =
      some (residents (k := k) labels ⟨k - 1, by omega⟩)) :
    (baseAt sweeps (renderedBase background labels cuts gap) n).dropLast.head? =
      some (residents (executeLabels ((repeatWord total (List.finRange k)).take n) labels)
        (precedingRank hk n)) := by
  by_cases hn : n = 0
  · subst n
    simpa only [baseAt, List.take_zero, scheduleEnd, renderedBase, List.dropLast_concat,
      executeLabels, precedingRank, Nat.zero_mod, ↓reduceIte] using hhead
  · exact prefix_base_head hM background _ labels cuts gap sweeps finalGap n htrace
      (precedingRank hk n) (normal_prefix_last hk total n (by omega) hbound)

end CoefficientTwoPrecision.NormalTraceHeads

#print axioms CoefficientTwoPrecision.NormalTraceHeads.normal_base_head
