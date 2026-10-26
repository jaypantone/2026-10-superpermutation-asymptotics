import Quantitative.NormalPrefixes
import Quantitative.PhasedControlOrder
import Quantitative.ActualCyclicMatching
import Quantitative.RendererReindex

/-!
# Exact physical cut vector during the actual normal word

Engine rank j denotes physical slot rev(j). The current physical cut is
the initial cut plus its binary normal-prefix phase, followed by the
common batch translation. The unshifted phased vector remains strictly
increasing, so the exact translated-renderer offset theorem applies.
-/

namespace CoefficientTwoPrecision.NormalCuts

open PositiveParking LiteralSchedule NormalPrefixes RobustMatching BatchSafety
open PhasedControlOrder ActualCyclicMatching

variable {M k : Nat} [NeZero M]

def normalPhase (ell : Nat) (i : Fin k) : Bool := decide (i.rev.val < ell)

@[simp] theorem normalPhase_rank (ell : Nat) (rank : Fin k) :
    normalPhase ell rank.rev = decide (rank.val < ell) := by simp [normalPhase]

theorem normalPhase_zero : normalPhase (k := k) 0 = fun _ => false := by
  funext i
  simp [normalPhase]

theorem normal_cut_value (hM : 0 < M) (hk : 0 < k) (total n : Nat) (hn : n < total * k)
    (q : Fin k → Fin M) (i : Fin k) :
    cutValue (executeCuts hM ((repeatWord total (List.finRange k)).take n) (fun rank => q rank.rev) i.rev) =
      cutValue (q i) + (n / k : Nat) + (bit (normalPhase (n % k) i) : ZMod M) := by
  unfold cutValue
  rw [executeCuts_count, normal_count_at_index hk total n hn i.rev]
  simp only [Fin.rev_rev, ZMod.natCast_mod, Nat.cast_add]
  by_cases hphase : i.rev.val < n % k
  · simp only [normalPhase, hphase, decide_true, bit, ite_true, Nat.cast_one, Int.cast_one, add_assoc]
  · simp only [normalPhase, hphase, decide_false, bit, ite_false, Nat.cast_zero, Int.cast_zero, add_zero]

/-- This is equality of the actual finite cuts, not only congruence of
abstract phase coordinates. -/
theorem normal_cuts_physical (hM : 2 ≤ M) (hk : 0 < k) (total n : Nat) (hn : n < total * k)
    (q : Fin k → Fin M) (hrobust : Robust (fun i => cutValue (q i)))
    (zeroSlot : Fin k) (hzero : q zeroSlot = 0) :
    (fun i => executeCuts (show 0 < M by omega)
      ((repeatWord total (List.finRange k)).take n) (fun rank => q rank.rev) i.rev) =
      fun i => phased hM q hrobust zeroSlot hzero (normalPhase (n % k)) i +
        translationCut ((n / k : Nat) : ZMod M) := by
  funext i
  apply cutValue_injective
  rw [normal_cut_value (by omega) hk total n hn q i, cutValue_add, phased_value, translationCut_value]
  ring

theorem phased_rank_value (hM : 2 ≤ M) (q : Fin k → Fin M)
    (hrobust : Robust (fun i => cutValue (q i))) (zeroSlot : Fin k)
    (hzero : q zeroSlot = 0) (ell : Nat) (rank : Fin k) :
    (phased hM q hrobust zeroSlot hzero (normalPhase ell) rank.rev).val =
      (q rank.rev).val + if rank.val < ell then 1 else 0 := by
  simp only [phased, normalPhase_rank, phaseNat]
  split <;> simp_all

theorem target_phase_value (hM : 2 ≤ M) (q : Fin k → Fin M)
    (hrobust : Robust (fun i => cutValue (q i))) (zeroSlot : Fin k)
    (hzero : q zeroSlot = 0) (ell : Nat) (hell : ell < k) :
    (phased hM q hrobust zeroSlot hzero (normalPhase ell) (⟨ell, hell⟩ : Fin k).rev).val =
      (q (⟨ell, hell⟩ : Fin k).rev).val := by
  rw [phased_rank_value]
  simp

theorem previous_phase_value (hM : 2 ≤ M) (q : Fin k → Fin M)
    (hrobust : Robust (fun i => cutValue (q i))) (zeroSlot : Fin k)
    (hzero : q zeroSlot = 0) (ell : Nat) (hell : ell < k) (hpos : 0 < ell) :
    (phased hM q hrobust zeroSlot hzero (normalPhase ell)
      (⟨ell - 1, by omega⟩ : Fin k).rev).val =
        (q (⟨ell - 1, by omega⟩ : Fin k).rev).val + 1 := by
  rw [phased_rank_value, if_pos (by change ell - 1 < ell; omega)]

end CoefficientTwoPrecision.NormalCuts

#print axioms CoefficientTwoPrecision.NormalCuts.normal_cuts_physical
