import Quantitative.BatchSafety
import Quantitative.ScheduleEndpoint

/-!
# Actual closed contours from complete positive batches

Every source row is a literal `Row`; the row list is constructed by the
positive-update renderer. Robustness supplies update safety, and the
endpoint proof uses the last resident as well as the returned role and cut
data. Source cyclic-class simplicity and the quantitative normal row count
remain separate obligations.
-/

namespace CoefficientTwoPrecision.ClosedPositive

open JointStates LiteralState StationaryCircle StationaryUpdate
open StationarySuccessor LiteralSchedule LiteralTrail PositiveSchedule ScheduleEndpoint
open RobustMatching BatchSafety
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type}

/-- Choose the literal starting gap immediately before the designated
last target's resident. -/
theorem initial_gap_exists (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (target : Fin k) :
    ∃ gap : Nat, ((render background resident cuts).rotateLeft gap).head? =
      some (resident target) := by
  have hmem : resident target ∈ render background resident cuts :=
    (mem_render background resident cuts _).mpr (Or.inr ⟨target, rfl⟩)
  obtain ⟨gap, hgap, hsymbol⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨gap, ?_⟩
  rw [LiteralState.rotateLeft_eq_rotate, List.head?_rotate hgap,
    List.getElem?_eq_getElem hgap, hsymbol]

/-- Complete robust batches with returning role and cut data give an
actual nonempty literally closed row contour. The target-word hypotheses
are explicit algebraic statements, not assumed contour-existence fields. -/
theorem closed_complete_batches (hM : 2 ≤ M) (background : Fin M → α)
    (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (hbackground : Function.Injective background)
    (hresident : Function.Injective (residents (k := k) labels))
    (hcross : ∀ (j : Fin k) (i : Fin M), residents labels j ≠ background i)
    (hrobust : Robust (fun j => cutValue (cuts j)))
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (hcounts : ∀ j, batches.flatten.count j = M)
    (hlabels : executeLabels batches.flatten labels = labels)
    (lastTarget : Fin k) (hlast : batches.flatten.getLast? = some lastTarget)
    (satellite : α) :
    ∃ sweeps : List Nat, ∃ base : List α,
      sweeps.length = batches.flatten.length ∧
      SuffixSchedule sweeps base ∧
      scheduleEnd sweeps base = base ∧
      ClosedTrail (scheduleRows satellite sweeps base) := by
  have hcuts : Function.Injective cuts := by
    intro i j hij
    apply robust_injective _ hrobust
    exact congrArg cutValue hij
  have hrep : Represents (fun j => cutValue (cuts j)) 0 (fun _ => false) cuts := by
    intro j
    simp [RobustSafety.perturbed, bit]
  have hsafe := complete_batches_safe hM (fun j => cutValue (cuts j)) hrobust
    batches horders 0 cuts hrep
  obtain ⟨gap, hgap⟩ := initial_gap_exists background (residents labels) cuts lastTarget
  obtain ⟨sweeps, finalGap, hlength, hvalid, hend, hhead⟩ :=
    realize_targets_with_head hM background batches.flatten labels cuts hcuts gap hsafe
  have hcutReturn := executeCuts_closed (show 0 < M by omega) batches.flatten cuts hcounts
  have hfinalHead : ((render background (residents labels) cuts).rotateLeft finalGap).head? =
      some (residents labels lastTarget) := by
    simpa only [hlabels, hcutReturn] using hhead lastTarget hlast
  have hnodup := render_nodup background (residents labels) cuts hbackground hresident hcross
  have hne : render background (residents labels) cuts ≠ [] := by
    have hlen := render_length_ge_background background (residents labels) cuts
    intro hnil
    simp [hnil] at hlen
    omega
  have hbaseEq := post_update_base_unique (render background (residents labels) cuts)
    hnodup hne (labels none) (residents labels lastTarget) finalGap gap hfinalHead hgap
  have hclosed : scheduleEnd sweeps
      ((render background (residents labels) cuts).rotateLeft gap ++ [labels none]) =
      (render background (residents labels) cuts).rotateLeft gap ++ [labels none] := by
    rw [hend, hlabels, hcutReturn]
    exact hbaseEq
  have hwordNe : batches.flatten ≠ [] := by
    intro hnil
    simp [hnil] at hlast
  have hsweepsNe : sweeps ≠ [] := by
    intro hnil
    have hzero : batches.flatten.length = 0 := by simpa [hnil] using hlength.symm
    exact hwordNe (List.length_eq_zero_iff.mp hzero)
  exact ⟨sweeps, (render background (residents labels) cuts).rotateLeft gap ++ [labels none],
    hlength, hvalid, hclosed, scheduleRows_closed satellite sweeps _ hsweepsNe hvalid hclosed⟩

end CoefficientTwoPrecision.ClosedPositive

#print axioms CoefficientTwoPrecision.ClosedPositive.initial_gap_exists
#print axioms CoefficientTwoPrecision.ClosedPositive.closed_complete_batches
