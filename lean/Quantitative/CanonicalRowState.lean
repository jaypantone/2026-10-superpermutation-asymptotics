import Quantitative.OriginTransport
import Quantitative.ActualPrefix
import Quantitative.PhysicalJointStates
import Quantitative.RendererReindex
import Quantitative.SortedFrameSupply
import Quantitative.CollisionGeometry

/-!
# Physical states of the actual emitted rows

Every emitted row is reconstructed from its actual proper target prefix.
Reversing the descending engine indices gives the increasing physical
indices used by the collision catalogue. The safe origin remains in the
canonical time. The affine frame condition is proved from the selected
physical frame; it is not assumed as a field of a row witness.
-/

namespace CoefficientTwoPrecision.CanonicalRowState

open LiteralState StationaryCircle LiteralSchedule PositiveSchedule TargetTrace
open BatchSafety BatchPrefixes RobustMatching RobustSafety ActualCyclicMatching
open PhysicalJointStates OriginTransport FiniteRoles
open SuperpermutationUpperBound

variable {M d k : Nat} {Control α : Type} [NeZero M]

theorem hasFrame_of_physicalFrame (q : Fin (d + 2) → Fin M)
    (hq : q ∈ SortedFrameSupply.physicalFrames M d)
    (localCuts : Fin (d + 2) → Fin M) (time : Fin M)
    (phase : Fin (d + 2) → Fin 2)
    (hlocal : ∀ i, (localCuts i).val = ((q i).val + time.val + (phase i).val) % M) :
    CollisionGeometry.HasFrame localCuts := by
  obtain ⟨sumSlot, hsum, _, _, _, hrelation⟩ :=
    SortedFrameSupply.physicalFrame_properties q hq
  refine ⟨sumSlot, (fun i => ((q i).val : Int)), phase, (time.val : Int), hsum, ?_, ?_⟩
  · apply (ZMod.intCast_eq_intCast_iff _ _ M).mp
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero] using hrelation
  · intro i
    apply (ZMod.intCast_eq_intCast_iff _ _ M).mp
    simp only [Int.cast_natCast, Int.cast_add]
    rw [hlocal, ZMod.natCast_mod, Nat.cast_add, Nat.cast_add]

/-- Reversing the stationary indices changes neither the literal
rendered circle nor its distinguished mobile label. -/
theorem base_reverse (background : Fin M → α) (embed : Control → α)
    (assignment : Role k ≃ Control) (cuts : Fin k → Fin M)
    (hcuts : Function.Injective cuts) (gap : Nat) :
    ActualMatching.base background embed ((reverseRoles k).trans assignment)
        (fun i => cuts i.rev) gap =
      ActualMatching.base background embed assignment cuts gap := by
  have hresident : ActualMatching.resident embed ((reverseRoles k).trans assignment) =
      ActualMatching.resident embed assignment ∘ Fin.revPerm := by
    funext i
    rfl
  have hrender := RendererReindex.render_reindex background
    (ActualMatching.resident embed assignment) cuts hcuts Fin.revPerm
  simp only [ActualMatching.base, hresident, Equiv.trans_apply, reverseRoles_none]
  exact congrArg (fun word : List α => word.rotateLeft gap ++ [embed (assignment none)]) hrender

/-- The time and role assignment refer to the same actual target prefix.
The equality is literal, including the mobile letter and the chosen gap.
Consequently the result can be used directly with the physical collision
theorem, whose row bases use increasing stationary indices. -/
theorem actual_row_state (hM : 0 < M) (background : Fin M → α)
    (embed : Control → α) (assignment : Role (d + 2) ≃ Control)
    (q : Fin (d + 2) → Fin M) (hq : q ∈ SortedFrameSupply.physicalFrames M d)
    (origin : Fin M) (batches : List (List (Fin (d + 2))))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange (d + 2)))
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace hM (shiftedBackground background origin) batches.flatten
      (fun p => embed (lift assignment p)) (fun rank => q rank.rev) gap sweeps finalGap)
    (satellite : α) (row : Row α)
    (hrow : row ∈ scheduleRows satellite sweeps
      (renderedBase (shiftedBackground background origin) (fun p => embed (lift assignment p))
        (fun rank => q rank.rev) gap)) :
    ∃ n < batches.flatten.length, ∃ rowGap,
      ∃ localCuts : Fin (d + 2) → Fin M, ∃ time : Fin M,
      ∃ phase : Fin (d + 2) → Fin 2,
        row.base = ActualMatching.base background embed
          ((reverseRoles (d + 2)).trans (execute (batches.flatten.take n) assignment))
          localCuts rowGap ∧
        cutValue time = cutValue origin + (n / (d + 2) : Nat) ∧
        (∀ i, (localCuts i).val = ((q i).val + time.val + (phase i).val) % M) ∧
        CollisionGeometry.HasFrame localCuts ∧
        (batches.flatten.take n).length = n := by
  obtain ⟨pre, target, tail, rowGap, hword, hbase⟩ :=
    canonical_row_prefix hM background origin batches.flatten
      (fun p => embed (lift assignment p)) (fun rank => q rank.rev)
      gap sweeps finalGap htrace satellite row hrow
  have hn : pre.length < batches.flatten.length := by
    rw [hword, List.length_append, List.length_cons]
    omega
  have htake : batches.flatten.take pre.length = pre := by
    rw [hword]
    exact List.take_left
  let n := pre.length
  let engineCuts : Fin (d + 2) → Fin M :=
    fun i => executeCuts hM (batches.flatten.take n) (fun rank => q rank.rev) i + origin
  let localCuts : Fin (d + 2) → Fin M := fun i => engineCuts i.rev
  let translation : ZMod M := cutValue origin + (n / (d + 2) : Nat)
  let physicalPhases : Fin (d + 2) → Bool := fun i => prefixPhases batches n i.rev
  let time : Fin M := translationCut translation
  let phase : Fin (d + 2) → Fin 2 := fun i =>
    ⟨PhasedControlOrder.phaseNat (physicalPhases i), by
      have := PhasedControlOrder.phaseNat_le (physicalPhases i)
      omega⟩
  have htime : cutValue time = translation := translationCut_value translation
  have hrep : Represents (fun i => cutValue (q i)) translation physicalPhases localCuts := by
    intro i
    have h := canonical_prefix_time hM (by omega : 0 < d + 2) origin batches horders
      n (Nat.le_of_lt hn) (fun rank => q rank.rev) i.rev
    simpa only [engineCuts, localCuts, translation, physicalPhases, Fin.rev_rev,
      perturbed] using h
  obtain ⟨_, _, _, _, hrobust, _⟩ := SortedFrameSupply.physicalFrame_properties q hq
  have hphysicalInjective : Function.Injective localCuts := by
    intro i j heq
    apply perturbed_injective (fun a => cutValue (q a)) hrobust translation physicalPhases
    rw [← hrep i, ← hrep j, heq]
  have hengineInjective : Function.Injective engineCuts := by
    intro i j heq
    apply Fin.rev_injective
    apply hphysicalInjective
    simpa only [localCuts, Fin.rev_rev] using heq
  have hphase (i : Fin (d + 2)) : ((phase i).val : ZMod M) =
      (bit (physicalPhases i) : ZMod M) := by
    change (PhasedControlOrder.phaseNat (physicalPhases i) : ZMod M) = _
    cases physicalPhases i <;> simp [PhasedControlOrder.phaseNat, bit]
  have hlocal (i : Fin (d + 2)) :
      (localCuts i).val = ((q i).val + time.val + (phase i).val) % M := by
    have hcast : ((localCuts i).val : ZMod M) =
        (((q i).val + time.val + (phase i).val : Nat) : ZMod M) := by
      simp only [Nat.cast_add, hphase]
      change cutValue (localCuts i) = cutValue (q i) + cutValue time + _
      rw [htime]
      exact hrep i
    have hval := congrArg ZMod.val hcast
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (localCuts i).isLt] using hval
  refine ⟨n, hn, rowGap, localCuts, time, phase, ?_, htime, hlocal,
    hasFrame_of_physicalFrame q hq localCuts time phase hlocal, ?_⟩
  · rw [hbase, ActualPrefix.rendered_execute_eq]
    have hreverse := base_reverse background embed (execute (batches.flatten.take n) assignment)
      engineCuts hengineInjective rowGap
    rw [hreverse]
    simp only [engineCuts, n, htake]
  · exact List.length_take_of_le (Nat.le_of_lt hn)

end CoefficientTwoPrecision.CanonicalRowState

#print axioms CoefficientTwoPrecision.CanonicalRowState.hasFrame_of_physicalFrame
#print axioms CoefficientTwoPrecision.CanonicalRowState.base_reverse
#print axioms CoefficientTwoPrecision.CanonicalRowState.actual_row_state
