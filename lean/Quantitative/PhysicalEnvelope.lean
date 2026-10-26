import Quantitative.EnvelopeDegree
import Quantitative.PhysicalJointStates
import Quantitative.RendererReindex

/-!
# The constructed literal envelope is the counted physical envelope

The schedule is indexed in descending normal-order ranks, while the frame
degree theorem uses increasing physical cuts. This theorem converts the
actual rendered base between those conventions, keeping the role action
and binary phases attached to the same joint catalogue index.
-/

namespace CoefficientTwoPrecision.PhysicalEnvelope

open FiniteRoles JointStates BatchSafety StationaryCircle LiteralSchedule TargetTrace
open ActualCyclicMatching EnvelopeDegree RobustMatching RobustSafety

theorem literal_mem {M d : Nat} [NeZero M] {α : Type} [DecidableEq α]
    (background : Fin M → α) (embed : FiniteRoles.Role (d + 2) → α)
    (initial : Equiv.Perm (FiniteRoles.Role (d + 2))) (q : Fin (d + 2) → Fin M)
    (hrobust : Robust (fun i => cutValue (q i))) (source : List α)
    (hsource : LiteralEnvelope.Envelope background
      (fun p => embed (FiniteRoles.lift ((PhysicalJointStates.reverseRoles (d + 2)).trans initial) p))
      (fun i => q i.rev) source) :
    ∃ index : Index (d + 2), ∃ translation : ZMod M, ∃ gap : Nat,
      source = EnvelopeDegree.row background embed (PhysicalJointStates.action (d + 2))
        (PhysicalJointStates.phase (d + 2)) (q, initial) index translation gap := by
  classical
  obtain ⟨state, hstate, translation, cuts, gap, hbase, hcuts⟩ := hsource
  obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hstate
  let labels : Option Nat → α := fun p => embed (FiniteRoles.lift
    ((PhysicalJointStates.reverseRoles (d + 2)).trans initial)
      ((interpret (d + 2) (List.range (d + 2)) index).labels p))
  let physicalCuts := phaseCuts q (translation : ZMod M) (PhysicalJointStates.phase (d + 2) index)
  have hvalues (i : Fin (d + 2)) :
      cutValue (cuts i.rev) = cutValue (q i) + (translation : ZMod M) +
        (bit (PhysicalJointStates.phase (d + 2) index i) : ZMod M) := by
    unfold cutValue
    rw [hcuts i.rev]
    simp only [Fin.rev_rev, ZMod.natCast_mod, Nat.cast_add]
    rw [PhysicalJointStates.phase_value]
  have hreindex : cuts ∘ Fin.revPerm = physicalCuts := by
    funext i
    apply cutValue_injective
    change cutValue (cuts i.rev) = cutValue (physicalCuts i)
    rw [hvalues]
    exact (phaseCuts_represents q (translation : ZMod M)
      (PhysicalJointStates.phase (d + 2) index) i).symm
  have hphysicalInj : Function.Injective physicalCuts := by
    intro i j hij
    apply perturbed_injective (fun i => cutValue (q i)) hrobust
      (translation : ZMod M) (PhysicalJointStates.phase (d + 2) index)
    have h := congrArg cutValue hij
    rw [phaseCuts_represents q (translation : ZMod M) (PhysicalJointStates.phase (d + 2) index) i,
      phaseCuts_represents q (translation : ZMod M) (PhysicalJointStates.phase (d + 2) index) j] at h
    exact h
  have hcutInj : Function.Injective cuts := by
    intro i j hij
    apply Fin.rev_injective
    apply hphysicalInj
    rw [← hreindex]
    simpa only [Function.comp_apply, Fin.revPerm_apply, Fin.rev_rev] using hij
  have hresidents : residents labels ∘ Fin.revPerm =
      ActualMatching.resident embed ((PhysicalJointStates.action (d + 2) index).trans initial) := by
    funext i
    exact congrArg embed (PhysicalJointStates.stationary_label index initial i)
  have hmobile : labels none = embed (((PhysicalJointStates.action (d + 2) index).trans initial) none) :=
    congrArg embed (PhysicalJointStates.mobile_label index initial)
  have hrender := RendererReindex.render_reindex background (residents labels) cuts hcutInj Fin.revPerm
  rw [hreindex, hresidents] at hrender
  refine ⟨index, (translation : ZMod M), gap, ?_⟩
  change source = (render background
    (ActualMatching.resident embed ((PhysicalJointStates.action (d + 2) index).trans initial))
      physicalCuts).rotateLeft gap ++ [embed (((PhysicalJointStates.action (d + 2) index).trans initial) none)]
  change source = (render background (residents labels) cuts).rotateLeft gap ++ [labels none] at hbase
  rw [hrender, ← hmobile]
  exact hbase

end CoefficientTwoPrecision.PhysicalEnvelope

#print axioms CoefficientTwoPrecision.PhysicalEnvelope.literal_mem
