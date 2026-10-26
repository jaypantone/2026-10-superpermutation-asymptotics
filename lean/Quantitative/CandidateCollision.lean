import Quantitative.CollisionToPrimary
import Quantitative.ProximitySurvivors
import Quantitative.SameBlockCollision

/-!
# Collision exclusion for two different surviving candidates

For a common active block, cyclic equality first identifies the guard
background. The fixed literal packing then distinguishes the selected
nodes. For distinct blocks, literal projection produces a primary event
at the current row's actual batch time, contradicting its repaired role
assignment. No global cyclic-distinctness hypothesis is used.
-/

namespace CoefficientTwoPrecision.CandidateCollision

open GuardCatalogue GridBackground PhysicalOldCuts NeighbourGeometry CollisionGeometry
open CandidateSpace LabelledReconstruction PrimaryCatalogue ProximitySurvivors

variable {m d A : Nat} {α : Type} [DecidableEq α]
variable (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A)
variable (old : Fin m → α) (ho : Function.Injective old)
variable (label : Physical d A → α) (hl : Function.Injective label)
variable (hcross : ∀ p i, label p ≠ old i)

include hm hd

/-- The avoidance premise is the local conclusion required from the
actual repaired program. All global collision cases are proved here. -/
theorem actual_rows_disjoint
    (rowIndex : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hpacking : ∀ (bg : Fin (m + guardNumber d A) → α)
        (embed : FiniteRoles.Role (d + 2) → α),
      Function.Injective bg → Function.Injective embed →
      (∀ i c, bg i ≠ embed c) →
      ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
        ∀ first second : List α, LiteralPacking.InEnvelope bg embed source first →
          LiteralPacking.InEnvelope bg embed target second → ¬ first.IsRotated second)
    (first second : Candidate m d A)
    (hfirst : first ∈ survivors m d A hA S) (hsecond : second ∈ survivors m d A hA S)
    (hne : first ≠ second)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (hframeL : HasFrame localL) (hframeR : HasFrame localR)
    (time : Fin (m + guardNumber d A)) (phase : Fin (d + 2) → Fin 2)
    (hlocal : ∀ j, (localL j).val =
      ((first.2.2.1 j).val + time.val + (phase j).val) % (m + guardNumber d A))
    (henvelopeL : LiteralPacking.InEnvelope
      (background hA old ho label hl hcross first.1 first.2.1)
      (fun c => label (activeControl d A hA first.1 (rowIndex c))) first.2.2
      (rowBase hA old ho label hl hcross first.1 first.2.1 roleL localL gapL))
    (henvelopeR : LiteralPacking.InEnvelope
      (background hA old ho label hl hcross second.1 second.2.1)
      (fun c => label (activeControl d A hA second.1 (rowIndex c))) second.2.2
      (rowBase hA old ho label hl hcross second.1 second.2.1 roleR localR gapR))
    (havoid : ∀ event : Event d A hA first.1,
      time ∈ times m hA first.1 first.2.1 first.2.2.1 event →
      roleL (some (slot hA first.1 event)) ≠ (shared hA first.1 event.1).1) :
    ¬ (rowBase hA old ho label hl hcross first.1 first.2.1 roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross second.1 second.2.1 roleR localR gapR) := by
  classical
  rcases first with ⟨active, cuts, node⟩
  rcases second with ⟨foreignBlock, foreignCuts, foreignNode⟩
  obtain ⟨hnode, hgood, hnot⟩ := (mem_survivors hA S _).mp hfirst
  obtain ⟨hforeignNode, hforeignGood, hforeignNot⟩ := (mem_survivors hA S _).mp hsecond
  intro hcyclic
  by_cases hactive : foreignBlock = active
  · subst foreignBlock
    have hcuts : cuts = foreignCuts := DFunLike.coe_injective
      (SameBlockCollision.guard_cuts_eq hA old ho label hl hcross hm active
        cuts foreignCuts roleL roleR localL localR gapL gapR hcyclic)
    subst foreignCuts
    have hnodeNe : node ≠ foreignNode := by
      intro he
      apply hne
      exact Prod.ext rfl (Prod.ext rfl he)
    exact hpacking (background hA old ho label hl hcross active cuts)
      (fun c => label (activeControl d A hA active (rowIndex c)))
      (SameBlockCollision.background_injective hA old ho label hl hcross active cuts)
      (hl.comp ((activeControl_injective d A hA active).comp rowIndex.injective))
      (fun i c => (active_ne_background hA old ho label hl hcross active cuts (rowIndex c) i).symm)
      node hnode foreignNode hforeignNode hnodeNe _ _ henvelopeL henvelopeR hcyclic
  · have hneighbour := neighbour_of_collision hm hd hA old ho label hl hcross
      active foreignBlock hactive cuts foreignCuts hgood roleL roleR localL localR gapL gapR
      hframeR hcyclic
    let foreign : Neighbour d A hA active := ⟨foreignBlock, hneighbour⟩
    obtain ⟨event, hforeign, hcontrol, htime⟩ := CollisionToPrimary.collision_event hm hd hA
      old ho label hl hcross active foreign cuts foreignCuts hgood hforeignGood roleL roleR
      localL localR gapL gapR hframeL hframeR node.1 time phase hlocal hcyclic
    have hrow : roleL (some (slot hA active event)) = (shared hA active event.1).1 := by
      rw [hforeign]
      exact congrArg Prod.fst hcontrol
    exact havoid event htime hrow

end CoefficientTwoPrecision.CandidateCollision

#print axioms CoefficientTwoPrecision.CandidateCollision.actual_rows_disjoint
