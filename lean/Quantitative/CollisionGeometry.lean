import Quantitative.PhysicalOldCuts
import Quantitative.PhysicalGuardExclusion
import Quantitative.GuardCollisionProjection
import Quantitative.NeighbourGeometry

/-!
# A surviving cross-block collision has one shared stationary control

The frame predicate records the actual local cuts, binary phases, common
translation, and the explicit stationary affine relation. Guard-only
collision exclusion first forces neighbouring blocks. Applying it in
both directions then shows that neither mobile can be the shared control.
-/

namespace CoefficientTwoPrecision.CollisionGeometry

open ActiveGrid GuardCatalogue GridBackground NeighbourGeometry PhysicalOldCuts
open GuardCollisionProjection

def HasFrame {M d : Nat} (cuts : Fin (d + 2) → Fin M) : Prop :=
  ∃ sumSlot : Fin (d + 2), ∃ q : Fin (d + 2) → Int,
    ∃ phase : Fin (d + 2) → Fin 2, ∃ t : Int,
      sumSlot ≠ 0 ∧
      Int.ModEq (M : Int) (∑ i, AffineReconstruction.frameWeight d sumSlot i * q i) 0 ∧
      ∀ i, Int.ModEq (M : Int) (cuts i).val (q i + t + (phase i).val)

variable {m d A : Nat} {α : Type} [DecidableEq α]
variable (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A)
variable (old : Fin m → α) (ho : Function.Injective old)
variable (label : Physical d A → α) (hl : Function.Injective label)
variable (hcross : ∀ p i, label p ≠ old i)

include hm hd

theorem no_collision_of_allGuards (active foreign : Active d A)
    (guardCutsL guardCutsR : Fin (guardNumber d A) ↪ Fin m)
    (hgood : guardCutsL ∈ goodEmbeddings m d A hA active)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (hguards : AllGuards d A hA active foreign (roleR none)) (hframe : HasFrame localR) :
    ¬ (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign guardCutsR roleR localR gapR) := by
  obtain ⟨sumSlot, q, phase, t, hsum, hq, hlocal⟩ := hframe
  exact PhysicalGuardExclusion.no_guard_only_collision hm hd hA old ho label hl hcross
    active foreign guardCutsL guardCutsR hgood roleL roleR localL localR gapL gapR hguards
    sumSlot hsum q phase t hq hlocal

theorem neighbour_of_collision (active foreign : Active d A) (hne : foreign ≠ active)
    (guardCutsL guardCutsR : Fin (guardNumber d A) ↪ Fin m)
    (hgood : guardCutsL ∈ goodEmbeddings m d A hA active)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (hframe : HasFrame localR)
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign guardCutsR roleR localR gapR)) :
    foreign ∈ ActiveIncidence.neighbours (d + 3) A (by omega) hA active := by
  classical
  by_contra hn
  have hdisjoint : Disjoint (activeBlock (d + 3) A (by omega) hA active)
      (activeBlock (d + 3) A (by omega) hA foreign) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpf
    apply hn
    exact (ActiveIncidence.mem_neighbours (d + 3) A (by omega) hA active foreign).mpr
      ⟨hne, p, Finset.mem_inter.mpr ⟨hp, hpf⟩⟩
  have hguards := allGuards_of_disjoint d A hA active foreign (roleR none) hdisjoint
  exact no_collision_of_allGuards hm hd hA old ho label hl hcross active foreign
    guardCutsL guardCutsR hgood roleL roleR localL localR gapL gapR hguards hframe hcyclic

theorem foreign_mobile_not_shared (active : Active d A) (foreign : Neighbour d A hA active)
    (guardCutsL guardCutsR : Fin (guardNumber d A) ↪ Fin m)
    (hgood : guardCutsL ∈ goodEmbeddings m d A hA active)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (hframe : HasFrame localR)
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign.val guardCutsR roleR localR gapR)) :
    roleR none ≠ (shared hA active foreign).1 := by
  intro he
  have hmobile : activeControl d A hA foreign.val (roleR none) ∈
      activeBlock (d + 3) A (by omega) hA active := by
    rw [he, shared_in_foreign_row]
    exact (Finset.mem_inter.mp (shared_mem hA active foreign)).1
  have hguards := allGuards_of_shared_mobile d A hA active foreign.val
    (neighbour_ne hA active foreign).symm (roleR none) hmobile
  exact no_collision_of_allGuards hm hd hA old ho label hl hcross active foreign.val
    guardCutsL guardCutsR hgood roleL roleR localL localR gapL gapR hguards hframe hcyclic

theorem current_mobile_not_shared (active : Active d A) (foreign : Neighbour d A hA active)
    (guardCutsL guardCutsR : Fin (guardNumber d A) ↪ Fin m)
    (hgood : guardCutsR ∈ goodEmbeddings m d A hA foreign.val)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (hframe : HasFrame localL)
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign.val guardCutsR roleR localR gapR)) :
    roleL none ≠ (shared hA active foreign).1 := by
  intro he
  have hmobile : activeControl d A hA active (roleL none) ∈
      activeBlock (d + 3) A (by omega) hA foreign.val := by
    rw [he, shared_in_current_row]
    exact (Finset.mem_inter.mp (shared_mem hA active foreign)).2
  have hguards := allGuards_of_shared_mobile d A hA foreign.val active
    (neighbour_ne hA active foreign) (roleL none) hmobile
  exact no_collision_of_allGuards hm hd hA old ho label hl hcross foreign.val active
    guardCutsR guardCutsL hgood roleR roleL localR localL gapR gapL hguards hframe hcyclic.symm

end CoefficientTwoPrecision.CollisionGeometry

#print axioms CoefficientTwoPrecision.CollisionGeometry.neighbour_of_collision
#print axioms CoefficientTwoPrecision.CollisionGeometry.foreign_mobile_not_shared
#print axioms CoefficientTwoPrecision.CollisionGeometry.current_mobile_not_shared
