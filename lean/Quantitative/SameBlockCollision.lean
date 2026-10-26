import Quantitative.PhysicalOldCuts
import Quantitative.GuardCount

/-!
# Collisions on one active block determine the guard background

Delete every active letter from an actual cyclic source row. The remaining
word is precisely its guard background, up to rotation. Reconstruction of
the original guard cuts then distinguishes all backgrounds on one block.
-/

namespace CoefficientTwoPrecision.SameBlockCollision

open GuardCatalogue GridBackground PhysicalOldCuts GuardBackgrounds
open StationaryCircle StationaryUpdate OldCircleProjection CutExtraction
open SuperpermutationUpperBound

variable {m d A : Nat} {α : Type} [DecidableEq α]
variable (hA : 0 < A) (old : Fin m → α) (ho : Function.Injective old)
variable (label : Physical d A → α) (hl : Function.Injective label)
variable (hcross : ∀ p i, label p ≠ old i)

noncomputable def keepInactive (active : Active d A) (symbol : α) : Bool := by
  classical
  exact decide (∀ i : Fin (d + 3), symbol ≠ label (activeControl d A hA active i))

theorem keep_active (active : Active d A) (i : Fin (d + 3)) :
    keepInactive hA label active (label (activeControl d A hA active i)) = false := by
  classical
  apply decide_eq_false_iff_not.mpr
  intro hall
  exact hall i rfl

include hcross in
theorem keep_old (active : Active d A) (j : Fin m) :
    keepInactive hA label active (old j) = true := by
  classical
  apply decide_eq_true_eq.mpr
  intro i hij
  exact hcross _ j hij.symm

include hl in
theorem keep_guard (active : Active d A) (j : Fin (guardNumber d A)) :
    keepInactive hA label active (label (guardLabel d A hA active j)) = true := by
  classical
  apply decide_eq_true_eq.mpr
  intro i hij
  exact activeControl_ne_guardLabel d A hA active i j (hl hij).symm

include hl hcross in
theorem guard_filter (active : Active d A) (cuts : Fin (guardNumber d A) → Fin m) :
    (guardWord hA old label active cuts).filter (keepInactive hA label active) =
      guardWord hA old label active cuts := by
  apply List.filter_eq_self.mpr
  intro symbol hsymbol
  rcases (mem_render old (fun j => label (guardLabel d A hA active j)) cuts symbol).mp hsymbol with
    ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact keep_old hA old label hcross active j
  · exact keep_guard hA label hl active j

theorem row_projection (active : Active d A)
    (guardCuts : Fin (guardNumber d A) → Fin m)
    (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localCuts : Fin (d + 2) → Fin (m + guardNumber d A)) (gap : Nat) :
    ((rowBase hA old ho label hl hcross active guardCuts role localCuts gap).filter
      (keepInactive hA label active)).IsRotated (guardWord hA old label active guardCuts) := by
  let keep := keepInactive hA label active
  let bg := background hA old ho label hl hcross active guardCuts
  let embed := fun i => label (activeControl d A hA active i)
  have hr : ∀ j, keep (ActualMatching.resident embed role j) = false :=
    fun j => keep_active hA label active (role (some j))
  have hm : keep (embed (role none)) = false := keep_active hA label active (role none)
  have h := mobile_projection (render bg (ActualMatching.resident embed role) localCuts)
    (embed (role none)) gap keep hm
  rw [all_residents_filter bg _ localCuts keep hr] at h
  rw [background_word hA old ho label hl hcross active guardCuts] at h
  have hfilter : (render old (fun j => label (guardLabel d A hA active j)) guardCuts).filter keep =
      guardWord hA old label active guardCuts := guard_filter hA old label hl hcross active guardCuts
  rw [hfilter] at h
  exact h

theorem background_injective (active : Active d A)
    (cuts : Fin (guardNumber d A) → Fin m) :
    Function.Injective (background hA old ho label hl hcross active cuts) := by
  have hnd := render_nodup old (fun j => label (guardLabel d A hA active j)) cuts
    ho (hl.comp (guardLabel_injective d A hA active)) (fun j i => hcross _ i)
  intro i j hij
  apply Fin.ext
  exact hnd.getElem_inj_iff.mp hij

theorem guard_cuts_eq (hm : 0 < m) (active : Active d A)
    (first second : Fin (guardNumber d A) → Fin m)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (hcyclic : (rowBase hA old ho label hl hcross active first roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross active second roleR localR gapR)) : first = second := by
  have hleft := row_projection hA old ho label hl hcross active first roleL localL gapL
  have hright := row_projection hA old ho label hl hcross active second roleR localR gapR
  have hrot := hleft.symm.trans ((filter_isRotated _ _ (keepInactive hA label active) hcyclic).trans hright)
  have hlen : 0 < (guardWord hA old label active first).length := by
    rw [guardWord_length hA old ho label hl hcross active first]
    omega
  have hcyc : CyclicEq (guardWord hA old label active first) (guardWord hA old label active second) := by
    obtain ⟨n, hn⟩ := hrot
    refine ⟨⟨n % _, Nat.mod_lt _ hlen⟩, ?_⟩
    change rot _ (n % _) = _
    rw [rot_mod]
    change (guardWord hA old label active first).rotateLeft n = _
    rwa [LiteralState.rotateLeft_eq_rotate]
  exact cuts_eq_of_cyclicEq old (fun j => label (guardLabel d A hA active j))
    ho (hl.comp (guardLabel_injective d A hA active)) (fun j i => hcross _ i) first second hcyc

end CoefficientTwoPrecision.SameBlockCollision

#print axioms CoefficientTwoPrecision.SameBlockCollision.background_injective
#print axioms CoefficientTwoPrecision.SameBlockCollision.guard_cuts_eq
