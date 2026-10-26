import Quantitative.GridBackground
import Quantitative.CrossBackgroundProjection
import Quantitative.StationaryWeightTransport

/-!
# Actual cross-background collision exclusion after guard-only deletion

Both rows below use canonical guard backgrounds and genuine bijective
physical role assignments. The foreign frame relation is stated on the
foreign row's own local cuts. All one-control filters are the canonical
predicate retaining the common old alphabet and that physical control.
Their values follow from grid membership and label injectivity. Thus no
coordinate-identification or filter table is assumed in the conclusion.
-/

namespace CoefficientTwoPrecision.PhysicalGuardExclusion

open ActiveGrid GuardCatalogue GridBackground GuardBackgrounds
open StationaryCircle StationaryRelations StationaryWeightTransport
open CrossBackgroundProjection

variable {m d A : Nat} {α : Type} [DecidableEq α]

theorem no_guard_only_collision
    (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A)
    (old : Fin m → α) (ho : Function.Injective old)
    (label : Physical d A → α) (hl : Function.Injective label)
    (hcross : ∀ p i, label p ≠ old i)
    (active foreign : Active d A)
    (guardCutsL guardCutsR : Fin (guardNumber d A) ↪ Fin m)
    (hgood : guardCutsL ∈ goodEmbeddings m d A hA active)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (hguards : AllGuards d A hA active foreign (roleR none))
    (sumSlot : Fin (d + 2)) (hsum : sumSlot ≠ 0)
    (q : Fin (d + 2) → Int) (phase : Fin (d + 2) → Fin 2) (t : Int)
    (hq : Int.ModEq ((m + guardNumber d A : Nat) : Int)
      (∑ i, AffineReconstruction.frameWeight d sumSlot i * q i) 0)
    (hlocal : ∀ i, Int.ModEq ((m + guardNumber d A : Nat) : Int) (localR i).val
      (q i + t + (phase i).val)) :
    ¬ (ActualMatching.base (background hA old ho label hl hcross active guardCutsL)
      (fun i => label (activeControl d A hA active i)) roleL localL gapL).IsRotated
      (ActualMatching.base (background hA old ho label hl hcross foreign guardCutsR)
        (fun i => label (activeControl d A hA foreign i)) roleR localR gapR) := by
  intro hcyclic
  let guardL := fun j => label (guardLabel d A hA active j)
  let guardR := fun j => label (guardLabel d A hA foreign j)
  let bgL := background hA old ho label hl hcross active guardCutsL
  let bgR := background hA old ho label hl hcross foreign guardCutsR
  let embedL := fun row => label (activeControl d A hA active row)
  let embedR := fun row => label (activeControl d A hA foreign row)
  let residentL := ActualMatching.resident embedL roleL
  let residentR := ActualMatching.resident embedR roleR
  let index := foreignGuardIndex d A hA active foreign (roleR none) hguards
  obtain ⟨slots, hslots⟩ := slotEquiv_exists roleR
  obtain ⟨assignment, hweight, hqphysical⟩ := physical_relation
    ((m + guardNumber d A : Nat) : Int) sumSlot hsum slots q hq
  have hguardLabel (i : Fin (d + 2)) :
      guardL (index i) = label (foreignControl d A hA foreign (roleR none) i) := by
    dsimp [guardL, index]
    rw [foreign_guard_label]
  have hresidentLabel (i : Fin (d + 2)) : residentR (slots i) = guardL (index i) := by
    rw [hguardLabel]
    dsimp [residentR, ActualMatching.resident, embedR]
    rw [hslots i]
    rfl
  have hoffsets (i : Fin (d + 2)) : ∃ e ≤ guardNumber d A,
      (localR (slots i)).val = (guardCutsL (index i)).val + e := by
    let p := foreignControl d A hA foreign (roleR none) i
    let keep := keepGuard old (label p)
    have hpnot : p ∉ activeBlock (d + 3) A (by omega) hA active := hguards i
    have hpmem : p ∈ activeBlock (d + 3) A (by omega) hA foreign :=
      activeControl_mem d A hA foreign ((roleR none).succAbove i)
    have hprow : p = activeControl d A hA foreign (roleR (some (slots i))) := by
      rw [hslots i]
      rfl
    have hkeep (v : Physical d A) : keep (label v) = decide (v = p) :=
      keep_physical old label hl hcross p v
    have hold : ∀ j, keep (old j) = true := keepGuard_old old (label p)
    have hgL : ∀ j, keep (guardL j) = decide (j = index i) := by
      intro j
      have h := keepGuard_guard old guardL (hl.comp (guardLabel_injective d A hA active))
        (fun j a => hcross _ a) (index i) j
      rw [hguardLabel i] at h
      exact h
    have hrL : ∀ j, keep (residentL j) = false := by
      intro j
      change keep (label (activeControl d A hA active (roleL (some j)))) = false
      rw [hkeep]
      apply decide_eq_false_iff_not.mpr
      intro he
      exact hpnot (he ▸ activeControl_mem d A hA active (roleL (some j)))
    have hmL : keep (embedL (roleL none)) = false := by
      change keep (label (activeControl d A hA active (roleL none))) = false
      rw [hkeep]
      apply decide_eq_false_iff_not.mpr
      intro he
      exact hpnot (he ▸ activeControl_mem d A hA active (roleL none))
    have hgR : ∀ j, keep (guardR j) = false := by
      intro j
      change keep (label (guardLabel d A hA foreign j)) = false
      rw [hkeep]
      apply decide_eq_false_iff_not.mpr
      intro he
      exact guardLabel_not_mem d A hA foreign j (he.symm ▸ hpmem)
    have hrR : ∀ j, keep (residentR j) = decide (j = slots i) := by
      intro j
      change keep (label (activeControl d A hA foreign (roleR (some j)))) = _
      rw [hkeep, hprow]
      simp only [(activeControl_injective d A hA foreign).eq_iff, roleR.injective.eq_iff,
        Option.some.injEq]
    have hmR : keep (embedR (roleR none)) = false := by
      change keep (label (activeControl d A hA foreign (roleR none))) = false
      rw [hkeep, hprow]
      simp only [(activeControl_injective d A hA foreign).eq_iff, roleR.injective.eq_iff,
        reduceCtorEq, decide_false]
    exact resident_guard_offset old ho guardL guardCutsL bgL
      (background_word hA old ho label hl hcross active guardCutsL)
      residentL localL (embedL (roleL none)) gapL
      guardR guardCutsR (hl.comp (guardLabel_injective d A hA foreign)) (fun j a => hcross _ a)
      bgR (background_word hA old ho label hl hcross foreign guardCutsR)
      residentR (ActualMatching.resident_injective embedR
        (hl.comp (activeControl_injective d A hA foreign)) roleR)
      (fun j a => active_ne_background hA old ho label hl hcross foreign guardCutsR (roleR (some j)) a)
      localR (embedR (roleR none)) gapR (index i) (slots i) (hresidentLabel i)
      (fun a => by rw [hguardLabel i]; exact hcross _ a)
      keep hold hgL hrL hmL hgR hrR hmR hcyclic
  obtain ⟨b, hb, hrel⟩ := foreign_relation_of_offsets hm hd assignment guardCutsL index
    (fun i => localR (slots i)) hoffsets (fun i => q (slots i)) (fun i => phase (slots i)) t
    hqphysical (fun i => hlocal (slots i))
  exact good_excludes m d A hA active foreign (roleR none) assignment hguards guardCutsL hgood b hb hrel

end CoefficientTwoPrecision.PhysicalGuardExclusion

#print axioms CoefficientTwoPrecision.PhysicalGuardExclusion.no_guard_only_collision
