import Quantitative.GuardCatalogue

/-!
# Applying the guard catalogue to actual foreign stationary symbols

The coordinates in this argument are positions in the concrete rendered
background. Their symbols identify the corresponding physical foreign
controls. The prescribed guard-cut projection therefore yields one of the
events already deleted by GuardCatalogue. Two elementary grid lemmas cover
disjoint blocks and a shared control that is the foreign mobile.
-/

namespace CoefficientTwoPrecision.GuardCollisionProjection

open ActiveGrid StationaryRelations StationaryCircle StationaryUpdate
open GuardPositions GuardEvents GuardCatalogue

theorem foreignControl_mem (d A : Nat) (hA : 0 < A) (foreign : Active d A)
    (mobile : Fin (d + 3)) (i : Fin (d + 2)) :
    foreignControl d A hA foreign mobile i ∈
      activeBlock (d + 3) A (by omega) hA foreign := by
  exact Finset.mem_image.mpr ⟨mobile.succAbove i, Finset.mem_univ _, rfl⟩

theorem allGuards_of_disjoint (d A : Nat) (hA : 0 < A)
    (active foreign : Active d A) (mobile : Fin (d + 3))
    (hdisjoint : Disjoint (activeBlock (d + 3) A (by omega) hA active)
      (activeBlock (d + 3) A (by omega) hA foreign)) :
    AllGuards d A hA active foreign mobile := by
  intro i hi
  exact Finset.disjoint_left.mp hdisjoint hi (foreignControl_mem d A hA foreign mobile i)

/-- If distinct blocks share the foreign mobile, their other stationary
controls are all guards of the current active block. -/
theorem allGuards_of_shared_mobile (d A : Nat) (hA : 0 < A)
    (active foreign : Active d A) (hne : active ≠ foreign) (mobile : Fin (d + 3))
    (hshared : controlAt (d + 3) A (by omega) hA foreign mobile ∈
      activeBlock (d + 3) A (by omega) hA active) :
    AllGuards d A hA active foreign mobile := by
  intro i hi
  have hstationary : foreignControl d A hA foreign mobile i ∈
      activeBlock (d + 3) A (by omega) hA active ∩
        activeBlock (d + 3) A (by omega) hA foreign :=
    Finset.mem_inter.mpr ⟨hi, foreignControl_mem d A hA foreign mobile i⟩
  have hmobile : controlAt (d + 3) A (by omega) hA foreign mobile ∈
      activeBlock (d + 3) A (by omega) hA active ∩
        activeBlock (d + 3) A (by omega) hA foreign :=
    Finset.mem_inter.mpr ⟨hshared, Finset.mem_image.mpr ⟨mobile, Finset.mem_univ _, rfl⟩⟩
  have hcard := activeBlock_inter_card (d + 3) A (by omega) hA active foreign hne
  have he := Finset.card_le_one.mp hcard _ hstationary _ hmobile
  have hrow : mobile.succAbove i = mobile := congrArg Prod.fst he
  exact Fin.succAbove_ne mobile i hrow

/-- A retained actual guard background contains no stationary foreign
frame whose stationary physical controls are all guards. -/
theorem no_guard_only_frame {m d A : Nat} {α : Type}
    (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A)
    (active foreign : Active d A) (mobile : Fin (d + 3))
    (hguards : AllGuards d A hA active foreign mobile)
    (old : Fin m → α) (ho : Function.Injective old)
    (label : Physical d A → α) (hlabel : Function.Injective label)
    (hcross : ∀ p i, label p ≠ old i)
    (cuts : Fin (guardNumber d A) ↪ Fin m)
    (hgood : cuts ∈ goodEmbeddings m d A hA active)
    (assignment : Assignment d)
    (y : Fin (d + 2) → Fin (m + guardNumber d A))
    (q : Fin (d + 2) → Int) (phase : Fin (d + 2) → Fin 2) (t : Int)
    (hq : Int.ModEq ((m + guardNumber d A : Nat) : Int)
      (∑ i, weight assignment i * q i) 0)
    (hy : ∀ i, Int.ModEq ((m + guardNumber d A : Nat) : Int) (y i).val
      (q i + t + (phase i).val))
    (hentries : ∀ i,
      (render old (fun j => label (guardLabel d A hA active j)) cuts)[(y i).val]? =
        some (label (foreignControl d A hA foreign mobile i))) : False := by
  let guard : Fin (guardNumber d A) → α := fun j => label (guardLabel d A hA active j)
  have hg : Function.Injective guard := hlabel.comp (guardLabel_injective d A hA active)
  have hcross' : ∀ j i, guard j ≠ old i := fun j i => hcross _ i
  let index := foreignGuardIndex d A hA active foreign mobile hguards
  have hpositions (i : Fin (d + 2)) :
      ∃ e ≤ guardNumber d A, (y i).val = (cuts (index i)).val + e := by
    apply guard_position_offset old guard cuts ho hg hcross' (index i)
    · rw [render_length old guard cuts ho hg hcross']
      exact (y i).isLt
    · simpa only [guard, index, foreign_guard_label] using hentries i
  choose e he hxe using hpositions
  have hsum := weight_abs_sum hd assignment
  have hphase (i : Fin (d + 2)) :
      0 ≤ ((phase i).val : Int) ∧ ((phase i).val : Int) ≤ 1 := by
    have hi := (phase i).isLt
    omega
  have hframe := frame_relation ((m + guardNumber d A : Nat) : Int) t
    (weight assignment) q (fun i => ((phase i).val : Int)) (fun i => ((y i).val : Int))
    (weight_sum assignment) hq hy
  obtain ⟨ell, hell, hrel⟩ := bounded_winding (m + guardNumber d A) (2 * d) (by omega)
    (weight assignment) (fun i => ((y i).val : Int))
    (fun i => ((phase i).val : Int)) hsum
    (fun i => by have hi := (y i).isLt; omega) hphase hframe
  have hph := weighted_abs_bound (weight assignment)
    (fun i => ((phase i).val : Int)) 1 (fun i => by have hi := hphase i; omega)
  rw [hsum, Nat.mul_one] at hph
  obtain ⟨b, hb, hmod⟩ := old_relation_of_offsets m (guardNumber d A) d (weight assignment)
    (fun i => ((cuts (index i)).val : Int)) (fun i => (e i : Int))
    (fun i => ((y i).val : Int)) ell (∑ i, weight assignment i * (phase i).val) hsum
    (fun i => by simpa only [Int.natAbs_natCast] using he i)
    (fun i => by exact_mod_cast hxe i) (by omega) hph (by simpa only [Nat.cast_add] using hrel)
  exact good_excludes m d A hA active foreign mobile assignment hguards cuts hgood b hb hmod

end CoefficientTwoPrecision.GuardCollisionProjection

#print axioms CoefficientTwoPrecision.GuardCollisionProjection.allGuards_of_shared_mobile
#print axioms CoefficientTwoPrecision.GuardCollisionProjection.no_guard_only_frame
