import Quantitative.ControlOrder
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Cyclic control order after a common translation of the cuts

Adding one common residue to all cuts changes the starting point of the
background circle. It preserves the cyclic order of the resident controls.
This statement applies to the actual renderer, including its mobile gap.
-/

namespace CoefficientTwoPrecision.TranslatedControlOrder

open ControlOrder StationaryCircle LiteralState

variable {M k : Nat} {α β : Type}

theorem flatMap_isRotated (first second : List α) (f : α → List β)
    (h : first.IsRotated second) :
    (first.flatMap f).IsRotated (second.flatMap f) := by
  obtain ⟨n, rfl⟩ := h
  have hsplit : first.flatMap f =
      (first.take (n % first.length)).flatMap f ++
        (first.drop (n % first.length)).flatMap f := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [hsplit, List.rotate_eq_drop_append_take_mod, List.flatMap_append]
  exact List.isRotated_append

theorem finRange_translate [NeZero M] (translation : Fin M) :
    (List.finRange M).map (fun cut => cut + translation) =
      (List.finRange M).rotate translation.val := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < M
  · rw [List.getElem?_map, List.getElem?_rotate (by simpa using hi)]
    simp only [List.finRange, List.length_ofFn, List.getElem?_ofFn, dite_eq_left hi,
      dite_eq_left (Nat.mod_lt _ (NeZero.pos M)), Option.map_some]
    congr 1
  · have hleft : ((List.finRange M).map (fun cut => cut + translation))[i]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)
    have hright : ((List.finRange M).rotate translation.val)[i]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)
    rw [hleft, hright]

theorem controlsAt_translate [NeZero M] (cuts : Fin k → Fin M)
    (translation cut : Fin M) :
    controlsAt (fun j => cuts j + translation) (cut + translation) =
      controlsAt cuts cut := by
  simp only [controlsAt, add_right_cancel_iff]

theorem slotOrder_translate [NeZero M] (cuts : Fin k → Fin M)
    (translation : Fin M) :
    (slotOrder (fun j => cuts j + translation)).IsRotated (slotOrder cuts) := by
  have hrot : (List.finRange M).IsRotated
      ((List.finRange M).map (fun cut => cut + translation)) := by
    rw [finRange_translate]
    exact ⟨translation.val, rfl⟩
  have h := flatMap_isRotated _ _
    (controlsAt (fun j => cuts j + translation)) hrot
  simpa only [slotOrder, List.flatMap_map, Function.comp_def,
    controlsAt_translate] using h

theorem render_control_projection (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (keep : α → Bool)
    (hbackground : ∀ i, keep (background i) = false) :
    (render background resident cuts).filter keep =
      ((slotOrder cuts).map resident).filter keep := by
  have hb (cut : Fin M) : (block background resident cuts cut).filter keep =
      ((controlsAt cuts cut).map resident).filter keep := by
    simp only [block, List.filter_append, List.filter_cons, hbackground,
      Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
  simp only [render, List.filter_flatMap, hb, slotOrder, List.map_flatMap]

theorem base_control_order [NeZero M] [DecidableEq α]
    (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : StrictMono cuts)
    (translation : Fin M) (mobile : α) (gap : Nat)
    (keep : α → Bool) (hbackground : ∀ i, keep (background i) = false)
    (hmobile : keep mobile = false) :
    (((List.finRange k).map resident).filter keep).IsRotated
      (((render background resident (fun j => cuts j + translation)).rotateLeft gap ++
        [mobile]).filter keep) := by
  have horder := (slotOrder_translate cuts translation).symm
  rw [slotOrder_eq cuts hcuts] at horder
  have hprojection := CutExtraction.filter_isRotated _ _ keep (horder.map resident)
  rw [← render_control_projection background resident _ keep hbackground] at hprojection
  have hgap := CutExtraction.filter_rotate
    (render background resident (fun j => cuts j + translation)) keep gap
  have h := hprojection.trans hgap
  simpa only [rotateLeft_eq_rotate, List.filter_append, List.filter_cons, hmobile,
    Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil] using h

end CoefficientTwoPrecision.TranslatedControlOrder

#print axioms CoefficientTwoPrecision.TranslatedControlOrder.base_control_order
