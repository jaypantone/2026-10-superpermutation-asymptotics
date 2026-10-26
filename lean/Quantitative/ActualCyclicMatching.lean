import Quantitative.RetainedControlOrder
import Quantitative.ControlOmissions

/-!
# Extracting the reconstruction matching from two actual cyclic rows

Binary perturbations preserve the anchored physical order, and common
translations preserve that order cyclically. After removing the two mobile
labels (or one mobile and one further label), equal cyclic bases therefore
give one of exactly n offsets on the n retained stationary positions.
-/

namespace CoefficientTwoPrecision.ActualCyclicMatching

open FiniteRoles BatchSafety RobustMatching RobustSafety PhasedControlOrder

variable {M n : Nat} [NeZero M] {Control α : Type} [DecidableEq α]

omit [NeZero M] in
theorem cutValue_injective : Function.Injective (cutValue (M := M)) := by
  intro i j h
  have hv := congrArg ZMod.val h
  apply Fin.ext
  simpa only [cutValue, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] using hv

omit [NeZero M] in
theorem cutValue_add (i j : Fin M) : cutValue (i + j) = cutValue i + cutValue j := by
  simp only [cutValue, Fin.val_add, ZMod.natCast_mod, Nat.cast_add]

def translationCut (t : ZMod M) : Fin M := ⟨t.val, ZMod.val_lt t⟩

theorem translationCut_value (t : ZMod M) : cutValue (translationCut t) = t :=
  ZMod.natCast_zmod_val t

theorem represented_cuts (hM : 2 ≤ M) (q : Fin (n + 1) → Fin M)
    (hr : Robust (fun i => cutValue (q i))) (hz : q 0 = 0)
    (t : ZMod M) (phase : Fin (n + 1) → Bool) (cuts : Fin (n + 1) → Fin M)
    (hrep : Represents (fun i => cutValue (q i)) t phase cuts) :
    cuts = fun i => phased hM q hr 0 hz phase i + translationCut t := by
  funext i
  apply cutValue_injective
  rw [hrep i, cutValue_add, phased_value, translationCut_value]
  simp only [perturbed]
  ring

theorem row_projection (hM : 2 ≤ M) (background : Fin M → α) (embed : Control → α)
    (assignment : Role (n + 1) ≃ Control)
    (q : Fin (n + 1) → Fin M) (hmono : StrictMono q)
    (hr : Robust (fun i => cutValue (q i))) (hz : q 0 = 0)
    (t : ZMod M) (phase : Fin (n + 1) → Bool) (cuts : Fin (n + 1) → Fin M)
    (hrep : Represents (fun i => cutValue (q i)) t phase cuts)
    (gap : Nat) (omitted : Fin (n + 1)) (keep : α → Bool)
    (hb : ∀ i, keep (background i) = false)
    (hm : keep (embed (assignment none)) = false)
    (hs : ∀ i, keep (embed (assignment (some i))) = decide (i ≠ omitted)) :
    ((CyclicMatching.retainedLabels assignment omitted).map embed).IsRotated
      ((ActualMatching.base background embed assignment cuts gap).filter keep) := by
  rw [represented_cuts hM q hr hz t phase cuts hrep]
  exact RetainedControlOrder.translated_base_projection background embed assignment
    (phased hM q hr 0 hz phase) (phased_strictMono hM q hmono hr 0 hz phase)
    (translationCut t) gap omitted keep hb hm hs

theorem actual_retained_matching (hM : 2 ≤ M) (hn : 0 < n)
    (background : Fin M → α) (embed : Control → α) (hembed : Function.Injective embed)
    (hcross : ∀ c i, embed c ≠ background i)
    (first second : Role (n + 1) ≃ Control)
    (q q' : Fin (n + 1) → Fin M) (hmono : StrictMono q) (hmono' : StrictMono q')
    (hr : Robust (fun i => cutValue (q i))) (hr' : Robust (fun i => cutValue (q' i)))
    (hz : q 0 = 0) (hz' : q' 0 = 0)
    (t t' : ZMod M) (phase phase' : Fin (n + 1) → Bool)
    (cuts cuts' : Fin (n + 1) → Fin M) (gap gap' : Nat)
    (hrep : Represents (fun i => cutValue (q i)) t phase cuts)
    (hrep' : Represents (fun i => cutValue (q' i)) t' phase' cuts')
    (hcyclic : (ActualMatching.base background embed first cuts gap).IsRotated
      (ActualMatching.base background embed second cuts' gap')) :
    ∃ omitted other : Fin (n + 1), ∃ offset : Fin n, ∀ i : Fin n,
      Matches first second (omitted.succAbove (i + offset)) (other.succAbove i) := by
  classical
  obtain ⟨omitted, other, homit⟩ := ControlOmissions.exists_omissions first second
  let keep := ControlOmissions.keep embed first omitted
  have hb (i : Fin M) : keep (background i) = false :=
    ControlOmissions.keep_background embed first omitted (background i) (fun c => hcross c i)
  have hfirst := row_projection hM background embed first q hmono hr hz t phase cuts
    hrep gap omitted keep hb
    (ControlOmissions.keep_first_mobile embed hembed first omitted)
    (ControlOmissions.keep_first_stationary embed hembed first omitted)
  have hsecond := row_projection hM background embed second q' hmono' hr' hz' t' phase' cuts'
    hrep' gap' other keep hb
    (ControlOmissions.keep_second_mobile embed hembed first second omitted other homit)
    (fun i => ControlOmissions.keep_second_stationary embed hembed first second
      omitted other i homit)
  have hprojected := CutExtraction.filter_isRotated _ _ keep hcyclic
  have hlabels := hfirst.trans (hprojected.trans hsecond.symm)
  have hof : (List.ofFn (fun i : Fin n => embed (first (some (omitted.succAbove i))))).IsRotated
      (List.ofFn (fun i : Fin n => embed (second (some (other.succAbove i))))) := by
    simpa only [CyclicMatching.retainedLabels, List.map_ofFn, Function.comp_def] using hlabels
  obtain ⟨offset, hoffset⟩ := CyclicMatching.rotation_offset hn _ _ hof
  exact ⟨omitted, other, offset, fun i => hembed (hoffset i)⟩

end CoefficientTwoPrecision.ActualCyclicMatching

#print axioms CoefficientTwoPrecision.ActualCyclicMatching.actual_retained_matching
