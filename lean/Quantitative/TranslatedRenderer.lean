import Quantitative.SweepOffsets
import Quantitative.TranslatedControlOrder

/-!
# Exact sweep offsets survive a common cyclic cut translation

Translating every cut changes only the background origin. Relabelling the
background symbols by that translation gives a cyclically equal literal
renderer. The common resident head fixes the same representative, so the
exact full-sweep offset equation is independent of the batch translation.
-/

namespace CoefficientTwoPrecision.TranslatedRenderer

open LiteralState StationaryCircle StationaryUpdate RendererOffsets SweepOffsets
open TranslatedControlOrder

variable {M k : Nat} {α : Type} [NeZero M]

theorem render_translate (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (translation : Fin M) :
    (render background resident (fun i => cuts i + translation)).IsRotated
      (render (fun cut => background (cut + translation)) resident cuts) := by
  have horder : (List.finRange M).IsRotated ((List.finRange M).map (fun cut => cut + translation)) := by
    rw [finRange_translate]
    exact ⟨translation.val, rfl⟩
  have hblock (cut : Fin M) :
      block background resident (fun i => cuts i + translation) (cut + translation) =
        block (fun cut => background (cut + translation)) resident cuts cut := by
    simp only [block, controlsAt_translate]
  have h := flatMap_isRotated _ _ (block background resident (fun i => cuts i + translation)) horder
  simpa only [render, List.flatMap_map, Function.comp_def, hblock] using h

theorem resident_head_normalizes [DecidableEq α]
    (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : StrictMono cuts) (translation : Fin M)
    (hnd : (render background resident (fun i => cuts i + translation)).Nodup)
    (previous : Fin k) (gap : Nat)
    (hhead : ((render background resident (fun i => cuts i + translation)).rotateLeft gap).head? =
      some (resident previous)) :
    (render background resident (fun i => cuts i + translation)).rotateLeft gap =
      (render (fun cut => background (cut + translation)) resident cuts).rotateLeft
        ((cuts previous).val + previous.val) := by
  have hsource : (render background resident (fun i => cuts i + translation)).IsRotated
      ((render background resident (fun i => cuts i + translation)).rotateLeft gap) :=
    ⟨gap, (LiteralState.rotateLeft_eq_rotate _ gap).symm⟩
  have htarget : (render (fun cut => background (cut + translation)) resident cuts).IsRotated
      ((render (fun cut => background (cut + translation)) resident cuts).rotateLeft
        ((cuts previous).val + previous.val)) :=
    ⟨_, (LiteralState.rotateLeft_eq_rotate _ _).symm⟩
  apply CutExtraction.isRotated_same_head_eq _ _ (hsource.nodup_iff.mp hnd)
    (hsource.symm.trans ((render_translate background resident cuts translation).trans htarget))
  exact hhead.trans (resident_offset (fun cut => background (cut + translation)) resident cuts hcuts previous).symm

/-- The translated actual target suffix gives the same offset congruence
as the unshifted increasing physical cuts. -/
theorem sweep_offset_equation [DecidableEq α]
    (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : StrictMono cuts) (translation : Fin M)
    (hnd : (render background resident (fun i => cuts i + translation)).Nodup)
    (previous target : Fin k) (mobile : α) (gap moves : Nat) (pre : List α)
    (hhead : ((render background resident (fun i => cuts i + translation)).rotateLeft gap).head? =
      some (resident previous))
    (hsuffix : fullIterate moves
      ((render background resident (fun i => cuts i + translation)).rotateLeft gap ++ [mobile]) =
        pre ++ [resident target, background (cuts target + translation), mobile]) :
    ((cuts previous).val + previous.val + moves) %
        (render background resident (fun i => cuts i + translation)).length =
      ((cuts target).val + target.val + 2) %
        (render background resident (fun i => cuts i + translation)).length := by
  have hnormalized := resident_head_normalizes background resident cuts hcuts translation hnd previous gap hhead
  rw [hnormalized] at hsuffix
  have hrotation := render_translate background resident cuts translation
  have h := SweepOffsets.sweep_offset_equation (fun cut => background (cut + translation)) resident cuts hcuts
    (hrotation.nodup_iff.mp hnd) previous target mobile ((cuts previous).val + previous.val) moves pre
    (resident_offset (fun cut => background (cut + translation)) resident cuts hcuts previous) hsuffix
  rw [← hrotation.perm.length_eq] at h
  exact h

theorem sweep_length [DecidableEq α]
    (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : StrictMono cuts) (translation : Fin M)
    (hnd : (render background resident (fun i => cuts i + translation)).Nodup)
    (previous target : Fin k) (mobile : α) (gap moves : Nat) (pre : List α)
    (hstart : (cuts previous).val + previous.val <
      (render background resident (fun i => cuts i + translation)).length)
    (htarget : (cuts target).val + target.val + 2 <
      (render background resident (fun i => cuts i + translation)).length)
    (hmoves : moves < (render background resident (fun i => cuts i + translation)).length)
    (hhead : ((render background resident (fun i => cuts i + translation)).rotateLeft gap).head? =
      some (resident previous))
    (hsuffix : fullIterate moves
      ((render background resident (fun i => cuts i + translation)).rotateLeft gap ++ [mobile]) =
        pre ++ [resident target, background (cuts target + translation), mobile]) :
    moves = if (cuts previous).val + previous.val ≤ (cuts target).val + target.val + 2
      then (cuts target).val + target.val + 2 - ((cuts previous).val + previous.val)
      else (render background resident (fun i => cuts i + translation)).length +
        ((cuts target).val + target.val + 2) - ((cuts previous).val + previous.val) := by
  have h := sweep_offset_equation background resident cuts hcuts translation hnd previous target mobile gap moves pre
    hhead hsuffix
  rw [Nat.mod_eq_of_lt htarget] at h
  exact forward_difference _ _ _ _ hstart htarget hmoves h

end CoefficientTwoPrecision.TranslatedRenderer

#print axioms CoefficientTwoPrecision.TranslatedRenderer.render_translate
#print axioms CoefficientTwoPrecision.TranslatedRenderer.sweep_length
