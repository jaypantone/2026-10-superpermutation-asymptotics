import Quantitative.SourceErasure
import Quantitative.LiteralSchedule

/-!
# Old-letter projection of the actual source bases

Iterated control erasure is ordinary filtering. Deleting every current
resident and mobile from a rendered base leaves a rotation of its filtered
background. This connects the source renderer to membership in the finite
insertion universe, including backgrounds that themselves contain guards.
-/

namespace CoefficientTwoPrecision.SourceProjection

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open CoefficientTwoPrecision.SourceUniverse CoefficientTwoPrecision.SourceErasure
open CoefficientTwoPrecision.LiteralState CoefficientTwoPrecision.LiteralSchedule
open CoefficientTwoPrecision.StationaryCircle

theorem eraseControls_eq_filter (controls word : List Nat) :
    eraseControls controls word = word.filter (fun a => decide (a ∉ controls)) := by
  induction controls generalizing word with
  | nil => simp [eraseControls]
  | cons v controls ih =>
    rw [eraseControls, ih, eraseSatellite, List.filter_filter]
    apply List.filter_congr
    intro a ha
    simp [List.mem_cons, not_or, and_comm, Bool.and_comm]

/-- Residents can be deleted while the background is filtered by an
arbitrary old-letter predicate. Background guards are therefore allowed. -/
theorem render_projection {M k : Nat} (background : Fin M → Nat) (resident : Fin k → Nat)
    (cuts : Fin k → Fin M) (keep : Nat → Bool)
    (hresident : ∀ j, keep (resident j) = false) :
    (render background resident cuts).filter keep =
      ((List.finRange M).map background).filter keep := by
  have hcontrols (cut : Fin M) : ((controlsAt cuts cut).map resident).filter keep = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    simp [hresident j]
  have hblock (cut : Fin M) :
      (block background resident cuts cut).filter keep = [background cut].filter keep := by
    simp only [block, List.filter_append, hcontrols, List.nil_append]
  rw [render, List.filter_flatMap]
  simp only [hblock]
  rw [List.map_eq_flatMap, List.filter_flatMap]

/-- Every mobile-gap representative of the rendered base has the same
filtered background cyclic order. -/
theorem rendered_base_projection {M k : Nat}
    (background : Fin M → Nat) (resident : Fin k → Nat) (cuts : Fin k → Fin M)
    (mobile gap : Nat) (keep : Nat → Bool)
    (hresident : ∀ j, keep (resident j) = false) (hmobile : keep mobile = false)
    (hne : ((List.finRange M).map background).filter keep ≠ []) :
    CyclicEq (((List.finRange M).map background).filter keep)
      (((render background resident cuts).rotateLeft gap ++ [mobile]).filter keep) := by
  have hfilter := render_projection background resident cuts keep hresident
  have hrne : (render background resident cuts).filter keep ≠ [] := by rwa [hfilter]
  have hr : render background resident cuts ≠ [] := by
    intro he
    apply hrne
    simp [he]
  have hc := (CyclicEq.of_rot hr gap).filter keep hrne
  rw [hfilter] at hc
  simpa only [List.filter_append, List.filter_cons, hmobile, Bool.false_eq_true,
    ↓reduceIte, List.filter_nil, List.append_nil] using hc

/-- A full sweep preserves that old-letter cyclic order at every emitted
row, provided its mobile is a deleted control. -/
theorem fullIterate_projection (stationary : List Nat) (mobile moves : Nat)
    (keep : Nat → Bool) (hmobile : keep mobile = false)
    (hne : stationary.filter keep ≠ []) :
    CyclicEq (stationary.filter keep) ((fullIterate moves (stationary ++ [mobile])).filter keep) := by
  have hs : stationary ≠ [] := by intro he; apply hne; simp [he]
  have hc := (CyclicEq.of_rot hs moves).filter keep hne
  rw [fullIterate_formula]
  simpa only [List.filter_append, List.filter_cons, hmobile, Bool.false_eq_true,
    ↓reduceIte, List.filter_nil, List.append_nil] using hc

/-- Actual source-base projection and alphabet membership imply membership
in the exact finite cyclic insertion universe. -/
theorem insertionAbove_of_projection (controls d word : List Nat)
    (hd : 0 < d.length) (hnd : (controls ++ d).Nodup)
    (hp : word.Perm (controls ++ d))
    (hprojection : CyclicEq d (word.filter (fun a => decide (a ∉ controls)))) :
    InsertionAbove controls d word := by
  apply insertionAbove_of_erasure controls d word hd hnd hp
  rwa [eraseControls_eq_filter]

end CoefficientTwoPrecision.SourceProjection

#print axioms CoefficientTwoPrecision.SourceProjection.rendered_base_projection
#print axioms CoefficientTwoPrecision.SourceProjection.insertionAbove_of_projection
