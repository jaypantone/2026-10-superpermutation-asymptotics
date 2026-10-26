import Quantitative.SourceRelabeling

/-!
# Uniform actual families from one canonical contour collection

The only contours supplied to this constructor are those over the canonical
old word `A0`. For every permutation `d` of `A0`, the original positional
relabeling sends `A0` to `d` and fixes all controls and the satellite. We
apply it to the actual contour lists and prove all SourceFamily fields,
including uniform row, charge, and circle counts. The existing advancement
and complement construction then yields an actual WidthBlockFamily.
-/

namespace CoefficientTwoPrecision.CanonicalSourceFamily

open SuperpermutationUpperBound SuperpermutationUpperBound43586371
open SourceUniverse SourceAdvancement SourceFamilyAdapter SourceRelabeling StageExtension

private theorem old_nodup {A0 controls : List ℕ} (hnd : (controls ++ A0).Nodup) : A0.Nodup :=
  (List.nodup_append.mp hnd).2.1

private theorem relab_injective' {A0 controls d : List ℕ}
    (hnd : (controls ++ A0).Nodup) (hd : d.Perm A0) : Function.Injective (relab A0 d) := by
  intro a b hab
  exact relab_injective (old_nodup hnd) hd a b hab

/-- The relabeling of old letters fixes every actual control. -/
theorem controls_fixed {A0 controls d : List ℕ} (hnd : (controls ++ A0).Nodup) :
    controls.map (relab A0 d) = controls := by
  calc
    controls.map (relab A0 d) = controls.map id := by
      apply List.map_congr_left
      intro a ha
      exact relab_of_not_mem (fun hm => (List.nodup_append.mp hnd).2.2 a ha a hm rfl)
    _ = controls := List.map_id controls

private theorem alphabet_perm {A0 controls d : List ℕ}
    (hnd : (controls ++ A0).Nodup) (hd : d.Perm A0) :
    ((controls ++ A0).map (relab A0 d)).Perm (controls ++ A0) :=
  map_relab_perm (old_nodup hnd) hd hnd (fun a ha => List.mem_append_right controls ha)

/-- The collection over an arbitrary old order is an explicit map of the
canonical collection. Nonpermutations are assigned the empty collection;
SourceFamily makes no assertions at those irrelevant inputs. -/
noncomputable def contours {A0 controls : List ℕ} {h : ℕ}
    (hnd : (controls ++ A0).Nodup) (h9 : 9 ∉ A0)
    (F : List (SourceContour (controls ++ A0) h)) (d : List ℕ) :
    List (SourceContour (controls ++ A0) h) :=
  if hd : d.Perm A0 then
    F.map (fun C => mapContour C (relab A0 d) (relab_injective' hnd hd)
      (relab_of_not_mem h9) (alphabet_perm hnd hd))
  else []

/-- A canonical contour collection produces an actual family over every
old permutation. All three uniform counts are the canonical actual counts. -/
noncomputable def family (A0 controls : List ℕ) (next h : ℕ)
    (hpositive : 0 < A0.length) (hnd : (controls ++ A0).Nodup) (h9 : 9 ∉ A0)
    (hsize : (controls ++ A0).length = h + 2) (hthree : 3 ≤ h + 2)
    (hnext : next ∉ controls ++ A0) (hnext9 : next ≠ 9) (h10 : 10 ∉ controls ++ A0)
    (F : List (SourceContour (controls ++ A0) h))
    (hinsertion : ∀ row ∈ sourceRows F, InsertionAbove controls A0 row.base)
    (hdistinct : (sourceRows F).Pairwise (fun row other => ¬ CyclicEq row.base other.base)) :
    SourceFamily A0 controls next h where
  oldPositive := hpositive
  alphabetSize := hsize
  sizeThree := hthree
  nextFresh := hnext
  nextNine := hnext9
  finalFresh := h10
  contours := contours hnd h9 F
  countRows := (sourceRows F).length
  countCharge := ((sourceRows F).map Row.charge).sum
  countCircles := (F.map (fun C => 2 * (portGcd C.rows h) ^ 2)).sum
  insertion d hd row hrow := by
    simp only [contours, dite_eq_left hd, sourceRows_map] at hrow
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
    have hi := insertionAbove_map (relab A0 d) (hinsertion old hold)
    rw [controls_fixed hnd, map_relab_self (old_nodup hnd) hd] at hi
    exact hi
  distinct d hd := by
    simpa only [contours, dite_eq_left hd] using
      sourceRows_distinct_map F (relab A0 d) (relab_injective' hnd hd)
        (relab_of_not_mem h9) (alphabet_perm hnd hd) hdistinct
  rows d hd := by
    simpa only [contours, dite_eq_left hd] using
      (source_counts_map F (relab A0 d) (relab_injective' hnd hd)
        (relab_of_not_mem h9) (alphabet_perm hnd hd)).1
  charge d hd := by
    simpa only [contours, dite_eq_left hd] using
      (source_counts_map F (relab A0 d) (relab_injective' hnd hd)
        (relab_of_not_mem h9) (alphabet_perm hnd hd)).2.1
  circleCount d hd := by
    simpa only [contours, dite_eq_left hd] using
      (source_counts_map F (relab A0 d) (relab_injective' hnd hd)
        (relab_of_not_mem h9) (alphabet_perm hnd hd)).2.2

/-- This is the full actual block constructor: relabel the canonical
contours, advance their rows and connectors, and construct the pending
complement in the actual insertion universe. -/
noncomputable def widthBlock (A0 controls : List ℕ) (next h : ℕ)
    (hpositive : 0 < A0.length) (hnd : (controls ++ A0).Nodup) (h9 : 9 ∉ A0)
    (hsize : (controls ++ A0).length = h + 2) (hthree : 3 ≤ h + 2)
    (hnext : next ∉ controls ++ A0) (hnext9 : next ≠ 9) (h10 : 10 ∉ controls ++ A0)
    (F : List (SourceContour (controls ++ A0) h))
    (hinsertion : ∀ row ∈ sourceRows F, InsertionAbove controls A0 row.base)
    (hdistinct : (sourceRows F).Pairwise (fun row other => ¬ CyclicEq row.base other.base)) :
    WidthBlockFamily A0 controls next :=
  toWidthBlockFamily (family A0 controls next h hpositive hnd h9 hsize hthree
    hnext hnext9 h10 F hinsertion hdistinct)

/-- The returned block uses the canonical actual occurrence counts exactly. -/
theorem widthBlock_counts (A0 controls : List ℕ) (next h : ℕ)
    (hpositive : 0 < A0.length) (hnd : (controls ++ A0).Nodup) (h9 : 9 ∉ A0)
    (hsize : (controls ++ A0).length = h + 2) (hthree : 3 ≤ h + 2)
    (hnext : next ∉ controls ++ A0) (hnext9 : next ≠ 9) (h10 : 10 ∉ controls ++ A0)
    (F : List (SourceContour (controls ++ A0) h))
    (hinsertion : ∀ row ∈ sourceRows F, InsertionAbove controls A0 row.base)
    (hdistinct : (sourceRows F).Pairwise (fun row other => ¬ CyclicEq row.base other.base)) :
    let K := widthBlock A0 controls next h hpositive hnd h9 hsize hthree
      hnext hnext9 h10 F hinsertion hdistinct
    K.sourceRows = (sourceRows F).length ∧
      K.sourceCharge = ((sourceRows F).map Row.charge).sum ∧
      K.advancedCircles = (F.map (fun C => 2 * (portGcd C.rows h) ^ 2)).sum := by
  exact ⟨rfl, rfl, rfl⟩

end CoefficientTwoPrecision.CanonicalSourceFamily

#print axioms CoefficientTwoPrecision.CanonicalSourceFamily.family
#print axioms CoefficientTwoPrecision.CanonicalSourceFamily.widthBlock
#print axioms CoefficientTwoPrecision.CanonicalSourceFamily.widthBlock_counts
