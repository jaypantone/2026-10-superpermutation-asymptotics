import Quantitative.SortedFrames
import Quantitative.FrameSetUniqueness
import Quantitative.FiniteRoles
import Mathlib.Data.Fintype.Perm

/-!
# Counting actual increasing cut tuples and their initial labels

The finite family consists of actual increasing functions into Fin M.
Every member has an anchored zero, a nonzero sum position and the precise
physical affine relation. A fibre of the sorting map has at most d!
elements, because equality of its full cut sets recovers the coordinate
set. Labels are included before any independent family is selected.
-/

namespace CoefficientTwoPrecision.SortedFrameSupply

open FrameAlgebra FrameCounting FrameOrbits RobustMatching SortedFrames
open FrameSetUniqueness AffineReconstruction

variable {M d : Nat} [NeZero M]

noncomputable def sortedChoice (x : Fin d → Fin M) : Fin (d + 2) → Fin M := by
  classical
  exact if hx : x ∈ goodFrames M d then Classical.choose (good_frame_sorted x hx) else fun _ => 0

theorem sortedChoice_spec (x : Fin d → Fin M) (hx : x ∈ goodFrames M d) :
    ∃ sumSlot : Fin (d + 2), sumSlot ≠ 0 ∧ StrictMono (sortedChoice x) ∧
      sortedChoice x 0 = 0 ∧ Robust (fun i => ((sortedChoice x i).val : ZMod M)) ∧
      (∑ i, (frameWeight d sumSlot i : ZMod M) * ((sortedChoice x i).val : ZMod M)) = 0 ∧
      ∃ order : Fin (d + 2) ≃ Point d, order 0 = none ∧ order sumSlot = some none ∧
        ∀ i, (sortedChoice x i).val = (cuts x (order i)).val := by
  classical
  simpa only [sortedChoice, dif_pos hx] using Classical.choose_spec (good_frame_sorted x hx)

theorem sortedChoice_pointSet (x : Fin d → Fin M) (hx : x ∈ goodFrames M d) :
    Finset.univ.image (fun i => ((sortedChoice x i).val : ZMod M)) = pointSet x := by
  classical
  obtain ⟨s, _, _, _, _, _, order, _, _, hvalue⟩ := sortedChoice_spec x hx
  have hcast (i : Fin (d + 2)) : ((sortedChoice x i).val : ZMod M) = cuts x (order i) := by
    rw [hvalue]
    exact ZMod.natCast_zmod_val _
  ext z
  constructor
  · intro hz
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨order i, Finset.mem_univ _, (hcast i).symm.trans hi⟩
  · intro hz
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨order.symm p, Finset.mem_univ _, ?_⟩
    rw [hcast, order.apply_symm_apply, hp]

theorem sorted_eq_coordinateSet (x y : Fin d → Fin M)
    (hx : x ∈ goodFrames M d) (hy : y ∈ goodFrames M d)
    (h : sortedChoice x = sortedChoice y) : coordinateSet x = coordinateSet y := by
  apply same_coordinateSet x y hx hy
  rw [← sortedChoice_pointSet x hx, ← sortedChoice_pointSet y hy, h]

noncomputable def physicalFrames (M d : Nat) [NeZero M] : Finset (Fin (d + 2) → Fin M) := by
  classical
  exact (goodFrames M d).image sortedChoice

theorem fixed_sorted_card_le (q : Fin (d + 2) → Fin M) :
    ((goodFrames M d).filter (fun x => sortedChoice x = q)).card ≤ d.factorial := by
  classical
  let S := (goodFrames M d).filter (fun x => sortedChoice x = q)
  rcases S.eq_empty_or_nonempty with hnil | ⟨y, hy⟩
  · change S.card ≤ d.factorial
    rw [hnil, Finset.card_empty]
    exact Nat.zero_le _
  · have hsub : S ⊆ (goodFrames M d).filter (fun x => coordinateSet x = coordinateSet y) := by
      intro x hx
      obtain ⟨hxgood, hxq⟩ := Finset.mem_filter.mp hx
      obtain ⟨hygood, hyq⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hxgood,
        sorted_eq_coordinateSet x y hxgood hygood (hxq.trans hyq.symm)⟩
    exact (Finset.card_le_card hsub).trans (fixed_image_card_le M d (coordinateSet y))

theorem physicalFrames_card_lower (hM : 0 < M) (hd : 3 ≤ d) :
    M ^ d ≤ (physicalFrames M d).card * d.factorial +
      18 * (d + 2) ^ 4 * M ^ (d - 1) := by
  classical
  have hcard : (goodFrames M d).card ≤ (physicalFrames M d).card * d.factorial := by
    apply FiniteFibers.card_le_of_fiber_bound (goodFrames M d) (physicalFrames M d)
      sortedChoice d.factorial
    · intro x hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · intro q _
      exact fixed_sorted_card_le q
  exact (goodFrames_card M d hM hd).trans (Nat.add_le_add_right hcard _)

theorem physicalFrame_properties (q : Fin (d + 2) → Fin M)
    (hq : q ∈ physicalFrames M d) :
    ∃ sumSlot : Fin (d + 2), sumSlot ≠ 0 ∧ StrictMono q ∧ q 0 = 0 ∧
      Robust (fun i => ((q i).val : ZMod M)) ∧
      (∑ i, (frameWeight d sumSlot i : ZMod M) * ((q i).val : ZMod M)) = 0 := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨s, hs, hm, hz, hr, hrel, _⟩ := sortedChoice_spec x hx
  exact ⟨s, hs, hm, hz, hr, hrel⟩

noncomputable def labelledFrames (M d : Nat) [NeZero M] :
    Finset ((Fin (d + 2) → Fin M) × Equiv.Perm (FiniteRoles.Role (d + 2))) := by
  classical
  exact (physicalFrames M d) ×ˢ Finset.univ

theorem labelledFrames_card : (labelledFrames M d).card =
    (physicalFrames M d).card * (d + 3).factorial := by
  classical
  simp [labelledFrames, FiniteRoles.Role, Fintype.card_perm, Nat.add_assoc]

end CoefficientTwoPrecision.SortedFrameSupply

#print axioms CoefficientTwoPrecision.SortedFrameSupply.physicalFrames_card_lower
#print axioms CoefficientTwoPrecision.SortedFrameSupply.physicalFrame_properties
#print axioms CoefficientTwoPrecision.SortedFrameSupply.labelledFrames_card
