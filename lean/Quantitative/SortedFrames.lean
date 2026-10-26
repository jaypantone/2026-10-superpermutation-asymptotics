import Quantitative.SortedCuts
import Quantitative.FrameOrbits
import Quantitative.AffineReconstruction

/-!
# Actual sorted frames with the physical affine relation

Every retained ordered coordinate vector gives an increasing tuple of
background cuts. Sorting retains a bijection to its formal points, which
identifies the unique anchored zero and the distinguished sum point. The
relation used in positional reconstruction is proved for these actual cuts.
-/

namespace CoefficientTwoPrecision.SortedFrames

open FrameAlgebra FrameCounting FrameOrbits RobustMatching SortedCuts AffineReconstruction

def formalWeight (d : Nat) : Point d → Int
  | none => (d : Int) - 1
  | some none => 1
  | some (some _) => -1

theorem formal_relation {M d : Nat} (x : Fin d → Fin M) :
    (∑ p, (formalWeight d p : ZMod M) * cuts x p) = 0 := by
  simp [Fintype.sum_option, formalWeight, cuts, coordinate, ite_mul,
    Finset.sum_neg_distrib]

theorem good_frame_sorted {M d : Nat} [NeZero M] (x : Fin d → Fin M)
    (hx : x ∈ goodFrames M d) :
    ∃ q : Fin (d + 2) → Fin M, ∃ sumSlot : Fin (d + 2),
      sumSlot ≠ 0 ∧ StrictMono q ∧ q 0 = 0 ∧
        Robust (fun i => ((q i).val : ZMod M)) ∧
        (∑ i, (frameWeight d sumSlot i : ZMod M) * ((q i).val : ZMod M)) = 0 ∧
        ∃ order : Fin (d + 2) ≃ Point d,
          order 0 = none ∧ order sumSlot = some none ∧
            ∀ i, (q i).val = (cuts x (order i)).val := by
  classical
  have hr := goodFrames_robust hx
  have hc : Fintype.card (Point d) = d + 2 := by simp [Point, Nat.add_assoc]
  obtain ⟨q, order, hmono, hvalue, hrobust⟩ := exists_sorted (cuts x) hr (d + 2) hc
  have hzero : cuts x none = 0 := by simp [cuts, coordinate]
  have hqzero : q 0 = 0 := sorted_zero (cuts x) (d + 2) (by omega)
    q order hmono hvalue none hzero
  have horderzero : order 0 = none := by
    apply robust_injective (cuts x) hr
    apply ZMod.val_injective M
    rw [← hvalue 0, hqzero, hzero]
    simp
  let sumSlot := order.symm (some none)
  have hsum : order sumSlot = some none := order.apply_symm_apply _
  have hsne : sumSlot ≠ 0 := by
    intro h
    rw [h, horderzero] at hsum
    cases hsum
  have hweight (i : Fin (d + 2)) :
      frameWeight d sumSlot i = formalWeight d (order i) := by
    by_cases hi0 : i = 0
    · subst i
      simp [frameWeight, horderzero, formalWeight]
    · by_cases his : i = sumSlot
      · subst i
        simp [frameWeight, hsne, hsum, formalWeight]
      · have hn : order i ≠ none := fun h => hi0 (order.injective (h.trans horderzero.symm))
        have hs : order i ≠ some none := fun h => his (order.injective (h.trans hsum.symm))
        cases h : order i with
        | none => exact False.elim (hn h)
        | some p =>
          cases p with
          | none => exact False.elim (hs h)
          | some j => simp [frameWeight, hi0, his, formalWeight]
  have hcast (i : Fin (d + 2)) : ((q i).val : ZMod M) = cuts x (order i) := by
    rw [hvalue i]
    exact ZMod.natCast_zmod_val _
  refine ⟨q, sumSlot, hsne, hmono, hqzero, hrobust, ?_, order, horderzero, hsum, hvalue⟩
  calc
    ∑ i, (frameWeight d sumSlot i : ZMod M) * ((q i).val : ZMod M) =
        ∑ p, (formalWeight d p : ZMod M) * cuts x p := by
      apply Fintype.sum_equiv order
      intro i
      rw [hweight, hcast]
    _ = 0 := formal_relation x

end CoefficientTwoPrecision.SortedFrames

#print axioms CoefficientTwoPrecision.SortedFrames.good_frame_sorted
