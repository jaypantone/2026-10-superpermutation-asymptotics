import Quantitative.AnchoredReconstruction
import Mathlib.Data.Fin.Tuple.Basic

/-!
# A finite catalogue of positional reconstruction candidates

Delete one source slot and one target slot, and match the remaining slots
in their cyclic order. For each cyclic offset and possible target sum slot,
the affine relation gives a finite set of actual anchored target tuples and
translations. The count below permits the observed vector to change with
the omitted target slot. It therefore counts the full reconstruction menu.
-/

namespace CoefficientTwoPrecision.PositionalCatalogue

open AnchoredReconstruction AffineReconstruction

variable {M d : Nat} [NeZero M]

/-- The translated target coordinates forced by one cyclic matching.
The value at the omitted coordinate is immaterial. -/
def observation (source leftPhase rightPhase : Fin (d + 2) → ZMod M)
    (sourceOmitted targetOmitted : Fin (d + 2)) (offset : Fin (d + 1)) :
    Fin (d + 2) → ZMod M :=
  Fin.insertNth targetOmitted 0 (fun j =>
    source (sourceOmitted.succAbove (j + offset)) +
      leftPhase (sourceOmitted.succAbove (j + offset)) -
        rightPhase (targetOmitted.succAbove j))

def candidates (source leftPhase rightPhase : Fin (d + 2) → ZMod M)
    (sourceOmitted : Fin (d + 2)) (offset sumIndex : Fin (d + 1))
    (targetOmitted : Fin (d + 2)) :=
  targets 0 (frameWeight d sumIndex.succ)
    (observation source leftPhase rightPhase sourceOmitted targetOmitted offset) targetOmitted

theorem candidates_mem (source leftPhase rightPhase target : Fin (d + 2) → ZMod M)
    (translation : ZMod M) (sourceOmitted targetOmitted : Fin (d + 2))
    (offset sumIndex : Fin (d + 1)) (hanchor : target 0 = 0)
    (hrel : (∑ i, (frameWeight d sumIndex.succ i : ZMod M) * target i) = 0)
    (hmatch : ∀ j : Fin (d + 1),
      target (targetOmitted.succAbove j) + translation =
        source (sourceOmitted.succAbove (j + offset)) +
          leftPhase (sourceOmitted.succAbove (j + offset)) -
            rightPhase (targetOmitted.succAbove j)) :
    (target, translation) ∈ candidates source leftPhase rightPhase sourceOmitted offset
      sumIndex targetOmitted := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hanchor, hrel, ?_⟩
  intro i hi
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
  simpa only [observation, Fin.insertNth_apply_succAbove] using hmatch j

theorem missing_sum_bound (hd : 2 ≤ d)
    (source leftPhase rightPhase : Fin (d + 2) → ZMod M)
    (sourceOmitted : Fin (d + 2)) (offset sumIndex : Fin (d + 1)) :
    (∑ targetOmitted, (candidates source leftPhase rightPhase sourceOmitted offset
      sumIndex targetOmitted).card) ≤ 2 * d := by
  calc
    ∑ targetOmitted, (candidates source leftPhase rightPhase sourceOmitted offset
        sumIndex targetOmitted).card ≤
        ∑ targetOmitted, (frameWeight d sumIndex.succ targetOmitted).natAbs := by
      apply Finset.sum_le_sum
      intro targetOmitted _
      exact targets_card 0 _ (frameWeight_sum d sumIndex.succ (Fin.succ_ne_zero _)) _
        targetOmitted (frameWeight_nonzero d hd sumIndex.succ targetOmitted)
    _ = 2 * d := frameWeight_abs_sum d hd sumIndex.succ

/-- Count witnesses, including repeats of the same target. This is the
polynomial bound before the two remaining control labels are assigned. -/
theorem witness_count (hd : 2 ≤ d)
    (source leftPhase rightPhase : Fin (d + 2) → ZMod M) :
    (∑ sourceOmitted, ∑ offset, ∑ sumIndex, ∑ targetOmitted,
      (candidates source leftPhase rightPhase sourceOmitted offset sumIndex targetOmitted).card)
      ≤ (d + 2) * (d + 1) ^ 2 * (2 * d) := by
  calc
    ∑ sourceOmitted, ∑ offset, ∑ sumIndex, ∑ targetOmitted,
        (candidates source leftPhase rightPhase sourceOmitted offset sumIndex targetOmitted).card
        ≤ ∑ _sourceOmitted : Fin (d + 2), ∑ _offset : Fin (d + 1),
            ∑ _sumIndex : Fin (d + 1), 2 * d := by
      apply Finset.sum_le_sum
      intro sourceOmitted _
      apply Finset.sum_le_sum
      intro offset _
      apply Finset.sum_le_sum
      intro sumIndex _
      exact missing_sum_bound hd source leftPhase rightPhase sourceOmitted offset sumIndex
    _ = (d + 2) * (d + 1) ^ 2 * (2 * d) := by simp; ring

end CoefficientTwoPrecision.PositionalCatalogue

#print axioms CoefficientTwoPrecision.PositionalCatalogue.candidates_mem
#print axioms CoefficientTwoPrecision.PositionalCatalogue.witness_count
