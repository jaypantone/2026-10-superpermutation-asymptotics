import Quantitative.PositionalCatalogue
import Quantitative.CyclicLabelCount

/-!
# Counting labelled target reconstructions for two fixed joint states

For each positional witness the target cut tuple is fixed. At most two
initial label assignments have the required current retained labels. Taking
unions counts repeated witnesses safely and includes coincident envelopes.
-/

namespace CoefficientTwoPrecision.LabelledReconstruction

open FiniteRoles

variable {M d : Nat} [NeZero M]

abbrev Labelled (M d : Nat) :=
  (Fin (d + 2) → Fin M) × Equiv.Perm (Role (d + 2))

noncomputable def forMatching
    (source leftPhase rightPhase : Fin (d + 2) → ZMod M)
    (sourceLabels targetAction : Equiv.Perm (Role (d + 2)))
    (omitted : Fin (d + 2)) (offset sumIndex : Fin (d + 1))
    (other : Fin (d + 2)) : Finset (Labelled M d) := by
  classical
  exact (PositionalCatalogue.candidates source leftPhase rightPhase
    omitted offset sumIndex other).biUnion (fun p =>
      (CyclicLabelCount.candidates sourceLabels targetAction omitted other offset).image
        (fun initial => ((fun i => AnchoredReconstruction.residue (p.1 i)), initial)))

theorem forMatching_card
    (source leftPhase rightPhase : Fin (d + 2) → ZMod M)
    (sourceLabels targetAction : Equiv.Perm (Role (d + 2)))
    (omitted : Fin (d + 2)) (offset sumIndex : Fin (d + 1)) (other : Fin (d + 2)) :
    (forMatching source leftPhase rightPhase sourceLabels targetAction omitted offset sumIndex other).card ≤
      (PositionalCatalogue.candidates source leftPhase rightPhase omitted offset sumIndex other).card * 2 := by
  classical
  apply FiniteFibers.bad_union_count
  intro p _
  exact Finset.card_image_le.trans (CyclicLabelCount.candidates_card sourceLabels targetAction
    omitted other offset)

noncomputable def all
    (source leftPhase rightPhase : Fin (d + 2) → ZMod M)
    (sourceLabels targetAction : Equiv.Perm (Role (d + 2))) : Finset (Labelled M d) := by
  classical
  exact Finset.univ.biUnion (fun omitted => Finset.univ.biUnion (fun offset =>
    Finset.univ.biUnion (fun sumIndex => Finset.univ.biUnion (fun other =>
      forMatching source leftPhase rightPhase sourceLabels targetAction omitted offset sumIndex other))))

theorem all_card (hd : 2 ≤ d)
    (source leftPhase rightPhase : Fin (d + 2) → ZMod M)
    (sourceLabels targetAction : Equiv.Perm (Role (d + 2))) :
    (all source leftPhase rightPhase sourceLabels targetAction).card ≤
      (d + 2) * (d + 1) ^ 2 * (2 * d) * 2 := by
  classical
  calc
    (all source leftPhase rightPhase sourceLabels targetAction).card ≤
        ∑ omitted, ∑ offset, ∑ sumIndex, ∑ other,
          (PositionalCatalogue.candidates source leftPhase rightPhase
            omitted offset sumIndex other).card * 2 := by
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro omitted _
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro offset _
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro sumIndex _
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro other _
      exact forMatching_card source leftPhase rightPhase sourceLabels targetAction
        omitted offset sumIndex other
    _ = (∑ omitted, ∑ offset, ∑ sumIndex, ∑ other,
          (PositionalCatalogue.candidates source leftPhase rightPhase
            omitted offset sumIndex other).card) * 2 := by simp only [Finset.sum_mul]
    _ ≤ (d + 2) * (d + 1) ^ 2 * (2 * d) * 2 :=
      Nat.mul_le_mul_right 2 (PositionalCatalogue.witness_count hd source leftPhase rightPhase)

theorem mem_all
    (source leftPhase rightPhase target : Fin (d + 2) → ZMod M)
    (sourceLabels targetAction initial : Equiv.Perm (Role (d + 2)))
    (translation : ZMod M) (omitted other : Fin (d + 2)) (offset sumIndex : Fin (d + 1))
    (hpos : (target, translation) ∈ PositionalCatalogue.candidates source leftPhase rightPhase
      omitted offset sumIndex other)
    (hlabels : ∀ i : Fin (d + 1), sourceLabels (some (omitted.succAbove (i + offset))) =
      (targetAction.trans initial) (some (other.succAbove i))) :
    ((fun i => AnchoredReconstruction.residue (target i)), initial) ∈
      all source leftPhase rightPhase sourceLabels targetAction := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨omitted, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨offset, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨sumIndex, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨other, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(target, translation), hpos, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨initial, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlabels⟩, rfl⟩

end CoefficientTwoPrecision.LabelledReconstruction

#print axioms CoefficientTwoPrecision.LabelledReconstruction.all_card
#print axioms CoefficientTwoPrecision.LabelledReconstruction.mem_all
