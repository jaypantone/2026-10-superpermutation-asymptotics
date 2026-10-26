import Quantitative.UniformPacking
import Quantitative.GuardCatalogue
import Quantitative.CandidateFactorization

/-!
# The actual finite candidate space with a fixed selected frame family

A candidate is an active block, an injective assignment of guard cuts,
and one labelled frame from the single uniformly separated selection.
The frame selection is a parameter shared by all blocks and backgrounds.
-/

namespace CoefficientTwoPrecision.CandidateSpace

open GuardCatalogue LabelledReconstruction

abbrev Candidate (m d A : Nat) :=
  Active d A × (Fin (guardNumber d A) ↪ Fin m) × Labelled (m + guardNumber d A) d

noncomputable def candidates (m d A : Nat)
    (S : Finset (Labelled (m + guardNumber d A) d)) : Finset (Candidate m d A) := by
  classical
  exact Finset.univ ×ˢ (Finset.univ ×ˢ S)

theorem mem_candidates (m d A : Nat)
    (S : Finset (Labelled (m + guardNumber d A) d)) (candidate : Candidate m d A) :
    candidate ∈ candidates m d A S ↔ candidate.2.2 ∈ S := by
  classical
  simp only [candidates, Finset.mem_product, Finset.mem_univ, true_and]

theorem candidates_card (m d A : Nat)
    (S : Finset (Labelled (m + guardNumber d A) d)) :
    (candidates m d A S).card =
      (A * ((d + 3) * A)) * m.descFactorial (guardNumber d A) * S.card := by
  classical
  simp only [candidates, Finset.card_product, Finset.card_univ,
    Fintype.card_embedding_eq, Fintype.card_fin, ActiveGrid.blocks_card, mul_assoc]

theorem guard_number_eq (d : Nat) :
    guardNumber d (sourceA (d + 3)) = CandidateFactorization.guardCount (d + 3) := by
  unfold guardNumber CandidateFactorization.guardCount sourceWidth
  congr 1
  ring

theorem prescribed_card (m d : Nat)
    (S : Finset (Labelled (m + guardNumber d (sourceA (d + 3))) d))
    (hS : S.card = ⌊sourceEta (d + 3) *
      ((m + guardNumber d (sourceA (d + 3)) : Nat) : ℚ) ^ d⌋₊) :
    (candidates m d (sourceA (d + 3)) S).card =
      CandidateFactorization.candidateCount (d + 3) m := by
  rw [candidates_card, hS, guard_number_eq]
  unfold CandidateFactorization.candidateCount CandidateFactorization.backgroundSize
  simp only [Nat.add_sub_cancel, sourceGridCount]
  ring

end CoefficientTwoPrecision.CandidateSpace

#print axioms CoefficientTwoPrecision.CandidateSpace.candidates_card
#print axioms CoefficientTwoPrecision.CandidateSpace.prescribed_card
