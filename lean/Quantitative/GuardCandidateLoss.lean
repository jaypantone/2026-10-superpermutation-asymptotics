import Quantitative.CandidateSpace
import Quantitative.CatalogueBounds
import Quantitative.SourceCountFactors

/-!
# The first deletion in the actual finite candidate set

The selected labelled frames are fixed while the guard cuts vary. Thus
the same frame cardinality multiplies both the original set and the
guard-only loss bound. No uniform distribution assertion is used.
-/

namespace CoefficientTwoPrecision.GuardCandidateLoss

open GuardCatalogue CandidateSpace LabelledReconstruction

noncomputable def retained (m d A : Nat) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) : Finset (Candidate m d A) := by
  classical
  exact (candidates m d A S).filter (fun candidate =>
    candidate.2.1 ∈ goodEmbeddings m d A hA candidate.1)

theorem mem_retained (m d A : Nat) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) (candidate : Candidate m d A) :
    candidate ∈ retained m d A hA S ↔ candidate.2.2 ∈ S ∧
      candidate.2.1 ∈ goodEmbeddings m d A hA candidate.1 := by
  classical
  simp only [retained, Finset.mem_filter, mem_candidates]

theorem retained_subset (m d A : Nat) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) :
    retained m d A hA S ⊆ candidates m d A S := Finset.filter_subset _ _

theorem product_filter_card {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (t : Finset β) (u : Finset γ) (p : α → β → Prop)
    [DecidablePred (fun x : α × β × γ => p x.1 x.2.1)] [∀ a, DecidablePred (p a)] :
    ((s ×ˢ (t ×ˢ u)).filter (fun x => p x.1 x.2.1)).card =
      ∑ a ∈ s, (t.filter (p a)).card * u.card := by
  simp only [Finset.card_filter, Finset.sum_product, Finset.sum_const,
    Nat.nsmul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : p a b <;> simp [hab]

theorem retained_card (m d A : Nat) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) :
    (retained m d A hA S).card =
      ∑ active : Active d A, (goodEmbeddings m d A hA active).card * S.card := by
  classical
  simpa only [retained, candidates, Finset.filter_mem_eq_inter, Finset.univ_inter] using
    (product_filter_card (Finset.univ : Finset (Active d A)) Finset.univ S
      (fun active cuts => cuts ∈ goodEmbeddings m d A hA active))

def lossBound (m d A : Nat) : Nat :=
  GuardCatalogue.eventCount d A * (m ^ (guardNumber d A - 1) * (d - 1))

theorem retained_lower (m d A : Nat) (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) :
    (candidates m d A S).card ≤ (retained m d A hA S).card +
      (A * ((d + 3) * A)) * lossBound m d A * S.card := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Active d A)))
    (fun active _ => Nat.mul_le_mul_right S.card (goodEmbeddings_lower m d A hm hd hA active))
  simp only [Nat.add_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    ActiveGrid.blocks_card, Nat.nsmul_eq_mul] at h
  rw [candidates_card, retained_card]
  convert h using 1
  all_goals
    try unfold lossBound
    ring

end CoefficientTwoPrecision.GuardCandidateLoss

#print axioms CoefficientTwoPrecision.GuardCandidateLoss.retained_card
#print axioms CoefficientTwoPrecision.GuardCandidateLoss.retained_lower
