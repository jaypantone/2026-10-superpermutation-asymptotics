import Quantitative.ProximityPairCount

/-!
# Global cardinality of the actual proximity deletion

The two rank cases partition the pair-event catalogue. A common upper
bound is their maximum, so the final estimate does not pay for both
cases on every entry. All finite sets below are subsets of the fixed
candidate product used by the construction.
-/

namespace CoefficientTwoPrecision.ProximityDeletion

open GuardCatalogue CandidateSpace LabelledReconstruction PrimaryCatalogue PrimaryRank
open ProximityCatalogue ProximitySurvivors ProximityPairCount

variable {m d A : Nat}

def guardBound (m d A selected : Nat) : Nat :=
  selected * (m ^ (guardNumber d A - 1) * (2 * (d - 1) ^ 2))

def frameBound (m d A : Nat) : Nat :=
  m.descFactorial (guardNumber d A) * (d + 3).factorial *
    ((d + 1) * d * ((m + guardNumber d A) ^ (d - 1) * (2 * (d - 1) ^ 2)))

def scaledBound (m d A selected : Nat) : Nat :=
  max ((d - 1).factorial * guardBound m d A selected) (frameBound m d A)

def pairCount (d A : Nat) : Nat := 3 * (2 * radius d + 1) * (typeCount d A) ^ 2

noncomputable def badFiber (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) : Finset (Fiber m d A) := by
  classical
  exact Finset.univ.biUnion (pairSolutions hA active S)

noncomputable def allBad (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) : Finset (Candidate m d A) := by
  classical
  exact (candidates m d A S).filter (Bad hA)

noncomputable def badFiberFilter (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) : Finset (Fiber m d A) := by
  classical
  exact ((Finset.univ : Finset (Fin (guardNumber d A) ↪ Fin m)) ×ˢ S).filter
    (fun p => Bad hA (active, p))

theorem badFiber_eq (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) :
    badFiber hA active S = badFiberFilter hA active S := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨event, _, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hbase, hdistinct, heq⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hbase, ⟨event, hdistinct, heq⟩⟩
  · intro hp
    obtain ⟨hbase, event, hdistinct, heq⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_biUnion.mpr ⟨event, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hbase, hdistinct, heq⟩⟩

theorem allBad_card (hA : 0 < A) (S : Finset (Labelled (m + guardNumber d A) d)) :
    (allBad hA S).card = ∑ active : Active d A, (badFiber hA active S).card := by
  classical
  simp only [allBad, candidates, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro active _
  rw [badFiber_eq]
  simp only [badFiberFilter, Finset.card_filter, Finset.sum_product]

theorem pair_scaled_count [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hM : m + guardNumber d A ≤ 2 * m) (hd : 3 ≤ d) (hA : 0 < A)
    (active : Active d A) (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d)
    (event : PairEvent d A hA active) :
    (d - 1).factorial * (pairSolutions hA active S event).card ≤ scaledBound m d A S.card := by
  classical
  by_cases hzero : ∀ u, guardCross hA active event.1 event.2.1 u = 0
  · exact (guard_free_count hm hM hd hA active S hS event hzero).trans (le_max_right _ _)
  · push_neg at hzero
    obtain ⟨u, hu⟩ := hzero
    exact (Nat.mul_le_mul_left (d - 1).factorial
      (guard_variable_count hm (by omega) hA active S event u hu)).trans (le_max_left _ _)

theorem badFiber_scaled_count [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hM : m + guardNumber d A ≤ 2 * m) (hd : 3 ≤ d) (hA : 0 < A)
    (active : Active d A) (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d) :
    (d - 1).factorial * (badFiber hA active S).card ≤
      pairCount d A * scaledBound m d A S.card := by
  classical
  calc
    (d - 1).factorial * (badFiber hA active S).card ≤
        (d - 1).factorial * ∑ event : PairEvent d A hA active,
          (pairSolutions hA active S event).card :=
      Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ event : PairEvent d A hA active,
        (d - 1).factorial * (pairSolutions hA active S event).card := Finset.mul_sum ..
    _ ≤ ∑ _event : PairEvent d A hA active, scaledBound m d A S.card := by
      apply Finset.sum_le_sum
      intro event _
      exact pair_scaled_count hm hM hd hA active S hS event
    _ = pairCount d A * scaledBound m d A S.card := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
        pairEvent_card, pairCount]

theorem allBad_scaled_count [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hM : m + guardNumber d A ≤ 2 * m) (hd : 3 ≤ d) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d) :
    (d - 1).factorial * (allBad hA S).card ≤
      (A * ((d + 3) * A)) * pairCount d A * scaledBound m d A S.card := by
  classical
  rw [allBad_card, Finset.mul_sum]
  calc
    (∑ active : Active d A, (d - 1).factorial * (badFiber hA active S).card) ≤
        ∑ _active : Active d A, pairCount d A * scaledBound m d A S.card := by
      apply Finset.sum_le_sum
      intro active _
      exact badFiber_scaled_count hm hM hd hA active S hS
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ActiveGrid.blocks_card, Nat.nsmul_eq_mul]
      ring

theorem deleted_le_allBad (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) :
    (GuardCandidateLoss.retained m d A hA S).card - (survivors m d A hA S).card ≤
      (allBad hA S).card := by
  classical
  have hsub : (GuardCandidateLoss.retained m d A hA S).filter (Bad hA) ⊆ allBad hA S := by
    intro c hc
    obtain ⟨hret, hbad⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr
      ⟨GuardCandidateLoss.retained_subset m d A hA S hret, hbad⟩
  have hcard := Finset.card_filter_add_card_filter_not
    (s := GuardCandidateLoss.retained m d A hA S) (Bad hA)
  have hle := Finset.card_le_card hsub
  change ((GuardCandidateLoss.retained m d A hA S).filter (Bad hA)).card +
    (survivors m d A hA S).card = (GuardCandidateLoss.retained m d A hA S).card at hcard
  omega

/-- The exact second deletion bound for the actual surviving candidates. -/
theorem deleted_scaled [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hM : m + guardNumber d A ≤ 2 * m) (hd : 3 ≤ d) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d) :
    (d - 1).factorial *
        ((GuardCandidateLoss.retained m d A hA S).card - (survivors m d A hA S).card) ≤
      (A * ((d + 3) * A)) * pairCount d A * scaledBound m d A S.card := by
  exact (Nat.mul_le_mul_left _ (deleted_le_allBad hA S)).trans
    (allBad_scaled_count hm hM hd hA S hS)

end CoefficientTwoPrecision.ProximityDeletion

#print axioms CoefficientTwoPrecision.ProximityDeletion.deleted_scaled
