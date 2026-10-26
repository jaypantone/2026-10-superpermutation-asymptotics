import Quantitative.GlobalRetention
import Quantitative.CandidateEvents

/-!
# The selected frames and retained candidates at the construction threshold

One selection works for every assignment of actual letters and every
guard background. Its cardinality is the prescribed floor, and the
actual two deletions satisfy the error used in the source estimates.
-/

namespace CoefficientTwoPrecision.SourceSelection

open GuardCatalogue CandidateSpace LabelledReconstruction CandidateFactorization
open SortedFrameSupply ProximitySurvivors ProximityCatalogue CatalogueBounds

theorem size_conditions (d m : Nat) (hd : 3 ≤ d)
    (hm : 4 * errorNumerator (d + 3) (sourceWidth (d + 3)) ≤ m) :
    0 < m ∧ 2 * (d + 2) ≤ m + guardNumber d (sourceA (d + 3)) ∧
      38 * (d + 3) ^ 4 ≤ m + guardNumber d (sourceA (d + 3)) ∧
      m + guardNumber d (sourceA (d + 3)) ≤ 2 * m ∧
      guardNumber d (sourceA (d + 3)) ^ 2 ≤ m ∧
      radius d < m + guardNumber d (sourceA (d + 3)) ∧
      (2 * (2 * (d + 3) + 1) + 1) * PrimaryCatalogue.occurrenceBound d (sourceA (d + 3)) <
        m + guardNumber d (sourceA (d + 3)) := by
  have hs := ConstructionSize.threshold_conditions (d + 3) m (by omega) hm
  have hA := sourceA_pos (d + 3) (by omega)
  have hG := guard_le d (sourceA (d + 3))
  have hW : width d (sourceA (d + 3)) = sourceWidth (d + 3) := rfl
  have hM : m + guardNumber d (sourceA (d + 3)) = backgroundSize (d + 3) m := by
    rw [guard_number_eq]
    rfl
  have hpower : d + 3 ≤ (d + 3) ^ 4 := le_self_pow₀ (by omega) (by decide)
  have hsmall : 4 * (d + 3) + 2 < backgroundSize (d + 3) m := by omega
  have hK := occurrence_bound d (sourceA (d + 3)) hA
  rw [hW] at hG hK
  have hG2 := Nat.pow_le_pow_left hG 2
  have hroom := (Nat.mul_le_mul_left (4 * (d + 3) + 3) hK).trans_lt hs.2.2.2.2.2.2
  rw [hM]
  refine ⟨hs.1, by omega, hs.2.2.2.1, by omega, by omega, ?_, ?_⟩
  · simpa only [radius] using hsmall
  · simpa only [show 2 * (2 * (d + 3) + 1) + 1 = 4 * (d + 3) + 3 by ring] using hroom

theorem background_divisible (d m : Nat) (hd : 3 ≤ d) (hm : d + 3 ∣ m) :
    d + 3 ∣ m + guardNumber d (sourceA (d + 3)) := by
  apply dvd_add hm
  unfold guardNumber
  exact Nat.dvd_sub (dvd_mul_right _ _) (dvd_refl _)

theorem contour_height (d m : Nat) (hd : 3 ≤ d) :
    m + guardNumber d (sourceA (d + 3)) + (d + 2) - 1 =
      m + sourceWidth (d + 3) - 2 := by
  rw [guard_number_eq]
  have hwidth := ConstructionSize.width_linear (d + 3) (by omega)
  unfold guardCount
  omega

theorem control_width (d : Nat) :
    sourceWidth (d + 3) = (d + 3) * ((d + 3) * sourceA (d + 3)) := by
  unfold sourceWidth
  ring

theorem exists_selection (d m : Nat) [NeZero (m + guardNumber d (sourceA (d + 3)))]
    (hd : 3 ≤ d)
    (hm : 4 * errorNumerator (d + 3) (sourceWidth (d + 3)) ≤ m) :
    ∃ S : Finset (Labelled (m + guardNumber d (sourceA (d + 3))) d),
      S ⊆ labelledFrames (m + guardNumber d (sourceA (d + 3))) d ∧
      S.card = ⌊sourceEta (d + 3) *
        ((m + guardNumber d (sourceA (d + 3)) : Nat) : ℚ) ^ d⌋₊ ∧
      (candidates m d (sourceA (d + 3)) S).card = candidateCount (d + 3) m ∧
      |((survivors m d (sourceA (d + 3)) (sourceA_pos (d + 3) (by omega)) S).card : ℚ) /
        candidateCount (d + 3) m - 1| ≤
          SourceCountErrors.deletionNumerator (d + 3) (sourceWidth (d + 3)) / m ∧
      ∀ {α : Type} (background : Fin (m + guardNumber d (sourceA (d + 3))) → α)
        (embed : FiniteRoles.Role (d + 2) → α),
        Function.Injective background → Function.Injective embed →
        (∀ i c, background i ≠ embed c) →
        ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
          ∀ first second : List α, LiteralPacking.InEnvelope background embed source first →
            LiteralPacking.InEnvelope background embed target second → ¬ first.IsRotated second := by
  have hs := size_conditions d m hd hm
  obtain ⟨S, hS, hcard, hsep⟩ := UniformPacking.exists_uniform_literal_separated hd
    (show 2 ≤ m + guardNumber d (sourceA (d + 3)) by omega) hs.2.2.1
  have hcandidates := prescribed_card m d S hcard
  have hhalf : sourceEta (d + 3) *
      ((m + guardNumber d (sourceA (d + 3)) : Nat) : ℚ) ^ d / 2 ≤ S.card := by
    rw [hcard, guard_number_eq]
    simpa only [Nat.add_sub_cancel, backgroundSize] using
      CandidatePositivity.selected_floor_half (d + 3) m (by omega) hm
  have hretention := GlobalRetention.retention_error hs.1 hd (sourceA_pos (d + 3) (by omega))
    hs.2.2.2.1 hs.2.2.2.2.1 S hS hhalf
  rw [hcandidates] at hretention
  exact ⟨S, hS, hcard, hcandidates, hretention, hsep⟩

end CoefficientTwoPrecision.SourceSelection

#print axioms CoefficientTwoPrecision.SourceSelection.size_conditions
#print axioms CoefficientTwoPrecision.SourceSelection.exists_selection
