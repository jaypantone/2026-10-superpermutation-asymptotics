import Quantitative.GlobalSourceFamily
import Quantitative.SourceSelection
import Quantitative.StageSourceCertificate

/-!
# Construction of the sparse-family supplier

The Stage's actual old and fresh letters label the finite control grid.
One universally separated frame selection is chosen, the two actual
deletions are applied, and every surviving candidate contributes its
constructed repaired contour. The global distinctness and count estimates
then give the actual WidthBlockFamily required by the sparse iteration.
-/

namespace CoefficientTwoPrecision.SparseFamilyConstruction

open SuperpermutationUpperBound GuardCatalogue CandidateFactorization
open CandidateSpace LabelledReconstruction StageState StageSourceCertificate
open SourceFamilyAdapter SourceAdvancement SourceUniverse SparseStageIteration

theorem supplier (r : Nat) (hr : 6 ≤ r) : SparseFamilySupplier r := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d : Nat, r = d + 3 := ⟨r - 3, by omega⟩
  have hd : 3 ≤ d := by omega
  intro m stage hdiv hm
  have hs := SourceSelection.size_conditions d m hd hm
  have hA := sourceA_pos (d + 3) hr
  letI : NeZero (m + guardNumber d (sourceA (d + 3))) := ⟨by omega⟩
  obtain ⟨hwidth, hnd, h9, h10, hnext, hnext9⟩ :=
    alphabet_data stage (sourceWidth (d + 3)) (ConstructionSize.width_positive (d + 3) hr)
  have hwidthGrid : (controls stage (sourceWidth (d + 3))).length =
      (d + 3) * ((d + 3) * sourceA (d + 3)) :=
    hwidth.trans (SourceSelection.control_width d)
  obtain ⟨old, physical, ho, hl, hcross, hword, hcontrol, hold⟩ :=
    GridAlphabet.exists_labels (controls stage (sourceWidth (d + 3))) stage.A0
      hwidthGrid stage.size hnd
  obtain ⟨S, hS, hcard, hraw, hretention, hpacking⟩ := SourceSelection.exists_selection d m hd hm
  let rowIndex : FiniteRoles.Role (d + 2) ≃ Fin (d + 3) :=
    Fintype.equivFinOfCardEq (by simp [FiniteRoles.Role])
  have holdPos : 0 < stage.A0.length := by rw [stage.size]; exact hs.1
  have hfamily := GlobalSourceFamily.exists_family hA old ho physical hl hcross
    (controls stage (sourceWidth (d + 3))) stage.A0 rowIndex S hs.1 hd hs.2.1
    hs.2.2.2.1 (SourceSelection.background_divisible d m hd hdiv)
    hs.2.2.2.2.2.1 hs.2.2.2.2.2.2 holdPos hnd h9 hword hold hcontrol hS
    (fun bg embed hb he hc => hpacking bg embed hb he hc)
  rw [SourceSelection.contour_height d m hd] at hfamily
  obtain ⟨F, hlength, hinsertion, hdistinct, hcounts⟩ := hfamily
  have hM : m + guardNumber d (sourceA (d + 3)) = backgroundSize (d + 3) m := by
    rw [guard_number_eq]
    rfl
  have hK := CatalogueBounds.occurrence_bound d (sourceA (d + 3)) hA
  change PrimaryCatalogue.occurrenceBound d (sourceA (d + 3)) ≤
    52 * (d + 3) ^ 4 * sourceWidth (d + 3) ^ 2 at hK
  apply StageSourceCertificate.from_contours (d + 3) hr stage hm F hinsertion hdistinct
  · rw [hlength]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hretention
  · intro C hC
    have herror := (hcounts C hC).2.2
    have hbound :
        ((10 * (d + 3) ^ 2 * PrimaryCatalogue.occurrenceBound d (sourceA (d + 3)) *
          (m + guardNumber d (sourceA (d + 3))) : Nat) : ℚ) ≤
        ((10 * (d + 3) ^ 2 * (52 * (d + 3) ^ 4 * sourceWidth (d + 3) ^ 2) *
          (m + guardNumber d (sourceA (d + 3))) : Nat) : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right (m + guardNumber d (sourceA (d + 3)))
        (Nat.mul_le_mul_left (10 * (d + 3) ^ 2) hK)
    have hfinal := herror.trans hbound
    rw [hM] at hfinal
    have hbaseline :
        (((backgroundSize (d + 3) m) *
          ((d + 3 - 2) * backgroundSize (d + 3) m + (d + 3) * (d + 3 - 1) + 1) : Nat) : ℚ) =
        (((d + 3 : Nat) : ℚ) - 2) * (backgroundSize (d + 3) m : ℚ) ^ 2 +
          (((d + 3 : Nat) : ℚ) * (((d + 3 : Nat) : ℚ) - 1) + 1) * backgroundSize (d + 3) m := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (show 2 ≤ d + 3 by omega),
        Nat.cast_sub (show 1 ≤ d + 3 by omega), Nat.cast_one, Nat.cast_ofNat]
      ring
    rw [hbaseline] at hfinal
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hfinal
  · intro C hC
    simpa only [hM] using (hcounts C hC).1
  · intro C hC
    exact (hcounts C hC).2.1

end CoefficientTwoPrecision.SparseFamilyConstruction

#print axioms CoefficientTwoPrecision.SparseFamilyConstruction.supplier
