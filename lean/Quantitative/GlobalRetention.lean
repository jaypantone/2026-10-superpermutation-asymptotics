import Quantitative.ProximityDeletion
import Quantitative.ProximityNormalization
import Quantitative.SourceCountErrors

/-!
# The retained fraction of the actual global candidate set

Both deletions act on the same fixed selected frame family. The first
loss and the normalized maximum of the two proximity cases give the
retention error required by the actual source-count estimates.
-/

namespace CoefficientTwoPrecision.GlobalRetention

open GuardCatalogue CandidateSpace LabelledReconstruction CatalogueBounds
open ProximitySurvivors ProximityDeletion ProximityNormalization GuardRelativeLoss

theorem proximity_loss {m d A : Nat} [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hd : 3 ≤ d) (hA : 0 < A)
    (hM : m + guardNumber d A ≤ 2 * m) (hsize : guardNumber d A ^ 2 ≤ m)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d)
    (hhalf : sourceEta (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 ≤ S.card) :
    ((GuardCandidateLoss.retained m d A hA S).card : ℚ) - (survivors m d A hA S).card ≤
      (candidates m d A S).card *
        ((7118280 : ℚ) * (d + 3) ^ 22 * (width d A : ℚ) ^ 4 / m) := by
  have hG := guard_positive d A hA
  have hGm : guardNumber d A ≤ m := by nlinarith
  have hmax := maximum_scaled m (m + guardNumber d A) (guardNumber d A) d
    (m.descFactorial (guardNumber d A)) S.card (by omega) hG (by omega)
    (falling_half m (guardNumber d A) hm hGm hsize) (selected_scaled d _ S.card hhalf)
  have hmax' : m * scaledBound m d A S.card ≤
      (d - 1).factorial *
        (1560 * (d + 3) ^ 13 * m.descFactorial (guardNumber d A) * S.card) := by
    simpa only [scaledBound, guardBound, frameBound, mul_assoc] using hmax
  have hpair : pairCount d A ≤ 4563 * (d + 3) ^ 9 * width d A ^ 4 :=
    proximity_type_bound d A hd hA
  have hdel := deleted_scaled hm hM hd hA S hS
  let removed := (GuardCandidateLoss.retained m d A hA S).card - (survivors m d A hA S).card
  have hscaled : (d - 1).factorial * (m * removed) ≤
      (d - 1).factorial *
        ((7118280 * (d + 3) ^ 22 * width d A ^ 4) * (candidates m d A S).card) := by
    calc
      (d - 1).factorial * (m * removed) = m * ((d - 1).factorial * removed) := by ring
      _ ≤ m * ((A * ((d + 3) * A)) * pairCount d A * scaledBound m d A S.card) :=
        Nat.mul_le_mul_left m hdel
      _ = ((A * ((d + 3) * A)) * pairCount d A) * (m * scaledBound m d A S.card) := by ring
      _ ≤ ((A * ((d + 3) * A)) * pairCount d A) *
          ((d - 1).factorial * (1560 * (d + 3) ^ 13 * m.descFactorial (guardNumber d A) * S.card)) :=
        Nat.mul_le_mul_left _ hmax'
      _ ≤ ((A * ((d + 3) * A)) * (4563 * (d + 3) ^ 9 * width d A ^ 4)) *
          ((d - 1).factorial * (1560 * (d + 3) ^ 13 * m.descFactorial (guardNumber d A) * S.card)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpair)
      _ = _ := by rw [candidates_card]; ring
  have hnat := Nat.le_of_mul_le_mul_left hscaled (Nat.factorial_pos (d - 1))
  have hsub := Finset.card_le_card (survivors_subset hA S)
  have hrat : (m : ℚ) *
      (((GuardCandidateLoss.retained m d A hA S).card : ℚ) - (survivors m d A hA S).card) ≤
        (7118280 * ((d : ℚ) + 3) ^ 22 * (width d A : ℚ) ^ 4) * (candidates m d A S).card := by
    have hcast : ((m * removed : Nat) : ℚ) ≤
        (((7118280 * (d + 3) ^ 22 * width d A ^ 4) * (candidates m d A S).card : Nat) : ℚ) := by
      exact_mod_cast hnat
    simpa only [removed, Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_pow, Nat.cast_add,
      Nat.cast_ofNat] using hcast
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (show (0 : ℚ) < m by exact_mod_cast hm)).mpr
  nlinarith

theorem total_loss {m d A : Nat} [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hd : 3 ≤ d) (hA : 0 < A)
    (hM : m + guardNumber d A ≤ 2 * m) (hsize : guardNumber d A ^ 2 ≤ m)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d)
    (hhalf : sourceEta (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 ≤ S.card) :
    ((candidates m d A S).card : ℚ) - (survivors m d A hA S).card ≤
      (candidates m d A S).card *
        (SourceCountErrors.deletionNumerator (d + 3) (width d A) / m) := by
  have hfirst := GuardRelativeLoss.retained_loss m d A hm (by omega) hA hsize S
  have hsecond := proximity_loss hm hd hA hM hsize S hS hhalf
  have hsum := add_le_add hfirst hsecond
  unfold SourceCountErrors.deletionNumerator
  convert hsum using 1 <;> ring

theorem retention_error {m d A : Nat} [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hd : 3 ≤ d) (hA : 0 < A)
    (hM : m + guardNumber d A ≤ 2 * m) (hsize : guardNumber d A ^ 2 ≤ m)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d)
    (hhalf : sourceEta (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 ≤ S.card) :
    |((survivors m d A hA S).card : ℚ) / (candidates m d A S).card - 1| ≤
      SourceCountErrors.deletionNumerator (d + 3) (width d A) / m := by
  have hG := guard_positive d A hA
  have hGm : guardNumber d A ≤ m := by nlinarith
  have hguards : 0 < m.descFactorial (guardNumber d A) := Nat.descFactorial_pos.mpr hGm
  have heta := CandidateFactorization.eta_pos (d + 3) (by omega)
  have hMpos : (0 : ℚ) < ((m + guardNumber d A : Nat) : ℚ) := by exact_mod_cast (by omega : 0 < m + guardNumber d A)
  have hselected : 0 < S.card := by
    have hpositive : 0 < sourceEta (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 := by positivity
    exact_mod_cast hpositive.trans_le hhalf
  have hraw : 0 < (candidates m d A S).card := by rw [candidates_card]; positivity
  have hrawQ : (0 : ℚ) < (candidates m d A S).card := by exact_mod_cast hraw
  have hupper : ((survivors m d A hA S).card : ℚ) ≤ (candidates m d A S).card := by
    exact_mod_cast Finset.card_le_card ((survivors_subset hA S).trans (GuardCandidateLoss.retained_subset m d A hA S))
  have hloss := total_loss hm hd hA hM hsize S hS hhalf
  have hlo : 1 - SourceCountErrors.deletionNumerator (d + 3) (width d A) / m ≤
      ((survivors m d A hA S).card : ℚ) / (candidates m d A S).card := by
    apply (le_div_iff₀ hrawQ).mpr
    nlinarith
  have hhi := (div_le_one hrawQ).mpr hupper
  have herror : 0 ≤ SourceCountErrors.deletionNumerator (d + 3) (width d A) / m := by
    unfold SourceCountErrors.deletionNumerator
    positivity
  apply abs_le.mpr
  constructor <;> linarith

end CoefficientTwoPrecision.GlobalRetention

#print axioms CoefficientTwoPrecision.GlobalRetention.proximity_loss
#print axioms CoefficientTwoPrecision.GlobalRetention.retention_error
