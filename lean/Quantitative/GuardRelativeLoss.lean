import Quantitative.GuardCandidateLoss

/-!
# The relative cost of deleting guard-only collisions

The actual cardinality inequality is normalized using the falling
factorial lower bound. The selected frame cardinality stays as the same
factor on both sides throughout the argument.
-/

namespace CoefficientTwoPrecision.GuardRelativeLoss

open GuardCatalogue GuardCandidateLoss CandidateSpace LabelledReconstruction CatalogueBounds

theorem falling_half (m G : Nat) (hm : 0 < m) (hG : G ≤ m) (hsize : G ^ 2 ≤ m) :
    m ^ G ≤ 2 * m.descFactorial G := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hsizeQ : (G : ℚ) ^ 2 ≤ m := by exact_mod_cast hsize
  have hG0 : (0 : ℚ) ≤ G := by positivity
  have he : (G : ℚ) * ((G : ℚ) - 1) / (2 * m) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 * m)).mpr
    nlinarith
  have hfall := (CountingRatios.falling_bounds m G hm hG).1
  have hlo : (1 / 2 : ℚ) ≤ (m.descFactorial G : ℚ) / (m : ℚ) ^ G := by linarith
  have hmul := (le_div_iff₀ (pow_pos hmQ G)).mp hlo
  have h : (m : ℚ) ^ G ≤ 2 * (m.descFactorial G : ℚ) := by linarith
  exact_mod_cast h

theorem guard_positive (d A : Nat) (hA : 0 < A) : 0 < guardNumber d A := by
  have h := Nat.mul_le_mul_left ((d + 3) ^ 2) (show 1 ≤ A from hA)
  have heq : (d + 3) * ((d + 3) * A) = (d + 3) ^ 2 * A := by ring
  unfold guardNumber
  rw [heq]
  simp only [Nat.mul_one] at h
  have hstrict : d + 3 < (d + 3) ^ 2 * A := by nlinarith
  omega

theorem scaled_loss (m d A : Nat) (hm : 0 < m) (hA : 0 < A)
    (hsize : guardNumber d A ^ 2 ≤ m) :
    m * lossBound m d A ≤
      (18 * (d + 3) ^ 2 * width d A ^ 3) * m.descFactorial (guardNumber d A) := by
  have hG := guard_positive d A hA
  have hGm : guardNumber d A ≤ m := by nlinarith
  have hhalf := falling_half m (guardNumber d A) hm hGm hsize
  have hcoef : GuardCatalogue.eventCount d A * (d - 1) ≤
      9 * (d + 3) ^ 2 * width d A ^ 3 := by
    calc
      GuardCatalogue.eventCount d A * (d - 1) ≤
          (9 * (d + 3) * width d A ^ 3) * (d + 3) :=
        Nat.mul_le_mul (guard_event_bound d A hA) (by omega)
      _ = 9 * (d + 3) ^ 2 * width d A ^ 3 := by ring
  have hpower : m * m ^ (guardNumber d A - 1) = m ^ guardNumber d A := by
    rw [← pow_succ', Nat.sub_add_cancel hG]
  calc
    m * lossBound m d A =
        (GuardCatalogue.eventCount d A * (d - 1)) * (m * m ^ (guardNumber d A - 1)) := by
      unfold lossBound
      ring
    _ = (GuardCatalogue.eventCount d A * (d - 1)) * m ^ guardNumber d A := by rw [hpower]
    _ ≤ (9 * (d + 3) ^ 2 * width d A ^ 3) * m ^ guardNumber d A :=
      Nat.mul_le_mul_right _ hcoef
    _ ≤ (9 * (d + 3) ^ 2 * width d A ^ 3) * (2 * m.descFactorial (guardNumber d A)) :=
      Nat.mul_le_mul_left _ hhalf
    _ = (18 * (d + 3) ^ 2 * width d A ^ 3) * m.descFactorial (guardNumber d A) := by ring

theorem retained_loss (m d A : Nat) (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A)
    (hsize : guardNumber d A ^ 2 ≤ m)
    (S : Finset (Labelled (m + guardNumber d A) d)) :
    ((candidates m d A S).card : ℚ) - (retained m d A hA S).card ≤
      (candidates m d A S).card *
        ((18 : ℚ) * (d + 3) ^ 2 * (width d A : ℚ) ^ 3 / m) := by
  have hbase := Nat.mul_le_mul_left m (retained_lower m d A hm hd hA S)
  have hscaled := Nat.mul_le_mul_left ((A * ((d + 3) * A)) * S.card)
    (scaled_loss m d A hm hA hsize)
  have hnat : m * (candidates m d A S).card ≤ m * (retained m d A hA S).card +
      (18 * (d + 3) ^ 2 * width d A ^ 3) * (candidates m d A S).card := by
    rw [candidates_card] at hbase ⊢
    nlinarith
  have hrat : (m : ℚ) * (candidates m d A S).card ≤
      (m : ℚ) * (retained m d A hA S).card +
        (18 * ((d : ℚ) + 3) ^ 2 * (width d A : ℚ) ^ 3) * (candidates m d A S).card := by
    exact_mod_cast hnat
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hmQ).mpr
  nlinarith

end CoefficientTwoPrecision.GuardRelativeLoss

#print axioms CoefficientTwoPrecision.GuardRelativeLoss.scaled_loss
#print axioms CoefficientTwoPrecision.GuardRelativeLoss.retained_loss
