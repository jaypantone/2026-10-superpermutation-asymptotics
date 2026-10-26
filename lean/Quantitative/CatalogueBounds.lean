import Quantitative.PrimaryCatalogue
import Quantitative.ConstructionParameters

/-!
# Polynomial bounds for the actual finite collision catalogues

The catalogues retain all coefficient assignments and all bounded right
sides. These bounds specialize their exact finite cardinalities to the
grid width W = r^2 A. The constants match the global deletion estimates.
-/

namespace CoefficientTwoPrecision.CatalogueBounds

open GuardCatalogue GuardEvents ActiveSlotEvents

def width (d A : Nat) : Nat := (d + 3) ^ 2 * A

theorem width_ge (d A : Nat) (hA : 0 < A) : d + 3 ≤ width d A := by
  have h := Nat.mul_le_mul_left ((d + 3) ^ 2) (show 1 ≤ A from hA)
  simp only [Nat.mul_one] at h
  unfold width
  nlinarith

theorem guard_le (d A : Nat) : guardNumber d A ≤ width d A := by
  unfold guardNumber width
  have h : (d + 3) * ((d + 3) * A) = (d + 3) ^ 2 * A := by ring
  rw [h]
  exact Nat.sub_le _ _

theorem stationary_bound (d A : Nat) (hA : 0 < A) :
    stationaryOffsetBound d (guardNumber d A) ≤ 4 * (d + 3) * width d A := by
  have hg := Nat.mul_le_mul_left (4 * d + 1) (guard_le d A)
  have hw := width_ge d A hA
  unfold stationaryOffsetBound
  nlinarith

theorem primary_bound (d A : Nat) (hA : 0 < A) :
    primaryOffsetBound d (guardNumber d A) ≤ 6 * (d + 3) * width d A := by
  have hfirst := stationary_bound d A hA
  have hw := width_ge d A hA
  have hlast := Nat.mul_le_mul (Nat.sub_le d 1)
    (show 2 * guardNumber d A + 1 ≤ 2 * width d A + 1 by have := guard_le d A; omega)
  have hg := Nat.mul_le_mul_left (4 * d + 1) (guard_le d A)
  unfold primaryOffsetBound stationaryOffsetBound
  nlinarith

theorem stationary_cells (d A : Nat) (hA : 0 < A) :
    2 * stationaryOffsetBound d (guardNumber d A) + 1 ≤ 9 * (d + 3) * width d A := by
  have h := stationary_bound d A hA
  have hw := width_ge d A hA
  nlinarith

theorem primary_cells (d A : Nat) (hA : 0 < A) :
    2 * primaryOffsetBound d (guardNumber d A) + 1 ≤ 13 * (d + 3) * width d A := by
  have h := primary_bound d A hA
  have hw := width_ge d A hA
  nlinarith

theorem guard_event_bound (d A : Nat) (hA : 0 < A) :
    GuardCatalogue.eventCount d A ≤ 9 * (d + 3) * width d A ^ 3 := by
  have hp : (d + 2) * (d + 1) ≤ (d + 3) ^ 2 := by nlinarith
  unfold GuardCatalogue.eventCount
  calc
    A * ((d + 3) * A) * (d + 3) * ((d + 2) * (d + 1)) *
        (2 * stationaryOffsetBound d (guardNumber d A) + 1) ≤
      (A * ((d + 3) * A) * (d + 3) * (d + 3) ^ 2) *
        (9 * (d + 3) * width d A) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) (stationary_cells d A hA)
    _ = 9 * (d + 3) * width d A ^ 3 := by unfold width; ring

theorem primary_type_bound (d A : Nat) (hA : 0 < A) :
    PrimaryCatalogue.typeCount d A ≤ 13 * (d + 3) ^ 4 * width d A ^ 2 := by
  have hI : (d + 3) * (A - 1) ≤ (d + 3) * A :=
    Nat.mul_le_mul_left _ (Nat.sub_le A 1)
  have hp : (d + 2) ^ 3 * (d + 1) ≤ (d + 3) ^ 4 := by
    calc
      (d + 2) ^ 3 * (d + 1) ≤ (d + 3) ^ 3 * (d + 3) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 3) (by omega)
      _ = (d + 3) ^ 4 := by ring
  unfold PrimaryCatalogue.typeCount
  calc
    (d + 3) * (A - 1) * (d + 2) ^ 3 * (d + 1) *
        (2 * primaryOffsetBound d (guardNumber d A) + 1) =
      ((d + 3) * (A - 1) * ((d + 2) ^ 3 * (d + 1))) *
        (2 * primaryOffsetBound d (guardNumber d A) + 1) := by ring
    _ ≤ ((d + 3) * A * (d + 3) ^ 4) * (13 * (d + 3) * width d A) :=
      Nat.mul_le_mul (Nat.mul_le_mul hI hp) (primary_cells d A hA)
    _ = 13 * (d + 3) ^ 4 * width d A ^ 2 := by unfold width; ring

theorem occurrence_bound (d A : Nat) (hA : 0 < A) :
    PrimaryCatalogue.occurrenceBound d A ≤ 52 * (d + 3) ^ 4 * width d A ^ 2 := by
  have hI : (d + 3) * (A - 1) ≤ (d + 3) * A :=
    Nat.mul_le_mul_left _ (Nat.sub_le A 1)
  have hpair : d * (d + 1) ≤ (d + 3) ^ 2 := by nlinarith
  have hp : (d + 2) ^ 2 * (d * (d + 1)) ≤ (d + 3) ^ 4 := by
    calc
      (d + 2) ^ 2 * (d * (d + 1)) ≤ (d + 3) ^ 2 * (d + 3) ^ 2 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) hpair
      _ = (d + 3) ^ 4 := by ring
  unfold PrimaryCatalogue.occurrenceBound
  calc
    4 * ((d + 3) * (A - 1)) * (d + 2) ^ 2 * d * (d + 1) *
        (2 * primaryOffsetBound d (guardNumber d A) + 1) =
      4 * (((d + 3) * (A - 1)) * ((d + 2) ^ 2 * (d * (d + 1)))) *
        (2 * primaryOffsetBound d (guardNumber d A) + 1) := by ring
    _ ≤ (4 * ((d + 3) * A * (d + 3) ^ 4)) *
        (13 * (d + 3) * width d A) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.mul_le_mul hI hp)) (primary_cells d A hA)
    _ = 52 * (d + 3) ^ 4 * width d A ^ 2 := by unfold width; ring

theorem proximity_type_bound (d A : Nat) (hd : 3 ≤ d) (hA : 0 < A) :
    3 * (2 * (4 * (d + 3) + 2) + 1) * PrimaryCatalogue.typeCount d A ^ 2 ≤
      4563 * (d + 3) ^ 9 * width d A ^ 4 := by
  have hwindow : 3 * (2 * (4 * (d + 3) + 2) + 1) ≤ 27 * (d + 3) := by omega
  calc
    3 * (2 * (4 * (d + 3) + 2) + 1) * PrimaryCatalogue.typeCount d A ^ 2 ≤
        (27 * (d + 3)) * (13 * (d + 3) ^ 4 * width d A ^ 2) ^ 2 :=
      Nat.mul_le_mul hwindow (Nat.pow_le_pow_left (primary_type_bound d A hA) 2)
    _ = 4563 * (d + 3) ^ 9 * width d A ^ 4 := by ring

theorem source_width (d : Nat) : width d (sourceA (d + 3)) = sourceWidth (d + 3) := rfl

end CoefficientTwoPrecision.CatalogueBounds

#print axioms CoefficientTwoPrecision.CatalogueBounds.guard_event_bound
#print axioms CoefficientTwoPrecision.CatalogueBounds.primary_type_bound
#print axioms CoefficientTwoPrecision.CatalogueBounds.occurrence_bound
#print axioms CoefficientTwoPrecision.CatalogueBounds.proximity_type_bound
