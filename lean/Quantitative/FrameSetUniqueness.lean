import Quantitative.FrameOrbits
import Quantitative.SumPoint

/-!
# The anchored cut set determines its coordinate set

The sum point is determined even for even or composite moduli. Removing it
and the anchored zero recovers precisely the original coordinate set. Thus
sorting all the cuts cannot identify different coordinate-set frames.
-/

namespace CoefficientTwoPrecision.FrameSetUniqueness

open FrameAlgebra FrameCounting FrameOrbits RobustMatching

variable {M d : Nat} [NeZero M]

def pointSet (x : Fin d → Fin M) : Finset (ZMod M) :=
  Finset.univ.image (cuts x)

theorem sum_cuts (x : Fin d → Fin M) :
    (∑ p, cuts x p) = 2 * cuts x (some none) := by
  simp [cuts, coordinate, Fintype.sum_option, ite_mul]
  ring

theorem pointSet_sum (x : Fin d → Fin M) (hx : x ∈ goodFrames M d) :
    (∑ z ∈ pointSet x, z) = 2 * cuts x (some none) := by
  classical
  rw [pointSet, Finset.sum_image]
  · exact sum_cuts x
  · intro p _ q _ heq
    exact robust_injective (cuts x) (goodFrames_robust hx) heq

theorem same_sum_point (x y : Fin d → Fin M)
    (hx : x ∈ goodFrames M d) (hy : y ∈ goodFrames M d)
    (hset : pointSet x = pointSet y) : cuts x (some none) = cuts y (some none) := by
  classical
  have hm : cuts y (some none) ∈ pointSet x := by
    rw [hset]
    exact Finset.mem_image.mpr ⟨some none, Finset.mem_univ _, rfl⟩
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hm
  have hs : 2 * cuts x (some none) = 2 * cuts y (some none) := by
    rw [← pointSet_sum x hx, ← pointSet_sum y hy, hset]
  have hdouble : 2 * cuts x p = 2 * cuts x (some none) := by
    rw [hp]
    exact hs.symm
  have heq := SumPoint.double_injective_on_robust (cuts x) (goodFrames_robust hx)
    p (some none) hdouble
  simpa only [heq] using hp

theorem coordinates_subset (x y : Fin d → Fin M)
    (hx : x ∈ goodFrames M d) (hy : y ∈ goodFrames M d)
    (hset : pointSet x = pointSet y) : coordinateSet x ⊆ coordinateSet y := by
  classical
  intro z hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
  have hm : cuts x (some (some i)) ∈ pointSet y := by
    rw [← hset]
    exact Finset.mem_image.mpr ⟨some (some i), Finset.mem_univ _, rfl⟩
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hm
  have hinj := robust_injective (cuts x) (goodFrames_robust hx)
  cases p with
  | none =>
    have heq : cuts x (some (some i)) = cuts x none := by
      simpa [cuts, coordinate] using hp.symm
    have hbad := hinj heq
    cases hbad
  | some p =>
    cases p with
    | none =>
      have heq : cuts x (some (some i)) = cuts x (some none) :=
        hp.symm.trans (same_sum_point x y hx hy hset).symm
      have hbad := hinj heq
      cases hbad
    | some j =>
      have heq : (y j).val = (x i).val := by
        have hv := congrArg ZMod.val hp
        simpa only [cuts_coordinate, ZMod.val_natCast_of_lt (y j).isLt,
          ZMod.val_natCast_of_lt (x i).isLt] using hv
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, Fin.ext heq⟩

theorem same_coordinateSet (x y : Fin d → Fin M)
    (hx : x ∈ goodFrames M d) (hy : y ∈ goodFrames M d)
    (hset : pointSet x = pointSet y) : coordinateSet x = coordinateSet y :=
  Finset.Subset.antisymm (coordinates_subset x y hx hy hset)
    (coordinates_subset y x hy hx hset.symm)

end CoefficientTwoPrecision.FrameSetUniqueness

#print axioms CoefficientTwoPrecision.FrameSetUniqueness.same_coordinateSet
