import Quantitative.StationaryRelations
import Quantitative.AffineReconstruction

/-!
# Automatic physical-label transport of the frame relation

A bijection from physical stationary labels to frame slots sends exactly
one label to the anchored zero and exactly one different label to the sum
slot. Their preimages determine an actual member of the finite coefficient
catalogue. No additional choice of coefficient vector is assumed.
-/

namespace CoefficientTwoPrecision.StationaryWeightTransport

open StationaryRelations AffineReconstruction

theorem exists_assignment {d : Nat} (first last : Fin (d + 2)) (hne : last ≠ first) :
    ∃ a : Assignment d, a.1 = first ∧ second a = last := by
  obtain ⟨other, hother⟩ := Fin.exists_succAbove_eq hne
  exact ⟨(first, other), rfl, hother⟩

/-- Reindexing the actual frame coefficients produces one of the listed
physical-label assignments, including its exact two distinguished labels. -/
theorem physical_assignment {d : Nat} (sumSlot : Fin (d + 2)) (hsum : sumSlot ≠ 0)
    (role : Fin (d + 2) ≃ Fin (d + 2)) :
    ∃ a : Assignment d, a.1 = role.symm 0 ∧ second a = role.symm sumSlot ∧
      ∀ i, weight a i = frameWeight d sumSlot (role i) := by
  have hne : role.symm sumSlot ≠ role.symm 0 := fun h => hsum (role.symm.injective h)
  obtain ⟨a, hfirst, hsecond⟩ := exists_assignment (role.symm 0) (role.symm sumSlot) hne
  refine ⟨a, hfirst, hsecond, ?_⟩
  intro i
  simp only [weight, hfirst, hsecond, role.eq_symm_apply, frameWeight]

theorem physical_relation {d : Nat} (M : Int) (sumSlot : Fin (d + 2))
    (hsum : sumSlot ≠ 0) (role : Fin (d + 2) ≃ Fin (d + 2))
    (q : Fin (d + 2) → Int)
    (hrel : Int.ModEq M (∑ i, frameWeight d sumSlot i * q i) 0) :
    ∃ a : Assignment d,
      (∀ i, weight a i = frameWeight d sumSlot (role i)) ∧
      Int.ModEq M (∑ i, weight a i * q (role i)) 0 := by
  obtain ⟨a, hfirst, hsecond, ha⟩ := physical_assignment sumSlot hsum role
  refine ⟨a, ha, ?_⟩
  have he : (∑ i, weight a i * q (role i)) = ∑ i, frameWeight d sumSlot i * q i := by
    apply Fintype.sum_equiv role
    intro i
    rw [ha i]
  rwa [he]

end CoefficientTwoPrecision.StationaryWeightTransport

#print axioms CoefficientTwoPrecision.StationaryWeightTransport.physical_assignment
#print axioms CoefficientTwoPrecision.StationaryWeightTransport.physical_relation
