import Quantitative.PrimaryCatalogue
import Quantitative.ForeignGuardSets
import Quantitative.ProportionalRelations
import Quantitative.LinearCount

/-!
# The rank alternatives for actual primary events

Each event has a coefficient on every actual guard variable, extended by
zero outside its foreign stationary set. Eliminating time from two events
gives the cross coefficient below. A private guard makes this coefficient
nonzero. If every guard coefficient vanishes, the foreign block, foreign
mobile, and stationary coefficient assignment must all agree.
-/

namespace CoefficientTwoPrecision.PrimaryRank

open GuardCatalogue NeighbourGeometry StationaryRelations PrimaryCatalogue ForeignGuardSets

variable {d A : Nat}

noncomputable def guardCoefficient (hA : 0 < A) (active : Active d A)
    (event : Event d A hA active) (u : Fin (guardNumber d A)) : Int :=
  ∑ i : {i : Fin (d + 2) // i ≠ sharedIndex hA active event.1 event.2.1},
    if guardIndex hA active event.1 event.2.1 i = u then weight event.2.2.1 i.val else 0

theorem coefficient_at (hA : 0 < A) (active : Active d A) (event : Event d A hA active)
    (i : {i : Fin (d + 2) // i ≠ sharedIndex hA active event.1 event.2.1}) :
    guardCoefficient hA active event (guardIndex hA active event.1 event.2.1 i) =
      weight event.2.2.1 i.val := by
  classical
  simp only [guardCoefficient, (guardIndex_injective hA active event.1 event.2.1).eq_iff]
  simp

theorem coefficient_outside (hA : 0 < A) (active : Active d A) (event : Event d A hA active)
    (u : Fin (guardNumber d A)) (hu : u ∉ guardSet hA active event.1 event.2.1) :
    guardCoefficient hA active event u = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  have hi : guardIndex hA active event.1 event.2.1 i ≠ u := by
    intro he
    exact hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
  simp only [if_neg hi]

theorem coefficient_nonzero_on (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A)
    (event : Event d A hA active) (u : Fin (guardNumber d A))
    (hu : u ∈ guardSet hA active event.1 event.2.1) : guardCoefficient hA active event u ≠ 0 := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  rw [coefficient_at]
  exact weight_nonzero hd _ _

theorem coefficient_abs (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A)
    (event : Event d A hA active) (u : Fin (guardNumber d A)) :
    (guardCoefficient hA active event u).natAbs ≤ d - 1 := by
  classical
  by_cases hu : u ∈ guardSet hA active event.1 event.2.1
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    rw [coefficient_at, weight_abs_formula hd]
    split_ifs <;> omega
  · rw [coefficient_outside hA active event u hu]
    simp

theorem guardSum_eq {m : Nat} (hA : 0 < A) (active : Active d A)
    (event : Event d A hA active) (x : Fin (guardNumber d A) → Fin m) :
    guardSum hA active event x =
      ∑ u, guardCoefficient hA active event u * (x u).val := by
  classical
  unfold guardCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

noncomputable def guardCross (hA : 0 < A) (active : Active d A)
    (first second : Event d A hA active) (u : Fin (guardNumber d A)) : Int :=
  coefficient hA active second * guardCoefficient hA active first u -
    coefficient hA active first * guardCoefficient hA active second u

theorem guardCross_abs (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A)
    (first second : Event d A hA active) (u : Fin (guardNumber d A)) :
    (guardCross hA active first second u).natAbs ≤ 2 * (d - 1) ^ 2 := by
  have hfirst : (coefficient hA active first).natAbs ≤ d - 1 := by
    unfold coefficient
    rw [weight_abs_formula hd]
    split_ifs <;> omega
  have hsecond : (coefficient hA active second).natAbs ≤ d - 1 := by
    unfold coefficient
    rw [weight_abs_formula hd]
    split_ifs <;> omega
  have hleft := Nat.mul_le_mul hsecond (coefficient_abs hd hA active first u)
  have hright := Nat.mul_le_mul hfirst (coefficient_abs hd hA active second u)
  have habs := Int.natAbs_sub_le
    (coefficient hA active second * guardCoefficient hA active first u)
    (coefficient hA active first * guardCoefficient hA active second u)
  simp only [Int.natAbs_mul] at habs
  unfold guardCross
  nlinarith

theorem private_guard_nonzero (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A)
    (first second : Event d A hA active) (u : Fin (guardNumber d A))
    (hfirst : u ∈ guardSet hA active first.1 first.2.1)
    (hsecond : u ∉ guardSet hA active second.1 second.2.1) :
    guardCross hA active first second u ≠ 0 := by
  rw [guardCross, coefficient_outside hA active second u hsecond, mul_zero, sub_zero]
  exact mul_ne_zero (PrimaryCatalogue.coefficient_nonzero hd hA active second)
    (coefficient_nonzero_on hd hA active first u hfirst)

/-- These are identities of the actual event data, not an assumed rank
condition on abstract coefficient arrays. -/
theorem pattern_eq_of_guardCross_zero (hd : 3 ≤ d) (hA : 0 < A) (active : Active d A)
    (first second : Event d A hA active)
    (hzero : ∀ u, guardCross hA active first second u = 0) :
    first.1 = second.1 ∧ first.2.1.val = second.2.1.val ∧ first.2.2.1 = second.2.2.1 := by
  classical
  have hforeign : first.1 = second.1 := by
    by_contra hne
    have hval : first.1.val ≠ second.1.val := fun he => hne (Subtype.ext he)
    obtain ⟨u, hu, hnu⟩ := private_guard_different_blocks (by omega) hA active
      first.1 second.1 hval first.2.1 second.2.1
    exact private_guard_nonzero (by omega) hA active first second u hu hnu (hzero u)
  rcases first with ⟨foreignFirst, mobileFirst, assignmentFirst, slotFirst, rhsFirst⟩
  rcases second with ⟨foreignSecond, mobileSecond, assignmentSecond, slotSecond, rhsSecond⟩
  dsimp only at hforeign
  subst foreignSecond
  have hmobile : mobileFirst = mobileSecond := by
    by_contra hne
    obtain ⟨u, hu, hnu⟩ := private_guard_different_mobiles hA active foreignFirst
      mobileFirst mobileSecond hne
    exact private_guard_nonzero (by omega) hA active
      ⟨foreignFirst, mobileFirst, assignmentFirst, slotFirst, rhsFirst⟩
      ⟨foreignFirst, mobileSecond, assignmentSecond, slotSecond, rhsSecond⟩ u hu hnu (hzero u)
  subst mobileSecond
  have hassignment : assignmentFirst = assignmentSecond := by
    apply ProportionalRelations.eq_of_guard_cross_zero hd assignmentFirst assignmentSecond
      (sharedIndex hA active foreignFirst mobileFirst)
    intro i hi
    have hz := hzero (guardIndex hA active foreignFirst mobileFirst ⟨i, hi⟩)
    have hfirst := coefficient_at hA active
      (⟨foreignFirst, mobileFirst, assignmentFirst, slotFirst, rhsFirst⟩ : Event d A hA active)
      ⟨i, hi⟩
    have hsecond := coefficient_at hA active
      (⟨foreignFirst, mobileFirst, assignmentSecond, slotSecond, rhsSecond⟩ : Event d A hA active)
      ⟨i, hi⟩
    rw [guardCross, hfirst, hsecond] at hz
    simpa only [coefficient] using hz
  exact ⟨rfl, rfl, hassignment⟩

/-- Once a guard coefficient survives, all other guard variables may be
fixed arbitrarily; no distribution property of the selected frames is used. -/
theorem guard_root_count (m : Nat) (hm : 0 < m) (hd : 2 ≤ d)
    (hA : 0 < A) (active : Active d A) (first second : Event d A hA active)
    (b : Int) (u : Fin (guardNumber d A)) (hu : guardCross hA active first second u ≠ 0) :
    (Finset.univ.filter (fun x : Fin (guardNumber d A) → Fin m =>
      Int.ModEq (m : Int) (∑ v, guardCross hA active first second v * (x v).val) b)).card ≤
      m ^ (guardNumber d A - 1) * (2 * (d - 1) ^ 2) := by
  exact (LinearCount.linear_root_count m (guardNumber d A) hm
    (guardCross hA active first second) b u hu).trans
      (Nat.mul_le_mul_left _ (guardCross_abs hd hA active first second u))

end CoefficientTwoPrecision.PrimaryRank

#print axioms CoefficientTwoPrecision.PrimaryRank.pattern_eq_of_guardCross_zero
#print axioms CoefficientTwoPrecision.PrimaryRank.guard_root_count
