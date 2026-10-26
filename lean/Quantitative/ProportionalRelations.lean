import Quantitative.StationaryRelations

/-!
# Proportional stationary coefficient vectors are identical

The catalogue coefficients take the values -1, 1, and d-1. When d is at
least three, evaluating proportionality at the two distinguished d-1
positions rules out every unequal scaling, including negative scaling.
Thus vanishing guard coefficients in the same foreign stationary set
force the full assignments to coincide.
-/

namespace CoefficientTwoPrecision.ProportionalRelations

open StationaryRelations

theorem weight_values {d : Nat} (a : Assignment d) (i : Fin (d + 2)) :
    weight a i = -1 ∨ weight a i = 1 ∨ weight a i = (d : Int) - 1 := by
  unfold weight
  split_ifs <;> simp

theorem weight_bounds {d : Nat} (hd : 2 ≤ d) (a : Assignment d)
    (i : Fin (d + 2)) : -1 ≤ weight a i ∧ weight a i ≤ (d : Int) - 1 := by
  rcases weight_values a i with h | h | h <;> rw [h] <;> omega

theorem proportional_eq {d : Nat} (hd : 3 ≤ d) (a b : Assignment d)
    (shared : Fin (d + 2))
    (hcross : ∀ i, weight b shared * weight a i = weight a shared * weight b i) :
    a = b := by
  have hfirst := hcross a.1
  have hsecond := hcross b.1
  have hownA : weight a a.1 = (d : Int) - 1 := by simp [weight]
  have hownB : weight b b.1 = (d : Int) - 1 := by simp [weight]
  rw [hownA] at hfirst
  rw [hownB] at hsecond
  have hboundA := weight_bounds (by omega : 2 ≤ d) b a.1
  have hboundB := weight_bounds (by omega : 2 ≤ d) a b.1
  have hscale : weight a shared = weight b shared := by
    rcases weight_values a shared with ha | ha | ha <;>
      rcases weight_values b shared with hb | hb | hb <;>
      rw [ha, hb] at hfirst hsecond ⊢ <;> nlinarith
  apply weight_injective hd
  funext i
  have hi := hcross i
  rw [hscale] at hi
  exact mul_left_cancel₀ (weight_nonzero (by omega) b shared) hi

/-- The omitted shared-coordinate equation is automatically zero, so
checking only the guard coordinates suffices. -/
theorem eq_of_guard_cross_zero {d : Nat} (hd : 3 ≤ d) (a b : Assignment d)
    (shared : Fin (d + 2))
    (hguard : ∀ i, i ≠ shared →
      weight b shared * weight a i - weight a shared * weight b i = 0) : a = b := by
  apply proportional_eq hd a b shared
  intro i
  by_cases hi : i = shared
  · subst i
    exact mul_comm _ _
  · exact sub_eq_zero.mp (hguard i hi)

end CoefficientTwoPrecision.ProportionalRelations

#print axioms CoefficientTwoPrecision.ProportionalRelations.proportional_eq
#print axioms CoefficientTwoPrecision.ProportionalRelations.eq_of_guard_cross_zero
