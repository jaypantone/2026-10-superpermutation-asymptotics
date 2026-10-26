import Quantitative.FrameAlgebra
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.Prod

/-!
# The finite catalogue of stationary affine relations

A relation assigns the coefficient d-1 to one stationary label and the
coefficient 1 to a different stationary label. Every other coefficient is
-1. There are (d+2)(d+1) different assignments, rather than (d+2)! possible
orders of all labels. The final sum counts roots for a fixed shared label.
-/

namespace CoefficientTwoPrecision.StationaryRelations

abbrev Assignment (d : Nat) := Fin (d + 2) × Fin (d + 1)

def second {d : Nat} (a : Assignment d) : Fin (d + 2) := a.1.succAbove a.2

def weight {d : Nat} (a : Assignment d) (i : Fin (d + 2)) : Int :=
  if i = a.1 then (d : Int) - 1 else if i = second a then 1 else -1

theorem second_ne {d : Nat} (a : Assignment d) : second a ≠ a.1 :=
  Fin.succAbove_ne _ _

theorem weight_formula {d : Nat} (a : Assignment d) (i : Fin (d + 2)) :
    weight a i = (if i = a.1 then (d : Int) else 0) +
      (if i = second a then 2 else 0) - 1 := by
  by_cases hi : i = a.1
  · subst i
    simp [weight, (second_ne a).symm]
  · simp only [weight, if_neg hi]
    split_ifs <;> omega

theorem weight_sum {d : Nat} (a : Assignment d) : ∑ i, weight a i = 0 := by
  simp_rw [weight_formula]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem weight_nonzero {d : Nat} (hd : 2 ≤ d) (a : Assignment d)
    (i : Fin (d + 2)) : weight a i ≠ 0 := by
  unfold weight
  split_ifs <;> omega

theorem weight_abs_formula {d : Nat} (hd : 2 ≤ d) (a : Assignment d)
    (i : Fin (d + 2)) :
    (weight a i).natAbs = (if i = a.1 then d - 2 else 0) + 1 := by
  unfold weight
  split_ifs <;> omega

theorem weight_abs_sum {d : Nat} (hd : 2 ≤ d) (a : Assignment d) :
    ∑ i, (weight a i).natAbs = 2 * d := by
  simp_rw [weight_abs_formula hd]
  simp only [Finset.sum_add_distrib]
  have hfirst : (∑ i : Fin (d + 2), if i = a.1 then d - 2 else 0) = d - 2 := by simp
  rw [hfirst]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

theorem weight_injective {d : Nat} (hd : 3 ≤ d) :
    Function.Injective (@weight d) := by
  intro a b hab
  have hfirst : a.1 = b.1 := by
    by_contra hne
    have h := congrFun hab a.1
    simp only [weight, if_pos rfl, if_neg hne] at h
    split_ifs at h <;> omega
  have hsecond : second a = second b := by
    by_contra hne
    have h := congrFun hab (second a)
    have hnot : second a ≠ b.1 := by simpa only [← hfirst] using second_ne a
    simpa [weight, second_ne a, hnot, hne] using h
  apply Prod.ext hfirst
  apply Fin.succAbove_right_injective (p := a.1)
  simpa only [second, ← hfirst] using hsecond

theorem assignment_card (d : Nat) : Fintype.card (Assignment d) = (d + 2) * (d + 1) := by
  simp [Assignment]

def catalogue (d : Nat) : Finset (Fin (d + 2) → Int) :=
  Finset.univ.image weight

theorem catalogue_card {d : Nat} (hd : 3 ≤ d) :
    (catalogue d).card = (d + 2) * (d + 1) := by
  rw [catalogue, Finset.card_image_of_injective _ (weight_injective hd),
    Finset.card_univ, assignment_card]

/-- For a fixed shared label, summing the modular root multiplicity over
all coefficient assignments gives exactly 2*d*(d+1). -/
theorem fixed_label_abs_sum {d : Nat} (hd : 2 ≤ d) (i : Fin (d + 2)) :
    ∑ a : Assignment d, (weight a i).natAbs = 2 * d * (d + 1) := by
  simp_rw [weight_abs_formula hd]
  rw [Fintype.sum_prod_type]
  change (∑ a : Fin (d + 2), ∑ _b : Fin (d + 1),
    ((if i = a then d - 2 else 0) + 1)) = 2 * d * (d + 1)
  have hinner (a : Fin (d + 2)) :
      (∑ _b : Fin (d + 1), ((if i = a then d - 2 else 0) + 1)) =
        (d + 1) * ((if i = a then d - 2 else 0) + 1) := by simp
  simp_rw [hinner]
  simp_rw [Nat.mul_add, Finset.sum_add_distrib]
  have hfirst : (∑ a : Fin (d + 2), (d + 1) * (if i = a then d - 2 else 0)) =
      (d + 1) * (d - 2) := by
    rw [← Finset.mul_sum]
    simp
  rw [hfirst]
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsub : d - 2 + 2 = d := by omega
  nlinarith

end CoefficientTwoPrecision.StationaryRelations

#print axioms CoefficientTwoPrecision.StationaryRelations.catalogue_card
#print axioms CoefficientTwoPrecision.StationaryRelations.fixed_label_abs_sum
