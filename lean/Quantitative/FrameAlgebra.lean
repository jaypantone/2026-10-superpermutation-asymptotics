import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

/-!
# The formal points of a modular frame

The points are zero, the d coordinate vectors, and the all-ones vector.
Their only affine relations have coefficients proportional to
(d-1,-1,...,-1,1). When d is at least three, every nonzero relation
therefore uses at least five points. In particular, comparisons of two
ordered differences produce nonzero linear forms unless they are the
same ordered difference.
-/

namespace CoefficientTwoPrecision.FrameAlgebra

/-- `none` is zero, `some none` is the sum point, and `some (some j)`
is the j-th coordinate vector. -/
abbrev Point (d : Nat) := Option (Option (Fin d))

def coordinate {d : Nat} (p : Point d) (j : Fin d) : Int :=
  match p with
  | none => 0
  | some none => 1
  | some (some i) => if i = j then 1 else 0

theorem coordinate_sum {d : Nat} (c : Point d → Int) (j : Fin d) :
    (∑ p, c p * coordinate p j) = c (some (some j)) + c (some none) := by
  simp [coordinate, Fintype.sum_option, add_comm]

theorem affine_coefficients {d : Nat} (c : Point d → Int)
    (hsum : ∑ p, c p = 0)
    (hcoordinates : ∀ j, ∑ p, c p * coordinate p j = 0) :
    (∀ j, c (some (some j)) = -c (some none)) ∧
      c none = ((d : Int) - 1) * c (some none) := by
  have hc (j : Fin d) : c (some (some j)) = -c (some none) := by
    have hj := hcoordinates j
    rw [coordinate_sum] at hj
    omega
  refine ⟨hc, ?_⟩
  simp only [Fintype.sum_option] at hsum
  simp_rw [hc] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith only [hsum]

/-- A nonzero affine relation on these points has every coefficient
nonzero. This uses d>=2; d>=3 is needed for the five-point consequence. -/
theorem nonzero_relation_full_support {d : Nat} (hd : 2 ≤ d)
    (c : Point d → Int) (hsum : ∑ p, c p = 0)
    (hcoordinates : ∀ j, ∑ p, c p * coordinate p j = 0)
    (hsumPoint : c (some none) ≠ 0) : ∀ p, c p ≠ 0 := by
  obtain ⟨hc, hzero⟩ := affine_coefficients c hsum hcoordinates
  intro p
  cases p with
  | none =>
    rw [hzero]
    apply mul_ne_zero _ hsumPoint
    have hdI : (2 : Int) ≤ d := by exact_mod_cast hd
    omega
  | some p =>
    cases p with
    | none => exact hsumPoint
    | some j => rw [hc]; exact neg_ne_zero.mpr hsumPoint

/-- No nonzero affine relation can involve four or fewer formal points. -/
theorem small_affine_relation_zero {d : Nat} (hd : 3 ≤ d)
    (c : Point d → Int) (hsum : ∑ p, c p = 0)
    (hcoordinates : ∀ j, ∑ p, c p * coordinate p j = 0)
    (hsupport : (Finset.univ.filter (fun p => c p ≠ 0)).card ≤ 4) :
    ∀ p, c p = 0 := by
  have hsumPoint : c (some none) = 0 := by
    by_contra hne
    have hall := nonzero_relation_full_support (by omega : 2 ≤ d) c hsum hcoordinates hne
    have hfull : Finset.univ.filter (fun p => c p ≠ 0) = Finset.univ := by
      ext p
      simp [hall p]
    rw [hfull] at hsupport
    have hcard : (Finset.univ : Finset (Point d)).card = d + 2 := by
      simp [Point, Nat.add_assoc]
    rw [hcard] at hsupport
    omega
  obtain ⟨hc, hzero⟩ := affine_coefficients c hsum hcoordinates
  intro p
  cases p with
  | none => simp [hzero, hsumPoint]
  | some p =>
    cases p with
    | none => exact hsumPoint
    | some j => simp [hc, hsumPoint]

/-- Coefficients obtained by subtracting two ordered differences. -/
def differenceCoefficients {d : Nat} (a b c e p : Point d) : Int :=
  (if p = a then 1 else 0) - (if p = b then 1 else 0) -
    (if p = c then 1 else 0) + (if p = e then 1 else 0)

theorem difference_coefficients_sum {d : Nat} (a b c e : Point d) :
    ∑ p, differenceCoefficients a b c e p = 0 := by
  simp [differenceCoefficients, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem difference_coefficients_coordinate {d : Nat} (a b c e : Point d) (j : Fin d) :
    (∑ p, differenceCoefficients a b c e p * coordinate p j) =
      coordinate a j - coordinate b j - coordinate c j + coordinate e j := by
  simp [differenceCoefficients, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul]

theorem difference_coefficients_support {d : Nat} (a b c e : Point d) :
    (Finset.univ.filter (fun p => differenceCoefficients a b c e p ≠ 0)).card ≤ 4 := by
  have hsub : Finset.univ.filter (fun p => differenceCoefficients a b c e p ≠ 0) ⊆
      {a, b, c, e} := by
    intro p hp
    by_contra hnot
    have hne : p ≠ a ∧ p ≠ b ∧ p ≠ c ∧ p ≠ e := by simpa using hnot
    exact (Finset.mem_filter.mp hp).2 (by simp [differenceCoefficients, hne.1,
      hne.2.1, hne.2.2.1, hne.2.2.2])
  have h1 := Finset.card_insert_le a ({b, c, e} : Finset (Point d))
  have h2 := Finset.card_insert_le b ({c, e} : Finset (Point d))
  have h3 := Finset.card_insert_le c ({e} : Finset (Point d))
  have h4 : ({e} : Finset (Point d)).card = 1 := Finset.card_singleton e
  exact (Finset.card_le_card hsub).trans (by omega)

/-- The distinct ordered differences of the formal frame points are
distinct vectors. Reduction modulo M is handled separately by root counts. -/
theorem ordered_difference_injective {d : Nat} (hd : 3 ≤ d)
    (a b c e : Point d) (hab : a ≠ b)
    (heq : ∀ j, coordinate a j - coordinate b j = coordinate c j - coordinate e j) :
    a = c ∧ b = e := by
  have hcoordinates (j : Fin d) :
      ∑ p, differenceCoefficients a b c e p * coordinate p j = 0 := by
    rw [difference_coefficients_coordinate]
    have hj := heq j
    omega
  have hzero := small_affine_relation_zero hd (differenceCoefficients a b c e)
    (difference_coefficients_sum a b c e) hcoordinates
    (difference_coefficients_support a b c e)
  have hac : a = c := by
    by_contra hne
    have h := hzero a
    unfold differenceCoefficients at h
    rw [if_pos rfl, if_neg hab, if_neg hne] at h
    split_ifs at h <;> omega
  subst c
  refine ⟨rfl, ?_⟩
  by_contra hbe
  have h := hzero b
  simp [differenceCoefficients, hbe] at h

end CoefficientTwoPrecision.FrameAlgebra

#print axioms CoefficientTwoPrecision.FrameAlgebra.affine_coefficients
#print axioms CoefficientTwoPrecision.FrameAlgebra.small_affine_relation_zero
#print axioms CoefficientTwoPrecision.FrameAlgebra.ordered_difference_injective
