import Quantitative.LinearCount

/-!
# Counting a relation on an explicitly embedded set of variables

Foreign stationary controls form an injectively indexed subset of the
guard variables. Extending their coefficient vector by zero gives an
ordinary linear congruence in all guard variables. A selected nonzero
coefficient remains nonzero under this extension.
-/

namespace CoefficientTwoPrecision.EmbeddedLinearCount

def extendedCoefficient {k G : Nat} (index : Fin k → Fin G)
    (c : Fin k → Int) (j : Fin G) : Int :=
  ∑ i, if index i = j then c i else 0

theorem coefficient_at {k G : Nat} (index : Fin k → Fin G)
    (hinj : Function.Injective index) (c : Fin k → Int) (i : Fin k) :
    extendedCoefficient index c (index i) = c i := by
  simp only [extendedCoefficient, hinj.eq_iff]
  simp

theorem extended_value {k G : Nat} (index : Fin k → Fin G)
    (c : Fin k → Int) (x : Fin G → Int) :
    (∑ j, extendedCoefficient index c j * x j) = ∑ i, c i * x (index i) := by
  unfold extendedCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

theorem root_count {k G : Nat} (m : Nat) (hm : 0 < m)
    (index : Fin k → Fin G) (hinj : Function.Injective index)
    (c : Fin k → Int) (b : Int) (i : Fin k) (hc : c i ≠ 0) :
    (Finset.univ.filter (fun x : Fin G → Fin m =>
      Int.ModEq (m : Int) (∑ j, c j * (x (index j)).val) b)).card ≤
      m ^ (G - 1) * (c i).natAbs := by
  have hcoef := coefficient_at index hinj c i
  have hcount := LinearCount.linear_root_count m G hm (extendedCoefficient index c) b
    (index i) (by rwa [hcoef])
  simpa only [extended_value, hcoef] using hcount

end CoefficientTwoPrecision.EmbeddedLinearCount

#print axioms CoefficientTwoPrecision.EmbeddedLinearCount.root_count
