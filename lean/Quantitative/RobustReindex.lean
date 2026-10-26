import Quantitative.RobustMatching

/-! Robust separation is unchanged by a bijection of stationary indices. -/

namespace CoefficientTwoPrecision.RobustReindex

open RobustMatching

def indexMap {A B : Type} (order : A ≃ B) : DifferenceIndex A → DifferenceIndex B
  | none => none
  | some p => some ⟨(order p.val.1, order p.val.2), fun h => p.property (order.injective h)⟩

theorem indexMap_injective {A B : Type} (order : A ≃ B) :
    Function.Injective (indexMap order) := by
  intro first second h
  cases first with
  | none => cases second <;> simpa [indexMap] using h
  | some p =>
    cases second with
    | none => simp [indexMap] at h
    | some q =>
      have hpq : order p.val.1 = order q.val.1 ∧ order p.val.2 = order q.val.2 := by
        simpa only [indexMap, Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq] using h
      congr 1
      apply Subtype.ext
      exact Prod.ext (order.injective hpq.1) (order.injective hpq.2)

theorem difference_map {M : Nat} {A B : Type} (order : A ≃ B)
    (q : B → ZMod M) (index : DifferenceIndex A) :
    difference q (indexMap order index) = difference (q ∘ order) index := by
  cases index <;> rfl

theorem robust_reindex {M : Nat} {A B : Type} [DecidableEq A] [DecidableEq B]
    (order : A ≃ B) (q : B → ZMod M) (h : Robust q) : Robust (q ∘ order) := by
  intro first second error hlo hhi heq
  apply indexMap_injective order
  apply h (indexMap order first) (indexMap order second) error hlo hhi
  simpa only [difference_map] using heq

end CoefficientTwoPrecision.RobustReindex

#print axioms CoefficientTwoPrecision.RobustReindex.robust_reindex
