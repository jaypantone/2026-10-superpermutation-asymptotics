import Challenge
import SuperpermutationUpperBound.Bounds.Definitions
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Statement bridges for the actual word bound

Both coverage predicates are imported unchanged from the supplied sources.
This file proves their equivalence and the natural/rational arithmetic bridge.
It does not assert the existence of a word satisfying the quantitative bound.
-/

namespace CoefficientTwoPrecision

theorem covers_iff_isSuperpermutation {n : ℕ} (w : List (Fin n)) :
    SuperpermutationBounds.Covers w ↔ SuperpermutationUpperBound.IsSuperpermutation w := by
  constructor
  · intro hw p hp
    obtain ⟨u, v, h⟩ := hw p hp.1 hp.2
    exact ⟨u, v, h.symm⟩
  · intro hw p hp hn
    obtain ⟨u, v, h⟩ := hw p ⟨hp, hn⟩
    exact ⟨u, v, h.symm⟩

@[simp] theorem cast_F3 (n : ℕ) :
    (SuperpermutationUpperBound.F3 n : ℚ) = SuperpermutationBounds.F3 n := by
  simp [SuperpermutationUpperBound.F3, SuperpermutationBounds.F3]

/-- The finite target in integer arithmetic is exactly the desired rational
length bound for the same word and the same factorial scale. -/
theorem integer_bound_iff (n r : ℕ) (hr : 0 < r) (w : List (Fin n)) :
    r * w.length ≤ r * SuperpermutationUpperBound.F3 n + (2 * r + 74) * (n - 4).factorial ↔
      (w.length : ℚ) ≤ SuperpermutationBounds.F3 n +
        (2 + 74 / (r : ℚ)) * ((n - 4).factorial : ℚ) := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hid : (r : ℚ) * (SuperpermutationBounds.F3 n +
      (2 + 74 / (r : ℚ)) * ((n - 4).factorial : ℚ)) =
      (r : ℚ) * SuperpermutationBounds.F3 n +
        (2 * (r : ℚ) + 74) * ((n - 4).factorial : ℚ) := by
    field_simp
  rw [← mul_le_mul_iff_right₀ hrQ, hid]
  rw [← cast_F3]
  exact_mod_cast (Iff.rfl :
    r * w.length ≤ r * SuperpermutationUpperBound.F3 n + (2 * r + 74) * (n - 4).factorial ↔
    r * w.length ≤ r * SuperpermutationUpperBound.F3 n + (2 * r + 74) * (n - 4).factorial)

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.covers_iff_isSuperpermutation
#print axioms CoefficientTwoPrecision.cast_F3
#print axioms CoefficientTwoPrecision.integer_bound_iff
