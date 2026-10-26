import Quantitative.StageState
import Quantitative.NumericalAssembly

/-!
# The actual dense tail and its extracted numerical trace

Starting with any actual Stage of size at least 49, we repeatedly apply the
original dense family. `trace` is then defined from the counts of those
constructed Stages. No existence or recurrence hypothesis for a numerical
trace is used.
-/

namespace CoefficientTwoPrecision.DenseStageIteration

open StageState

noncomputable def stages {b : ℕ} (S : BuiltStage b) (hb : 49 ≤ b) :
    (i : ℕ) → BuiltStage (b + 3 * i)
  | 0 => S.reindex (by omega)
  | i + 1 =>
    (Classical.choose (dense (stages S hb i) (by omega))).reindex (by omega)

@[simp] theorem zero_p {b : ℕ} (S : BuiltStage b) (hb : 49 ≤ b) :
    (stages S hb 0).p = S.p := by simp only [stages, BuiltStage.reindex_p]
@[simp] theorem zero_X {b : ℕ} (S : BuiltStage b) (hb : 49 ≤ b) :
    (stages S hb 0).X = S.X := by simp only [stages, BuiltStage.reindex_X]
@[simp] theorem zero_zmass {b : ℕ} (S : BuiltStage b) (hb : 49 ≤ b) :
    (stages S hb 0).zmass = S.zmass := by simp only [stages, BuiltStage.reindex_zmass]

theorem step_values {b : ℕ} (S : BuiltStage b) (hb : 49 ≤ b) (i : ℕ) :
    (stages S hb (i + 1)).p ≤ (3 / 4) * (stages S hb i).p ∧
    (stages S hb (i + 1)).X - (stages S hb i).X ≤
      (8 / ((b : ℚ) + 3 * i)) * ((stages S hb i).p - (stages S hb (i + 1)).p) ∧
    (stages S hb (i + 1)).zmass - (stages S hb i).zmass ≤
      8 * (stages S hb i).p / (((b : ℚ) + 3 * i) * ((b : ℚ) + 3 * i + 1)) := by
  have h := Classical.choose_spec (dense (stages S hb i) (by omega))
  simpa only [stages, BuiltStage.reindex_p, BuiltStage.reindex_X,
    BuiltStage.reindex_zmass, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

/-- The trace is read from actual Stage counts, subtracting the inherited
cost and circle mass at the start of the dense tail. -/
noncomputable def trace (n : ℕ) (S : BuiltStage (tailStart n)) (hb : 49 ≤ tailStart n)
    (p0 : ℚ) (hp : S.p = p0) : DenseNumericalTrace n p0 where
  p i := (stages S hb i).p
  X i := (stages S hb i).X - S.X
  z i := (stages S hb i).zmass - S.zmass
  p_zero := (zero_p S hb).trans hp
  X_zero := by rw [zero_X]; exact sub_self _
  z_zero := by rw [zero_zmass]; exact sub_self _
  p_nonneg i _ := (stages S hb i).p_nonneg
  contraction i _ := (step_values S hb i).1
  cost_step i _ := by
    have h := (step_values S hb i).2.1
    linarith only [h]
  circle_step i _ := by
    have h := (step_values S hb i).2.2
    linarith only [h]

end CoefficientTwoPrecision.DenseStageIteration

#print axioms CoefficientTwoPrecision.DenseStageIteration.step_values
#print axioms CoefficientTwoPrecision.DenseStageIteration.trace
