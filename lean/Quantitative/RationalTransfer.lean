import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact rational invariants for the sparse transfer

These lemmas are independent of a source-family existence assertion. They
will be applied to the normalized counts of actual stages. No conclusion
about a covering word is claimed in this file.
-/

namespace CoefficientTwoPrecision

/-- One step of the pending-mass invariant. -/
theorem pending_step (p s f : ℚ) (hp : 0 ≤ p) (hs : 0 ≤ s) (hf : 0 ≤ f) :
    p * (1 - f) * (1 + (s + f)) ≤ p * (1 + s) := by
  have hsf : 0 ≤ p * f * (s + f) := mul_nonneg (mul_nonneg hp hf) (add_nonneg hs hf)
  nlinarith only [hsf]

/-- One step of the exact cost invariant; the local cost is charged only
against the mass removed in this step. -/
theorem cost_step (n K p X f g : ℚ) (hp : 0 ≤ p) (hcost : n * g ≤ K * f) :
    n * (X + p * g) + K * (p * (1 - f)) ≤ n * X + K * p := by
  have h := mul_le_mul_of_nonneg_left hcost hp
  nlinarith only [h]

/-- A recursive pending mass, starting from mass one. -/
def pending (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => pending f j * (1 - f j)

/-- A recursive sum of densities. -/
def densitySum (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | j + 1 => densitySum f j + f j

/-- Total normalized cost, using the pending mass before each step. -/
def accumulatedCost (f g : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | j + 1 => accumulatedCost f g j + pending f j * g j

theorem pending_nonneg (f : ℕ → ℚ) (j : ℕ)
    (hf : ∀ i < j, f i ≤ 1) : 0 ≤ pending f j := by
  induction j with
  | zero => simp [pending]
  | succ j ih =>
    exact mul_nonneg (ih (fun i hi => hf i (by omega))) (sub_nonneg.mpr (hf j (by omega)))

theorem densitySum_nonneg (f : ℕ → ℚ) (j : ℕ)
    (hf : ∀ i < j, 0 ≤ f i) : 0 ≤ densitySum f j := by
  induction j with
  | zero => simp [densitySum]
  | succ j ih =>
    exact add_nonneg (ih (fun i hi => hf i (by omega))) (hf j (by omega))

/-- The product estimate is proved by an invariant, without logarithms. -/
theorem pending_invariant (f : ℕ → ℚ) (j : ℕ)
    (hf : ∀ i < j, 0 ≤ f i ∧ f i ≤ 1) :
    pending f j * (1 + densitySum f j) ≤ 1 := by
  induction j with
  | zero => simp [pending, densitySum]
  | succ j ih =>
    have hprefix : ∀ i < j, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (by omega)
    calc
      pending f (j + 1) * (1 + densitySum f (j + 1))
          ≤ pending f j * (1 + densitySum f j) :=
        pending_step _ _ _ (pending_nonneg f j (fun i hi => (hprefix i hi).2))
          (densitySum_nonneg f j (fun i hi => (hprefix i hi).1)) (hf j (by omega)).1
      _ ≤ 1 := ih hprefix

/-- All sparse costs telescope, with the unspent mass retained explicitly. -/
theorem cost_invariant (f g : ℕ → ℚ) (j : ℕ) (n K : ℚ)
    (hf : ∀ i < j, f i ≤ 1)
    (hcost : ∀ i < j, n * g i ≤ K * f i) :
    n * accumulatedCost f g j + K * pending f j ≤ K := by
  induction j with
  | zero => simp [pending, accumulatedCost]
  | succ j ih =>
    have hprefix : ∀ i < j, f i ≤ 1 := fun i hi => hf i (by omega)
    calc
      n * accumulatedCost f g (j + 1) + K * pending f (j + 1)
          ≤ n * accumulatedCost f g j + K * pending f j :=
        cost_step _ _ _ _ _ _ (pending_nonneg f j hprefix) (hcost j (by omega))
      _ ≤ K := ih hprefix (fun i hi => hcost i (by omega))

/-- A lower bound on the summed sparse densities gives the required mass bound. -/
theorem pending_le_four_div (f : ℕ → ℚ) (j : ℕ) (r : ℚ) (hr : 0 < r)
    (hf : ∀ i < j, 0 ≤ f i ∧ f i ≤ 1)
    (hsum : r / 4 ≤ densitySum f j) : pending f j ≤ 4 / r := by
  have hp := pending_nonneg f j (fun i hi => (hf i hi).2)
  have hi := pending_invariant f j hf
  have h := mul_le_mul_of_nonneg_left hsum hp
  apply (le_div_iff₀ hr).2
  nlinarith only [h, hi, hp]

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.pending_invariant
#print axioms CoefficientTwoPrecision.cost_invariant
#print axioms CoefficientTwoPrecision.pending_le_four_div
