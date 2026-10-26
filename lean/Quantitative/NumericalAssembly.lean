import Quantitative.CircleMass

/-!
# The complete numerical implication for the chosen schedule

`SparseNumericalData` contains integer counts and their estimates, not a
geometric source family. `DenseNumericalTrace` contains normalized updates,
not actual stages. The theorem in this file is conditional on those data.
It supplies all numerical estimates required by actual word completion,
but makes no word-existence assertion.
-/

namespace CoefficientTwoPrecision

def scheduledDenominator (n r i : ℕ) : ℕ :=
  SourceUniverse.risingCount (sparseStart n r (sourceWidth r) i) (sourceWidth r)

structure SparseNumericalData (n r : ℕ) where
  rows : ℕ → ℕ
  charge : ℕ → ℕ
  circles : ℕ → ℕ
  theta : ℕ → ℚ
  epsilon : ℕ → ℚ
  rows_le : ∀ i < sparseBlocks n r (sourceWidth r), rows i ≤ scheduledDenominator n r i
  density_eq : ∀ i < sparseBlocks n r (sourceWidth r),
    (rows i : ℚ) / (scheduledDenominator n r i : ℚ) =
      (sourceRho r * (sourceWidth r : ℚ) /
        (sparseStart n r (sourceWidth r) i : ℚ)) * (1 + theta i)
  cost_eq : ∀ i < sparseBlocks n r (sourceWidth r),
    ((charge i : ℚ) + (circles i : ℚ)) / (scheduledDenominator n r i : ℚ) =
      ((2 * ((r : ℚ) - 1) / ((r : ℚ) - 2)) *
        (sourceRho r * (sourceWidth r : ℚ)) /
        (sparseStart n r (sourceWidth r) i : ℚ) ^ 2) * (1 + epsilon i)
  errors : ∀ i < sparseBlocks n r (sourceWidth r),
    |theta i| ≤ (errorNumerator r (sourceWidth r) : ℚ) /
        (sparseStart n r (sourceWidth r) i : ℚ) ∧
    |epsilon i| ≤ (errorNumerator r (sourceWidth r) : ℚ) /
        (sparseStart n r (sourceWidth r) i : ℚ)
  circle_ratio : ∀ i < sparseBlocks n r (sourceWidth r),
    (circles i : ℚ) ≤ ((r : ℚ) - 1) * (charge i : ℚ) /
      (sparseStart n r (sourceWidth r) i : ℚ)

def SparseNumericalData.density {n r : ℕ} (S : SparseNumericalData n r) (i : ℕ) : ℚ :=
  (S.rows i : ℚ) / (scheduledDenominator n r i : ℚ)

def SparseNumericalData.chargeRate {n r : ℕ} (S : SparseNumericalData n r) (i : ℕ) : ℚ :=
  (S.charge i : ℚ) / (scheduledDenominator n r i : ℚ)

def SparseNumericalData.circleRate {n r : ℕ} (S : SparseNumericalData n r) (i : ℕ) : ℚ :=
  (S.circles i : ℚ) / (scheduledDenominator n r i : ℚ)

def SparseNumericalData.totalRate {n r : ℕ} (S : SparseNumericalData n r) (i : ℕ) : ℚ :=
  ((S.charge i : ℚ) + (S.circles i : ℚ)) / (scheduledDenominator n r i : ℚ)

structure DenseNumericalTrace (n : ℕ) (initialPending : ℚ) where
  p : ℕ → ℚ
  X : ℕ → ℚ
  z : ℕ → ℚ
  p_zero : p 0 = initialPending
  X_zero : X 0 = 0
  z_zero : z 0 = 0
  p_nonneg : ∀ i ≤ denseBlocks n, 0 ≤ p i
  contraction : ∀ i < denseBlocks n, p (i + 1) ≤ (3 / 4) * p i
  cost_step : ∀ i < denseBlocks n,
    X (i + 1) - X i ≤ (8 / ((tailStart n : ℚ) + 3 * i)) * (p i - p (i + 1))
  circle_step : ∀ i < denseBlocks n,
    z (i + 1) - z i ≤ 8 * p i /
      (((tailStart n : ℚ) + 3 * i) * ((tailStart n : ℚ) + 3 * i + 1))

theorem pending_le_one (f : ℕ → ℚ) (J : ℕ)
    (hf : ∀ i < J, 0 ≤ f i ∧ f i ≤ 1) : pending f J ≤ 1 := by
  have h := pending_invariant f J hf
  have hp := pending_nonneg f J (fun i hi => (hf i hi).2)
  have hs := densitySum_nonneg f J (fun i hi => (hf i hi).1)
  have hcross := mul_nonneg hp hs
  nlinarith only [h, hcross]

theorem dense_cost_telescope (X p : ℕ → ℚ) (K : ℕ) (b : ℚ)
    (hstep : ∀ i < K, X (i + 1) - X i ≤ b * (p i - p (i + 1))) :
    X K - X 0 ≤ b * (p 0 - p K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hprev := ih (fun i hi => hstep i (by omega))
    have hlast := hstep K (by omega)
    nlinarith only [hprev, hlast]

theorem dense_trace_cost (n : ℕ) (a : ℚ) (T : DenseNumericalTrace n a)
    (htail : 0 < (tailStart n : ℚ)) :
    T.X (denseBlocks n) ≤ 8 * a / (tailStart n : ℚ) := by
  have huniform : ∀ i < denseBlocks n, T.X (i + 1) - T.X i ≤
      (8 / (tailStart n : ℚ)) * (T.p i - T.p (i + 1)) := by
    intro i hi
    have hp := T.p_nonneg i (Nat.le_of_lt hi)
    have hcon := T.contraction i hi
    have hdiff : 0 ≤ T.p i - T.p (i + 1) := by linarith only [hp, hcon]
    have hsize : (tailStart n : ℚ) ≤ (tailStart n : ℚ) + 3 * i := by
      have hi0 : (0 : ℚ) ≤ i := Nat.cast_nonneg i
      linarith only [hi0]
    exact (T.cost_step i hi).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℚ) ≤ 8) htail hsize) hdiff)
  have h := dense_cost_telescope T.X T.p (denseBlocks n) (8 / (tailStart n : ℚ)) huniform
  rw [T.X_zero, T.p_zero] at h
  have hpEnd := T.p_nonneg (denseBlocks n) le_rfl
  have hnonneg : 0 ≤ (8 / (tailStart n : ℚ)) * T.p (denseBlocks n) := by positivity
  have heq : (8 / (tailStart n : ℚ)) * a = 8 * a / (tailStart n : ℚ) := by ring
  nlinarith only [h, hnonneg, heq]

theorem dense_trace_circles (n : ℕ) (a : ℚ) (T : DenseNumericalTrace n a)
    (htail : 0 < (tailStart n : ℚ)) (ha : a ≤ 1) :
    T.z (denseBlocks n) ≤ 32 / ((tailStart n : ℚ) * ((tailStart n : ℚ) + 1)) := by
  have huniform : ∀ i < denseBlocks n, T.z (i + 1) - T.z i ≤
      (8 / ((tailStart n : ℚ) * ((tailStart n : ℚ) + 1))) * T.p i := by
    intro i hi
    exact (T.circle_step i hi).trans
      (dense_circle_increment_uniform (tailStart n : ℚ) ((tailStart n : ℚ) + 3 * i)
        (T.p i) htail
        (by have hi0 : (0 : ℚ) ≤ i := Nat.cast_nonneg i; linarith only [hi0])
        (T.p_nonneg i (Nat.le_of_lt hi)))
  have h := dense_circle_bound T.z T.p (denseBlocks n) (tailStart n : ℚ) htail
    (by rw [T.p_zero]; exact ha) (T.p_nonneg _ le_rfl) T.contraction huniform
  simpa only [T.z_zero, sub_zero] using h

/-- The complete scheduled numerical bound. Its hypotheses include integer
source counts and a terminal trace, but no actual source-family constructor.
Instantiation by the geometric construction is a separate obligation. -/
theorem scheduled_numerical_bound (n r : ℕ) (hr : 6 ≤ r)
    (hn : transferConstant * r ^ 61 ≤ n) (S : SparseNumericalData n r)
    (T : DenseNumericalTrace n (pending S.density (sparseBlocks n r (sourceWidth r)))) :
    (n : ℚ) * accumulatedCost S.density S.totalRate (sparseBlocks n r (sourceWidth r)) +
      (n : ℚ) * T.X (denseBlocks n) +
      ((n : ℚ) * (accumulatedCost S.density S.circleRate (sparseBlocks n r (sourceWidth r)) +
        T.z (denseBlocks n)) + 2 * (n : ℚ) * T.p (denseBlocks n)) ≤ 2 + 74 / (r : ℚ) := by
  obtain ⟨hn0, hW0, hJpos, _, htail49, hstarts⟩ := source_schedule_valid n r hr hn
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn0
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℚ) < r := by linarith only [hrQ]
  have hr1 : (1 : ℚ) ≤ r := by linarith only [hrQ]
  have htail0 : (0 : ℚ) < tailStart n := by exact_mod_cast (show 0 < tailStart n by omega)
  have hstart0 := hstarts 0 hJpos
  have hm0half : (n : ℚ) ≤ 2 * (scheduleStart n r : ℚ) := by
    have h : n ≤ 2 * scheduleStart n r := by simpa [sparseStart] using hstart0.2.2.1
    exact_mod_cast h
  have hm0 : (0 : ℚ) < scheduleStart n r := by linarith only [hm0half, hnQ]
  have hm0n : (scheduleStart n r : ℚ) ≤ n := by
    have h : scheduleStart n r ≤ n := by simpa [sparseStart] using hstart0.2.2.2
    exact_mod_cast h
  have hroom : 2 * r * (r + sourceWidth r + tailLength n) ≤ n :=
    (construction_threshold_conditions r n hr hn).2.2
  have hend := (schedule_bounds n r (sourceWidth r) hr hn0 hW0 (sourceWidth_dvd r) hroom).2.2.1
  have hm0End : scheduleStart n r ≤ sparseEnd n r (sourceWidth r) := by unfold sparseEnd; omega
  have htailhalf : (n : ℚ) ≤ 2 * (tailStart n : ℚ) := by
    have h : (scheduleStart n r : ℚ) ≤ tailStart n := by exact_mod_cast hm0End.trans hend
    linarith only [hm0half, h]
  have hD : ∀ i < sparseBlocks n r (sourceWidth r), (0 : ℚ) < scheduledDenominator n r i := by
    intro i hi
    have hhalf := (hstarts i hi).2.2.1
    have hm : 0 < sparseStart n r (sourceWidth r) i := by omega
    exact_mod_cast risingCount_pos _ _ hm
  have hf : ∀ i < sparseBlocks n r (sourceWidth r), 0 ≤ S.density i ∧ S.density i ≤ 1 := by
    intro i hi
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (hD i hi))
    · apply (div_le_iff₀ (hD i hi)).2
      simpa only [one_mul] using (show (S.rows i : ℚ) ≤ scheduledDenominator n r i by
        exact_mod_cast S.rows_le i hi)
  obtain ⟨hcost, hsum, _⟩ := scheduled_sparse_estimates n r hr hn S.density S.totalRate
    S.theta S.epsilon hf S.density_eq S.cost_eq S.errors
  have hRate : ∀ i, S.totalRate i = S.chargeRate i + S.circleRate i := by
    intro i
    exact add_div _ _ _
  have hq0 : ∀ i < sparseBlocks n r (sourceWidth r), 0 ≤ S.chargeRate i := by
    intro i hi
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (hD i hi))
  have hc0 : ∀ i < sparseBlocks n r (sourceWidth r), 0 ≤ S.circleRate i := by
    intro i hi
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (hD i hi))
  have hratio : ∀ i < sparseBlocks n r (sourceWidth r), S.circleRate i ≤
      (((r : ℚ) - 1) / (scheduleStart n r : ℚ)) * S.chargeRate i := by
    intro i hi
    apply normalized_circle_ratio (S.charge i : ℚ) (S.circles i : ℚ)
      (scheduledDenominator n r i : ℚ) (sparseStart n r (sourceWidth r) i : ℚ)
      (scheduleStart n r : ℚ) (r : ℚ) (Nat.cast_nonneg _) (hD i hi) hm0 _ hr1 (S.circle_ratio i hi)
    exact_mod_cast (show scheduleStart n r ≤ sparseStart n r (sourceWidth r) i by
      unfold sparseStart
      omega)
  have hcoeff : 2 + 9 / (r : ℚ) ≤ 8 := by
    have h : 9 / (r : ℚ) ≤ 6 := (div_le_iff₀ hr0).2 (by linarith only [hrQ])
    linarith only [h]
  have hcost8 : ∀ i < sparseBlocks n r (sourceWidth r),
      (scheduleStart n r : ℚ) * (S.chargeRate i + S.circleRate i) ≤ 8 * S.density i := by
    intro i hi
    rw [← hRate i]
    exact (mul_le_mul_of_nonneg_right hm0n (by rw [hRate i]; exact add_nonneg (hq0 i hi) (hc0 i hi))).trans
      ((hcost i hi).trans (mul_le_mul_of_nonneg_right hcoeff (hf i hi).1))
  have hsparse := sparse_circle_bound S.density S.chargeRate S.circleRate
    (sparseBlocks n r (sourceWidth r)) (scheduleStart n r : ℚ) (r : ℚ) hm0 hr1
    (fun i hi => (hf i hi).2) hc0 hratio hcost8
  have hp0 := pending_nonneg S.density (sparseBlocks n r (sourceWidth r)) (fun i hi => (hf i hi).2)
  have hp1 := pending_le_one S.density (sparseBlocks n r (sourceWidth r)) hf
  have htailCost := dense_trace_cost n _ T htail0
  have hdense := dense_cost_scaling (n : ℚ) (tailStart n : ℚ)
    (pending S.density (sparseBlocks n r (sourceWidth r))) (T.X (denseBlocks n))
    htail0 hp0 (le_of_lt hnQ) htailhalf htailCost
  have htailCircles := dense_trace_circles n _ T htail0 hp1
  have hz := circle_mass_uniform (n : ℚ) (scheduleStart n r : ℚ) (tailStart n : ℚ)
    (r : ℚ) (accumulatedCost S.density S.circleRate (sparseBlocks n r (sourceWidth r)))
    (T.z (denseBlocks n)) hnQ hm0 htail0 hr1 hm0half htailhalf hsparse htailCircles
  have hp := dense_pending_lt_inverse_cube n hn0 T.p
    (by rw [T.p_zero]; exact hp1) T.contraction
  have hnSize : 96 * (r : ℚ) ^ 2 ≤ n := by
    exact_mod_cast (construction_threshold_conditions r n hr hn).2.1
  have hj := completion_mass_error_bound (n : ℚ) (r : ℚ)
    (accumulatedCost S.density S.circleRate (sparseBlocks n r (sourceWidth r)) + T.z (denseBlocks n))
    (T.p (denseBlocks n)) hrQ hnSize hz (le_of_lt hp)
  exact finite_transfer_coefficient S.density S.totalRate (sparseBlocks n r (sourceWidth r))
    (n : ℚ) (r : ℚ) ((n : ℚ) * T.X (denseBlocks n))
    ((n : ℚ) * (accumulatedCost S.density S.circleRate (sparseBlocks n r (sourceWidth r)) +
      T.z (denseBlocks n)) + 2 * (n : ℚ) * T.p (denseBlocks n))
    hr0 hf hsum hcost hdense hj

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.dense_trace_cost
#print axioms CoefficientTwoPrecision.scheduled_numerical_bound
