import Quantitative.ScheduleArithmetic

/-!
# The schedule instantiated with the constructed numerical parameters

These results discharge the size and summation assumptions needed by the
sparse transfer. The input sequences still have to be obtained from actual
source families and actual Stage updates.
-/

namespace CoefficientTwoPrecision

theorem sparse_count_rational (n r W J : ℕ) (hr : 0 < r) (hW : 0 < W)
    (hcount : n ≤ 2 * r * J * W) :
    (n : ℚ) / (2 * (r : ℚ) * (W : ℚ)) ≤ (J : ℚ) := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hWQ : (0 : ℚ) < W := by exact_mod_cast hW
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 * (r : ℚ) * (W : ℚ))).2
  have hcast : (n : ℚ) ≤ 2 * (r : ℚ) * (J : ℚ) * (W : ℚ) := by exact_mod_cast hcount
  calc
    (n : ℚ) ≤ 2 * (r : ℚ) * (J : ℚ) * (W : ℚ) := hcast
    _ = (J : ℚ) * (2 * (r : ℚ) * (W : ℚ)) := by ring

theorem source_schedule_valid (n r : ℕ) (hr : 6 ≤ r)
    (hn : transferConstant * r ^ 61 ≤ n) :
    0 < n ∧ 0 < sourceWidth r ∧
      0 < sparseBlocks n r (sourceWidth r) ∧
      (n : ℚ) / (2 * (r : ℚ) * (sourceWidth r : ℚ)) ≤
        (sparseBlocks n r (sourceWidth r) : ℚ) ∧
      49 ≤ tailStart n ∧
      (∀ i < sparseBlocks n r (sourceWidth r),
        r ∣ sparseStart n r (sourceWidth r) i ∧
        4 * errorNumerator r (sourceWidth r) ≤ sparseStart n r (sourceWidth r) i ∧
        n ≤ 2 * sparseStart n r (sourceWidth r) i ∧
        sparseStart n r (sourceWidth r) i ≤ n) := by
  obtain ⟨hprimitive, hsize, hroom⟩ := construction_threshold_conditions r n hr hn
  have hr0 : 0 < r := by omega
  have hrpow : 1 ≤ r ^ 2 := Nat.one_le_pow 2 r hr0
  have hn0 : 0 < n := by nlinarith only [hsize, hrpow]
  have hW0 : 0 < sourceWidth r := lt_of_lt_of_le (by omega : 0 < r ^ 2)
    (sourceWidth_lower r hr)
  have hroom' : 2 * r * (r + sourceWidth r + tailLength n) ≤ n := hroom
  obtain ⟨hJ, hcount, hend, _, _, hstarts⟩ := schedule_bounds n r (sourceWidth r)
    hr hn0 hW0 (sourceWidth_dvd r) hroom'
  have hzero := hstarts 0 hJ
  have hstartHalf : n ≤ 2 * scheduleStart n r := by simpa [sparseStart] using hzero.2.1
  have hstartEnd : scheduleStart n r ≤ sparseEnd n r (sourceWidth r) := by
    unfold sparseEnd
    omega
  have htailHalf : n ≤ 2 * tailStart n := by omega
  have htail49 : 49 ≤ tailStart n := by nlinarith only [hsize, hrpow, htailHalf, hr]
  refine ⟨hn0, hW0, hJ, sparse_count_rational n r (sourceWidth r)
    (sparseBlocks n r (sourceWidth r)) hr0 hW0 hcount, htail49, ?_⟩
  intro i hi
  obtain ⟨hdiv, hhalf, hle⟩ := hstarts i hi
  have hmult := Nat.mul_le_mul_right (8 * errorNumerator r (sourceWidth r))
    (show 1 ≤ r by omega)
  have hE : 4 * errorNumerator r (sourceWidth r) ≤ sparseStart n r (sourceWidth r) i := by
    nlinarith only [hmult, hprimitive, hhalf]
  exact ⟨hdiv, hE, hhalf, hle⟩

theorem local_error_le_quarter (n m r E : ℚ) (hr : 0 < r) (hm : 0 < m)
    (hprimitive : 8 * r * E ≤ n) (hhalf : n ≤ 2 * m) :
    E / m ≤ 1 / (4 * r) := by
  apply (div_le_div_iff₀ hm (by positivity : (0 : ℚ) < 4 * r)).2
  nlinarith only [hprimitive, hhalf]

/-- The actual schedule and source estimates imply the local ratio and
the small pending mass. No existence assertion for these sequences occurs. -/
theorem scheduled_sparse_estimates (n r : ℕ) (hr : 6 ≤ r)
    (hn : transferConstant * r ^ 61 ≤ n) (f g theta epsilon : ℕ → ℚ)
    (hf : ∀ i < sparseBlocks n r (sourceWidth r), 0 ≤ f i ∧ f i ≤ 1)
    (hformulaF : ∀ i < sparseBlocks n r (sourceWidth r),
      f i = (sourceRho r * (sourceWidth r : ℚ) /
        (sparseStart n r (sourceWidth r) i : ℚ)) * (1 + theta i))
    (hformulaG : ∀ i < sparseBlocks n r (sourceWidth r),
      g i = ((2 * ((r : ℚ) - 1) / ((r : ℚ) - 2)) *
        (sourceRho r * (sourceWidth r : ℚ)) /
        (sparseStart n r (sourceWidth r) i : ℚ) ^ 2) * (1 + epsilon i))
    (herr : ∀ i < sparseBlocks n r (sourceWidth r),
      |theta i| ≤ (errorNumerator r (sourceWidth r) : ℚ) /
          (sparseStart n r (sourceWidth r) i : ℚ) ∧
      |epsilon i| ≤ (errorNumerator r (sourceWidth r) : ℚ) /
          (sparseStart n r (sourceWidth r) i : ℚ)) :
    (∀ i < sparseBlocks n r (sourceWidth r),
      (n : ℚ) * g i ≤ (2 + 9 / (r : ℚ)) * f i) ∧
      (r : ℚ) / 4 ≤ densitySum f (sparseBlocks n r (sourceWidth r)) ∧
      pending f (sparseBlocks n r (sourceWidth r)) ≤ 4 / (r : ℚ) := by
  obtain ⟨hn0, hW0, _, hJ, _, hstarts⟩ := source_schedule_valid n r hr hn
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℚ) < r := by linarith only [hrQ]
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn0
  have hWQ : (0 : ℚ) < sourceWidth r := by exact_mod_cast hW0
  obtain ⟨hrho, _⟩ := sourceRho_bounds r hr
  have hrho0 : 0 ≤ sourceRho r := (sq_nonneg (r : ℚ)).trans hrho
  have hprimitive : 8 * (r : ℚ) * (errorNumerator r (sourceWidth r) : ℚ) ≤ n := by
    exact_mod_cast (construction_threshold_conditions r n hr hn).1
  have hstartLower : (((r : ℚ) - 1) / (r : ℚ)) * (n : ℚ) ≤
      (scheduleStart n r : ℚ) :=
    (roundUpMultiple_bounds r ((((r : ℚ) - 1) / (r : ℚ)) * (n : ℚ))
      (by omega)
      (mul_nonneg (div_nonneg (by linarith only [hrQ]) (le_of_lt hr0))
        (le_of_lt hnQ))).1
  have hlocal : ∀ i < sparseBlocks n r (sourceWidth r),
      (n : ℚ) * g i ≤ (2 + 9 / (r : ℚ)) * f i ∧
      sourceRho r * (sourceWidth r : ℚ) / (2 * (n : ℚ)) ≤ f i := by
    intro i hi
    obtain ⟨_, _, hhalfN, hleN⟩ := hstarts i hi
    have hhalf : (n : ℚ) ≤ 2 * (sparseStart n r (sourceWidth r) i : ℚ) := by
      exact_mod_cast hhalfN
    have hm0 : (0 : ℚ) < sparseStart n r (sourceWidth r) i := by linarith only [hhalf, hnQ]
    have hle : (sparseStart n r (sourceWidth r) i : ℚ) ≤ n := by exact_mod_cast hleN
    have herrSmall := local_error_le_quarter (n : ℚ)
      (sparseStart n r (sourceWidth r) i : ℚ) (r : ℚ)
      (errorNumerator r (sourceWidth r) : ℚ) hr0 hm0 hprimitive hhalf
    have htheta := (herr i hi).1.trans herrSmall
    have hepsilon := (herr i hi).2.trans herrSmall
    have hm : (((r : ℚ) - 1) / (r : ℚ)) * (n : ℚ) ≤
        (sparseStart n r (sourceWidth r) i : ℚ) := by
      apply hstartLower.trans
      exact_mod_cast (show scheduleStart n r ≤ sparseStart n r (sourceWidth r) i by
        unfold sparseStart
        omega)
    have hquarter : 1 / (4 * (r : ℚ)) ≤ (1 / 2 : ℚ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℚ) < 4 * (r : ℚ))).2
      linarith only [hrQ]
    have hthetaHalf : -(1 / 2 : ℚ) ≤ theta i := by
      have h := (abs_le.mp htheta).1
      linarith only [h, hquarter]
    exact ⟨sparse_local_cost_bound (n : ℚ) (sparseStart n r (sourceWidth r) i : ℚ)
      (r : ℚ) (sourceRho r * (sourceWidth r : ℚ)) (theta i) (epsilon i) (f i) (g i)
      hrQ hnQ hm (mul_nonneg hrho0 (le_of_lt hWQ)) htheta hepsilon
      (hformulaF i hi) (hformulaG i hi),
      sparse_density_lower (n : ℚ) (sparseStart n r (sourceWidth r) i : ℚ)
        (sourceRho r) (sourceWidth r : ℚ) (theta i) (f i) hnQ hm0 hle hrho0
        (le_of_lt hWQ) hthetaHalf (hformulaF i hi)⟩
  have hsum := sparse_densitySum_ge f (sparseBlocks n r (sourceWidth r))
    (n : ℚ) (r : ℚ) (sourceRho r) (sourceWidth r : ℚ) hnQ hr0 hWQ hrho hJ
    (fun i hi => (hlocal i hi).2)
  exact ⟨fun i hi => (hlocal i hi).1, hsum,
    pending_le_four_div f (sparseBlocks n r (sourceWidth r)) (r : ℚ) hr0 hf hsum⟩

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.source_schedule_valid
#print axioms CoefficientTwoPrecision.scheduled_sparse_estimates
