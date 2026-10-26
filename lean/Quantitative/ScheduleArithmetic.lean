import Quantitative.ConstructionParameters
import Quantitative.CompletionEstimates

/-!
# Finite schedule, sparse densities, and terminal contraction

The schedule consists of a rounded starting size, a whole number of sparse
blocks, fewer than one sparse width of empty steps, and a binary-length
terminal segment. These lemmas concern integers and exact rational
recurrences. Existence of the corresponding geometric stages is not asserted.
-/

namespace CoefficientTwoPrecision

def roundUpMultiple (r : ℕ) (x : ℚ) : ℕ := r * ⌈x / (r : ℚ)⌉₊

theorem roundUpMultiple_bounds (r : ℕ) (x : ℚ) (hr : 0 < r) (hx : 0 ≤ x) :
    x ≤ (roundUpMultiple r x : ℚ) ∧ (roundUpMultiple r x : ℚ) < x + r ∧
      r ∣ roundUpMultiple r x := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hlo := Nat.le_ceil (x / (r : ℚ))
  have hhi := Nat.ceil_lt_add_one (div_nonneg hx (le_of_lt hrQ))
  have hcast : (roundUpMultiple r x : ℚ) =
      (r : ℚ) * (⌈x / (r : ℚ)⌉₊ : ℚ) := by simp only [roundUpMultiple, Nat.cast_mul]
  refine ⟨?_, ?_, ⟨⌈x / (r : ℚ)⌉₊, rfl⟩⟩
  · rw [hcast]
    have h := (div_le_iff₀ hrQ).1 hlo
    simpa only [mul_comm] using h
  · rw [hcast]
    calc
      (r : ℚ) * (⌈x / (r : ℚ)⌉₊ : ℚ) < (r : ℚ) * (x / (r : ℚ) + 1) :=
        mul_lt_mul_of_pos_left hhi hrQ
      _ = x + r := by field_simp [ne_of_gt hrQ] <;> ring

def scheduleStart (n r : ℕ) : ℕ :=
  roundUpMultiple r ((((r : ℚ) - 1) / (r : ℚ)) * (n : ℚ))

def tailLength (n : ℕ) : ℕ := 3 + 36 * binaryLength n

def denseBlocks (n : ℕ) : ℕ := 12 * binaryLength n

def tailStart (n : ℕ) : ℕ := n - tailLength n

def sparseBlocks (n r W : ℕ) : ℕ := (tailStart n - scheduleStart n r) / W

def sparseEnd (n r W : ℕ) : ℕ := scheduleStart n r + sparseBlocks n r W * W

def sparseStart (n r W i : ℕ) : ℕ := scheduleStart n r + i * W

theorem scheduleStart_scaled_bounds (n r : ℕ) (hr : 2 ≤ r) :
    (r - 1) * n ≤ r * scheduleStart n r ∧
      r * scheduleStart n r < (r - 1) * n + r ^ 2 ∧
      r ∣ scheduleStart n r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr1 : (1 : ℚ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have harg : 0 ≤ (((r : ℚ) - 1) / (r : ℚ)) * (n : ℚ) := by positivity
  obtain ⟨hlo, hhi, hdvd⟩ := roundUpMultiple_bounds r
    ((((r : ℚ) - 1) / (r : ℚ)) * (n : ℚ)) (by omega) harg
  have hlow := mul_le_mul_of_nonneg_left hlo (le_of_lt hrQ)
  have hupp := mul_lt_mul_of_pos_left hhi hrQ
  have hidentity : (r : ℚ) * ((((r : ℚ) - 1) / (r : ℚ)) * (n : ℚ)) =
      ((r : ℚ) - 1) * (n : ℚ) := by field_simp [ne_of_gt hrQ] <;> ring
  have hNatSub : ((r - 1 : ℕ) : ℚ) = (r : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hlowQ : ((r : ℚ) - 1) * (n : ℚ) ≤ (r : ℚ) * (scheduleStart n r : ℚ) := by
    simpa only [hidentity, scheduleStart] using hlow
  have huppQ : (r : ℚ) * (scheduleStart n r : ℚ) <
      ((r : ℚ) - 1) * (n : ℚ) + (r : ℚ) ^ 2 := by
    calc
      (r : ℚ) * (scheduleStart n r : ℚ) <
          (r : ℚ) * ((((r : ℚ) - 1) / (r : ℚ)) * (n : ℚ) + r) := hupp
      _ = ((r : ℚ) - 1) * (n : ℚ) + (r : ℚ) ^ 2 := by
        rw [mul_add, hidentity]
        ring
  refine ⟨?_, ?_, hdvd⟩
  · rw [← hNatSub] at hlowQ
    exact_mod_cast hlowQ
  · rw [← hNatSub] at huppQ
    exact_mod_cast huppQ

/-- Pure integer facts behind the schedule. The upper rounding bound is
strict and therefore loses less than one multiple of `r`. -/
theorem integer_schedule_bounds (n r W tau m0 : ℕ) (hr : 2 ≤ r)
    (hn : 0 < n) (hW : 0 < W)
    (hlo : (r - 1) * n ≤ r * m0)
    (hhi : r * m0 < (r - 1) * n + r ^ 2)
    (hroom : 2 * r * (r + W + tau) ≤ n) :
    m0 + tau + W < n ∧ n ≤ 2 * m0 ∧
      n ≤ 2 * r * ((n - tau - m0) / W) * W := by
  have hr0 : 0 < r := by omega
  have hsplit : (r - 1) * n + n = r * n := by
    have heq : r - 1 + 1 = r := by omega
    calc
      (r - 1) * n + n = (r - 1 + 1) * n := by ring
      _ = r * n := by rw [heq]
  have hroomWeak : r * (r + W + tau) ≤ n := by nlinarith only [hroom]
  have hfitMul : r * (m0 + tau + W) < r * n := by
    nlinarith only [hhi, hsplit, hroomWeak]
  have hfit : m0 + tau + W < n := (mul_lt_mul_iff_right₀ hr0).1 hfitMul
  have hdouble := Nat.mul_le_mul_right n (show r ≤ 2 * (r - 1) by omega)
  have hhalfMul : n * r ≤ (2 * m0) * r := by nlinarith only [hlo, hdouble]
  have hhalf : n ≤ 2 * m0 := (mul_le_mul_iff_left₀ hr0).1 hhalfMul
  have hgap : n - tau - m0 + m0 + tau = n := by omega
  have hfloor : n - tau - m0 < W * ((n - tau - m0) / W + 1) :=
    Nat.lt_mul_div_succ _ hW
  have hfloorMul := Nat.mul_lt_mul_of_pos_left hfloor (show 0 < 2 * r by omega)
  have hcount : n ≤ 2 * r * ((n - tau - m0) / W) * W := by
    nlinarith only [hgap, hfloorMul, hhi, hsplit, hroom]
  exact ⟨hfit, hhalf, hcount⟩

theorem schedule_bounds (n r W : ℕ) (hr : 6 ≤ r) (hn : 0 < n)
    (hW : 0 < W) (hdiv : r ∣ W)
    (hroom : 2 * r * (r + W + tailLength n) ≤ n) :
    0 < sparseBlocks n r W ∧
      n ≤ 2 * r * sparseBlocks n r W * W ∧
      sparseEnd n r W ≤ tailStart n ∧
      tailStart n - sparseEnd n r W < W ∧
      tailStart n + 3 * denseBlocks n = n - 3 ∧
      (∀ i < sparseBlocks n r W,
        r ∣ sparseStart n r W i ∧ n ≤ 2 * sparseStart n r W i ∧
          sparseStart n r W i ≤ n) := by
  obtain ⟨hlo, hhi, hstartdiv⟩ := scheduleStart_scaled_bounds n r (by omega)
  obtain ⟨hfit, hhalf, hcount⟩ := integer_schedule_bounds n r W (tailLength n)
    (scheduleStart n r) (by omega) hn hW hlo hhi hroom
  have hstarttail : scheduleStart n r ≤ tailStart n := by unfold tailStart; omega
  have htaun : tailLength n ≤ n := by omega
  have hcount' : n ≤ 2 * r * sparseBlocks n r W * W := hcount
  have hJpos : 0 < sparseBlocks n r W := by
    by_contra h
    have hzero : sparseBlocks n r W = 0 := by omega
    rw [hzero] at hcount'
    simp only [Nat.mul_zero, Nat.zero_mul] at hcount'
    omega
  have hgap : tailStart n - scheduleStart n r + scheduleStart n r = tailStart n :=
    Nat.sub_add_cancel hstarttail
  have hquot := Nat.div_mul_le_self (tailStart n - scheduleStart n r) W
  have hend : sparseEnd n r W ≤ tailStart n := by
    unfold sparseEnd sparseBlocks
    omega
  have hrem := Nat.mod_lt (tailStart n - scheduleStart n r) hW
  have hmod := Nat.mod_add_div' (tailStart n - scheduleStart n r) W
  have hpadding : tailStart n - sparseEnd n r W < W := by
    unfold sparseEnd sparseBlocks
    omega
  have hfinish : tailStart n + 3 * denseBlocks n = n - 3 := by
    unfold tailStart tailLength denseBlocks at *
    omega
  refine ⟨hJpos, hcount', hend, hpadding, hfinish, ?_⟩
  intro i hi
  have himul := Nat.mul_le_mul_right W (Nat.le_of_lt hi)
  have hstartEnd : sparseStart n r W i ≤ sparseEnd n r W := by
    unfold sparseStart sparseEnd
    omega
  have hm0 : scheduleStart n r ≤ sparseStart n r W i := by unfold sparseStart; omega
  refine ⟨dvd_add hstartdiv (dvd_mul_of_dvd_right hdiv i), by omega, ?_⟩
  exact hstartEnd.trans (hend.trans (Nat.sub_le n (tailLength n)))

/-- A uniform lower bound on individual sparse densities. -/
theorem sparse_density_lower (n m rho W theta f : ℚ) (hn : 0 < n)
    (hm : 0 < m) (hmn : m ≤ n) (hrho : 0 ≤ rho) (hW : 0 ≤ W)
    (htheta : -(1 / 2) ≤ theta) (hf : f = (rho * W / m) * (1 + theta)) :
    rho * W / (2 * n) ≤ f := by
  have hnum : 0 ≤ rho * W := mul_nonneg hrho hW
  have hquot := div_le_div_of_nonneg_left hnum hm hmn
  have hphase : (1 / 2 : ℚ) ≤ 1 + theta := by linarith
  calc
    rho * W / (2 * n) = (rho * W / n) * (1 / 2) := by ring
    _ ≤ (rho * W / m) * (1 / 2) := mul_le_mul_of_nonneg_right hquot (by norm_num)
    _ ≤ (rho * W / m) * (1 + theta) :=
      mul_le_mul_of_nonneg_left hphase (div_nonneg hnum (le_of_lt hm))
    _ = f := hf.symm

theorem densitySum_lower (f : ℕ → ℚ) (J : ℕ) (b : ℚ)
    (hf : ∀ i < J, b ≤ f i) : (J : ℚ) * b ≤ densitySum f J := by
  induction J with
  | zero => simp [densitySum]
  | succ J ih =>
    have hprev := ih (fun i hi => hf i (by omega))
    have hlast := hf J (by omega)
    simp only [densitySum, Nat.cast_add, Nat.cast_one]
    linarith only [hprev, hlast]

theorem sparse_densitySum_ge (f : ℕ → ℚ) (J : ℕ) (n r rho W : ℚ)
    (hn : 0 < n) (hr : 0 < r) (hW : 0 < W) (hrho : r ^ 2 ≤ rho)
    (hJ : n / (2 * r * W) ≤ (J : ℚ))
    (hf : ∀ i < J, rho * W / (2 * n) ≤ f i) : r / 4 ≤ densitySum f J := by
  have hrho0 : 0 ≤ rho := (sq_nonneg r).trans hrho
  have hb : 0 ≤ rho * W / (2 * n) := by positivity
  have hsum := densitySum_lower f J (rho * W / (2 * n)) hf
  have hcount := mul_le_mul_of_nonneg_right hJ hb
  have hidentity : (n / (2 * r * W)) * (rho * W / (2 * n)) = rho / (4 * r) := by
    field_simp [ne_of_gt hn, ne_of_gt hr, ne_of_gt hW] <;> ring
  have hrholower : r / 4 ≤ rho / (4 * r) := by
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 4 * r)).2
    nlinarith only [hrho]
  exact hrholower.trans (by rw [hidentity] at hcount; exact hcount.trans hsum)

theorem pending_after_sparse (f : ℕ → ℚ) (J : ℕ) (n r rho W : ℚ)
    (hn : 0 < n) (hr : 0 < r) (hW : 0 < W) (hrho : r ^ 2 ≤ rho)
    (hJ : n / (2 * r * W) ≤ (J : ℚ))
    (hf : ∀ i < J, 0 ≤ f i ∧ f i ≤ 1)
    (hlower : ∀ i < J, rho * W / (2 * n) ≤ f i) : pending f J ≤ 4 / r := by
  exact pending_le_four_div f J r hr hf
    (sparse_densitySum_ge f J n r rho W hn hr hW hrho hJ hlower)

theorem geometric_tail_bound (p : ℕ → ℚ) (K : ℕ) (hzero : p 0 ≤ 1)
    (hstep : ∀ i < K, p (i + 1) ≤ (3 / 4) * p i) :
    p K ≤ (3 / 4 : ℚ) ^ K := by
  induction K with
  | zero => simpa using hzero
  | succ K ih =>
    have hprev := ih (fun i hi => hstep i (by omega))
    calc
      p (K + 1) ≤ (3 / 4) * p K := hstep K (by omega)
      _ ≤ (3 / 4) * (3 / 4 : ℚ) ^ K :=
        mul_le_mul_of_nonneg_left hprev (by norm_num)
      _ = (3 / 4 : ℚ) ^ (K + 1) := by rw [pow_succ]; ring

theorem dense_pending_lt_inverse_cube (n : ℕ) (hn : 0 < n)
    (p : ℕ → ℚ) (hzero : p 0 ≤ 1)
    (hstep : ∀ i < denseBlocks n, p (i + 1) ≤ (3 / 4) * p i) :
    p (denseBlocks n) < 1 / (n : ℚ) ^ 3 := by
  have htail := geometric_tail_bound p (denseBlocks n) hzero hstep
  have hbase : (3 / 4 : ℚ) ^ 12 ≤ (1 / 2 : ℚ) ^ 3 := by norm_num
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ (3 / 4 : ℚ) ^ 12)
    hbase (binaryLength n)
  have hcontract : (3 / 4 : ℚ) ^ denseBlocks n ≤
      1 / ((2 : ℚ) ^ binaryLength n) ^ 3 := by
    unfold denseBlocks
    calc
      (3 / 4 : ℚ) ^ (12 * binaryLength n) =
          ((3 / 4 : ℚ) ^ 12) ^ binaryLength n := pow_mul _ _ _
      _ ≤ ((1 / 2 : ℚ) ^ 3) ^ binaryLength n := hpow
      _ = 1 / ((2 : ℚ) ^ binaryLength n) ^ 3 := by
        simp only [← pow_mul, div_pow, one_pow]
        congr 2
        omega
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hbinary : (n : ℚ) < (2 : ℚ) ^ binaryLength n := by
    exact_mod_cast (binaryLength_bounds n hn).2
  have hcubes := pow_lt_pow_left₀ hbinary (le_of_lt hnQ) (by decide : 3 ≠ 0)
  have hinverse : 1 / ((2 : ℚ) ^ binaryLength n) ^ 3 < 1 / (n : ℚ) ^ 3 := by
    apply (div_lt_div_iff₀ (by positivity) (pow_pos hnQ 3)).2
    simpa only [one_mul] using hcubes
  exact (htail.trans hcontract).trans_lt hinverse

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.schedule_bounds
#print axioms CoefficientTwoPrecision.pending_after_sparse
#print axioms CoefficientTwoPrecision.dense_pending_lt_inverse_cube
