import Quantitative.ScheduledTransfer
import Quantitative.CountNormalization

/-!
# The normalized circle count

The sparse comparison uses the actual local source charge and circle
counts. The dense comparison telescopes the contraction of pending mass.
These lemmas establish the numerical completion error once the stated
updates have been realized by stages.
-/

namespace CoefficientTwoPrecision

theorem normalized_circle_ratio (q c D m m0 r : ℚ)
    (hq : 0 ≤ q) (hD : 0 < D) (hm0 : 0 < m0) (hm : m0 ≤ m)
    (hr : 1 ≤ r) (hsource : c ≤ (r - 1) * q / m) :
    c / D ≤ ((r - 1) / m0) * (q / D) := by
  have hnum : 0 ≤ (r - 1) * q := mul_nonneg (sub_nonneg.mpr hr) hq
  have hcompare := div_le_div_of_nonneg_left hnum hm0 hm
  have hbound := hsource.trans hcompare
  calc
    c / D ≤ ((r - 1) * q / m0) / D := div_le_div_of_nonneg_right hbound (le_of_lt hD)
    _ = ((r - 1) / m0) * (q / D) := by ring

theorem accumulatedCost_nonneg (f g : ℕ → ℚ) (J : ℕ)
    (hf : ∀ i < J, f i ≤ 1) (hg : ∀ i < J, 0 ≤ g i) :
    0 ≤ accumulatedCost f g J := by
  induction J with
  | zero => simp [accumulatedCost]
  | succ J ih =>
    exact add_nonneg (ih (fun i hi => hf i (by omega)) (fun i hi => hg i (by omega)))
      (mul_nonneg (pending_nonneg f J (fun i hi => hf i (by omega))) (hg J (by omega)))

theorem accumulatedCost_congr (f g g' : ℕ → ℚ) (J : ℕ)
    (hg : ∀ i < J, g i = g' i) : accumulatedCost f g J = accumulatedCost f g' J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    simp only [accumulatedCost, ih (fun i hi => hg i (by omega)), hg J (by omega)]

theorem accumulatedCost_add (f q c : ℕ → ℚ) (J : ℕ) :
    accumulatedCost f (fun i => q i + c i) J =
      accumulatedCost f q J + accumulatedCost f c J := by
  induction J with
  | zero => simp [accumulatedCost]
  | succ J ih => simp only [accumulatedCost, ih]; ring

theorem accumulatedCost_compare (f q c : ℕ → ℚ) (J : ℕ) (K : ℚ)
    (hf : ∀ i < J, f i ≤ 1) (hc : ∀ i < J, c i ≤ K * q i) :
    accumulatedCost f c J ≤ K * accumulatedCost f q J := by
  induction J with
  | zero => simp [accumulatedCost]
  | succ J ih =>
    have hprev := ih (fun i hi => hf i (by omega)) (fun i hi => hc i (by omega))
    have hlast := mul_le_mul_of_nonneg_left (hc J (by omega))
      (pending_nonneg f J (fun i hi => hf i (by omega)))
    simp only [accumulatedCost]
    nlinarith only [hprev, hlast]

theorem sparse_circle_bound (f q c : ℕ → ℚ) (J : ℕ) (m0 r : ℚ)
    (hm0 : 0 < m0) (hr : 1 ≤ r)
    (hf : ∀ i < J, f i ≤ 1) (hc0 : ∀ i < J, 0 ≤ c i)
    (hratio : ∀ i < J, c i ≤ ((r - 1) / m0) * q i)
    (hcost : ∀ i < J, m0 * (q i + c i) ≤ 8 * f i) :
    accumulatedCost f c J ≤ 8 * (r - 1) / m0 ^ 2 := by
  have hcircles := accumulatedCost_compare f q c J ((r - 1) / m0) hf hratio
  have hz0 := accumulatedCost_nonneg f c J hf hc0
  have hp0 := pending_nonneg f J hf
  have hI := cost_invariant f (fun i => q i + c i) J m0 8 hf hcost
  rw [accumulatedCost_add] at hI
  have htotal : m0 * (accumulatedCost f q J + accumulatedCost f c J) ≤ 8 := by
    linarith only [hI, hp0]
  have hy : accumulatedCost f q J ≤ 8 / m0 := by
    apply (le_div_iff₀ hm0).2
    have hnonneg := mul_nonneg (le_of_lt hm0) hz0
    nlinarith only [htotal, hnonneg]
  calc
    accumulatedCost f c J ≤ ((r - 1) / m0) * accumulatedCost f q J := hcircles
    _ ≤ ((r - 1) / m0) * (8 / m0) :=
      mul_le_mul_of_nonneg_left hy (div_nonneg (sub_nonneg.mpr hr) (le_of_lt hm0))
    _ = 8 * (r - 1) / m0 ^ 2 := by ring

theorem contraction_sum_bound (p : ℕ → ℚ) (K : ℕ)
    (hstep : ∀ i < K, p (i + 1) ≤ (3 / 4) * p i) :
    densitySum p K ≤ 4 * (p 0 - p K) := by
  induction K with
  | zero => simp [densitySum]
  | succ K ih =>
    have hprev := ih (fun i hi => hstep i (by omega))
    have hlast := hstep K (by omega)
    simp only [densitySum]
    linarith only [hprev, hlast]

theorem increments_le_densitySum (z p : ℕ → ℚ) (K : ℕ) (b : ℚ)
    (hstep : ∀ i < K, z (i + 1) - z i ≤ b * p i) :
    z K - z 0 ≤ b * densitySum p K := by
  induction K with
  | zero => simp [densitySum]
  | succ K ih =>
    have hprev := ih (fun i hi => hstep i (by omega))
    have hlast := hstep K (by omega)
    simp only [densitySum]
    nlinarith only [hprev, hlast]

theorem dense_circle_bound (z p : ℕ → ℚ) (K : ℕ) (a : ℚ) (ha : 0 < a)
    (hzero : p 0 ≤ 1) (hend : 0 ≤ p K)
    (hcontraction : ∀ i < K, p (i + 1) ≤ (3 / 4) * p i)
    (hincrement : ∀ i < K, z (i + 1) - z i ≤ (8 / (a * (a + 1))) * p i) :
    z K - z 0 ≤ 32 / (a * (a + 1)) := by
  have hsum : densitySum p K ≤ 4 := by
    have h := contraction_sum_bound p K hcontraction
    linarith only [h, hzero, hend]
  have hinc := increments_le_densitySum z p K (8 / (a * (a + 1))) hincrement
  calc
    z K - z 0 ≤ (8 / (a * (a + 1))) * densitySum p K := hinc
    _ ≤ (8 / (a * (a + 1))) * 4 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 32 / (a * (a + 1)) := by ring

theorem dense_circle_increment_uniform (a b p : ℚ) (ha : 0 < a)
    (hab : a ≤ b) (hp : 0 ≤ p) : 8 * p / (b * (b + 1)) ≤
      (8 / (a * (a + 1))) * p := by
  have hden : a * (a + 1) ≤ b * (b + 1) :=
    mul_le_mul hab (add_le_add hab (le_refl 1)) (by linarith) (ha.le.trans hab)
  calc
    8 * p / (b * (b + 1)) ≤ 8 * p / (a * (a + 1)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (8 / (a * (a + 1))) * p := by ring

theorem circle_mass_uniform (n m0 a r sparse tail : ℚ)
    (hn : 0 < n) (hm0 : 0 < m0) (ha : 0 < a) (hr : 1 ≤ r)
    (hhalf : n ≤ 2 * m0) (htailhalf : n ≤ 2 * a)
    (hsparse : sparse ≤ 8 * (r - 1) / m0 ^ 2)
    (htail : tail ≤ 32 / (a * (a + 1))) :
    sparse + tail ≤ (32 * r + 96) / n ^ 2 := by
  have hmSquare : n ^ 2 ≤ 4 * m0 ^ 2 := by
    have h := pow_le_pow_left₀ (le_of_lt hn) hhalf 2
    nlinarith only [h]
  have haSquare : n ^ 2 ≤ 4 * (a * (a + 1)) := by
    have h := pow_le_pow_left₀ (le_of_lt hn) htailhalf 2
    nlinarith only [h, ha]
  have hsInverse : 1 / m0 ^ 2 ≤ 4 / n ^ 2 :=
    (div_le_div_iff₀ (pow_pos hm0 2) (pow_pos hn 2)).2 (by simpa only [one_mul] using hmSquare)
  have htInverse : 1 / (a * (a + 1)) ≤ 4 / n ^ 2 :=
    (div_le_div_iff₀ (by positivity) (pow_pos hn 2)).2 (by simpa only [one_mul] using haSquare)
  have hs : sparse ≤ 32 * (r - 1) / n ^ 2 := by
    calc
      sparse ≤ 8 * (r - 1) / m0 ^ 2 := hsparse
      _ = (8 * (r - 1)) * (1 / m0 ^ 2) := by ring
      _ ≤ (8 * (r - 1)) * (4 / n ^ 2) :=
        mul_le_mul_of_nonneg_left hsInverse (by nlinarith only [hr])
      _ = 32 * (r - 1) / n ^ 2 := by ring
  have ht : tail ≤ 128 / n ^ 2 := by
    calc
      tail ≤ 32 / (a * (a + 1)) := htail
      _ = 32 * (1 / (a * (a + 1))) := by ring
      _ ≤ 32 * (4 / n ^ 2) := mul_le_mul_of_nonneg_left htInverse (by norm_num)
      _ = 128 / n ^ 2 := by ring
  calc
    sparse + tail ≤ 32 * (r - 1) / n ^ 2 + 128 / n ^ 2 := add_le_add hs ht
    _ = (32 * r + 96) / n ^ 2 := by ring

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.sparse_circle_bound
#print axioms CoefficientTwoPrecision.dense_circle_bound
#print axioms CoefficientTwoPrecision.circle_mass_uniform
