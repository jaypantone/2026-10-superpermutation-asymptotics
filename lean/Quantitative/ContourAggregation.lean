import Quantitative.CanonicalSourceFamily
import Mathlib.Tactic

/-!
# Finite aggregation of the actual canonical contours

All row and connector counts in this file are lengths or charge sums of the
actual lists constructed in SourceFamilyAdapter. Per-contour geometric
estimates imply the aggregate charge, connector bound, and one averaged
relative row error. Empty collections are included explicitly.
-/

namespace CoefficientTwoPrecision.ContourAggregation

open SuperpermutationUpperBound SourceFamilyAdapter SourceAdvancement

variable {A : List ℕ} {h : ℕ}

/-- Concatenation counts actual row occurrences, including multiplicities. -/
theorem rows_length (F : List (SourceContour A h)) :
    (sourceRows F).length = (F.map (fun C => C.rows.length)).sum := by
  simp only [sourceRows, List.length_flatMap]

theorem rows_charge (F : List (SourceContour A h)) :
    ((sourceRows F).map Row.charge).sum =
      (F.map (fun C => (C.rows.map Row.charge).sum)).sum := by
  induction F with
  | nil => rfl
  | cons C rest ih =>
    simpa only [sourceRows, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] using congrArg (fun q => (C.rows.map Row.charge).sum + q) ih

/-- The exact short charge is the same in every modified contour. -/
theorem uniform_charge (F : List (SourceContour A h)) (r M : ℕ)
    (hcharge : ∀ C ∈ F, (C.rows.map Row.charge).sum = 2 * (r - 1) * M) :
    ((sourceRows F).map Row.charge).sum = F.length * (2 * (r - 1) * M) := by
  rw [rows_charge]
  induction F with
  | nil => simp
  | cons C rest ih =>
    rw [List.map_cons, List.sum_cons, hcharge C (by simp),
      ih (fun D hD => hcharge D (by simp [hD])), List.length_cons]
    ring

/-- The actual list has two squared-gcd connectors for every contour. -/
theorem connector_bound (F : List (SourceContour A h)) (r : ℕ)
    (hg : ∀ C ∈ F, portGcd C.rows h ≤ r - 1) :
    (circles F).length ≤ F.length * (2 * (r - 1) ^ 2) := by
  rw [circles_length]
  induction F with
  | nil => simp
  | cons C rest ih =>
    have hsq := Nat.mul_le_mul (hg C (by simp)) (hg C (by simp))
    have hC : 2 * (portGcd C.rows h) ^ 2 ≤ 2 * (r - 1) ^ 2 := by
      nlinarith only [hsq]
    have hrest := ih (fun D hD => hg D (by simp [hD]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith only [hC, hrest]

/-- The connector estimate is tied to the actual total charge. -/
theorem connector_times_background (F : List (SourceContour A h)) (r M : ℕ)
    (hcharge : ∀ C ∈ F, (C.rows.map Row.charge).sum = 2 * (r - 1) * M)
    (hg : ∀ C ∈ F, portGcd C.rows h ≤ r - 1) :
    M * (circles F).length ≤ (r - 1) * ((sourceRows F).map Row.charge).sum := by
  rw [uniform_charge F r M hcharge]
  calc
    M * (circles F).length ≤ M * (F.length * (2 * (r - 1) ^ 2)) :=
      Nat.mul_le_mul_left M (connector_bound F r hg)
    _ = (r - 1) * (F.length * (2 * (r - 1) * M)) := by ring

/-- This is the precise circle-to-charge ratio used by SparseBlockCertificate. -/
theorem connector_ratio (F : List (SourceContour A h)) (r m M : ℕ)
    (hr : 1 ≤ r) (hm : 0 < m) (hmM : m ≤ M)
    (hcharge : ∀ C ∈ F, (C.rows.map Row.charge).sum = 2 * (r - 1) * M)
    (hg : ∀ C ∈ F, portGcd C.rows h ≤ r - 1) :
    ((circles F).length : ℚ) ≤ ((r : ℚ) - 1) *
      (((sourceRows F).map Row.charge).sum : ℚ) / (m : ℚ) := by
  have hscaled := (Nat.mul_le_mul_right (circles F).length hmM).trans
    (connector_times_background F r M hcharge hg)
  have hcast : (m : ℚ) * ((circles F).length : ℚ) ≤
      ((r : ℚ) - 1) * (((sourceRows F).map Row.charge).sum : ℚ) := by
    have hc : ((m * (circles F).length : ℕ) : ℚ) ≤
        (((r - 1) * ((sourceRows F).map Row.charge).sum : ℕ) : ℚ) := by
      exact_mod_cast hscaled
    simpa only [Nat.cast_mul, Nat.cast_sub hr, Nat.cast_one] using hc
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  exact (le_div_iff₀ hmQ).2 (by simpa only [mul_comm] using hcast)

private theorem relative_identity (N L : ℚ) (hL : 0 < L) :
    |N / L - 1| = |N - L| / L := by
  rw [show N / L - 1 = (N - L) / L by field_simp [ne_of_gt hL],
    abs_div, abs_of_pos hL]

/-- The normal term and a bounded perturbation give the per-contour relative
error used in the average. The event allowance is K <= 52 r^4 W^2. -/
theorem contour_relative_error (N r m M W K : ℚ) (hr : 6 ≤ r) (hm : 0 < m)
    (hmM : m ≤ M) (hK : 0 ≤ K) (hKbound : K ≤ 52 * r ^ 4 * W ^ 2)
    (hperturb : |N - ((r - 2) * M ^ 2 + (r * (r - 1) + 1) * M)| ≤
      10 * r ^ 2 * K * M) :
    |N / ((r - 2) * M ^ 2) - 1| ≤ (2 * r + 1040 * r ^ 5 * W ^ 2) / m := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr2 : 0 < r - 2 := by linarith only [hr]
  have hM : 0 < M := hm.trans_le hmM
  have hL : 0 < (r - 2) * M ^ 2 := mul_pos hr2 (sq_pos_of_pos hM)
  have hbase0 : 0 ≤ (r * (r - 1) + 1) * M := by
    have hr1 : 0 ≤ r - 1 := by linarith only [hr]
    positivity
  have hbase : r * (r - 1) + 1 ≤ (r - 2) * (2 * r) := by
    have hs := sq_nonneg (r - 2)
    nlinarith only [hr, hs]
  have hmult : 10 * r ^ 2 ≤ (r - 2) * (20 * r) := by
    have hs := mul_nonneg hr0.le (show 0 ≤ r - 4 by linarith only [hr])
    nlinarith only [hs]
  have hmultK := mul_le_mul_of_nonneg_right hmult hK
  have hcoefficient : 10 * r ^ 2 * K + (r * (r - 1) + 1) ≤
      (r - 2) * (2 * r + 20 * r * K) := by
    calc
      10 * r ^ 2 * K + (r * (r - 1) + 1) ≤
          ((r - 2) * (20 * r)) * K + (r - 2) * (2 * r) := add_le_add hmultK hbase
      _ = (r - 2) * (2 * r + 20 * r * K) := by ring
  have hdeviation : |N - (r - 2) * M ^ 2| ≤
      (r - 2) * (2 * r + 20 * r * K) * M := by
    calc
      |N - (r - 2) * M ^ 2| =
          |(N - ((r - 2) * M ^ 2 + (r * (r - 1) + 1) * M)) +
            (r * (r - 1) + 1) * M| := by congr 1; ring
      _ ≤ |N - ((r - 2) * M ^ 2 + (r * (r - 1) + 1) * M)| +
          |(r * (r - 1) + 1) * M| := abs_add_le _ _
      _ ≤ 10 * r ^ 2 * K * M + (r * (r - 1) + 1) * M := by
        rw [abs_of_nonneg hbase0]
        exact add_le_add hperturb (le_refl _)
      _ = (10 * r ^ 2 * K + (r * (r - 1) + 1)) * M := by ring
      _ ≤ (r - 2) * (2 * r + 20 * r * K) * M :=
        mul_le_mul_of_nonneg_right hcoefficient hM.le
  have hKscaled : 2 * r + 20 * r * K ≤ 2 * r + 1040 * r ^ 5 * W ^ 2 := by
    calc
      2 * r + 20 * r * K ≤ 2 * r + (20 * r) * (52 * r ^ 4 * W ^ 2) := by
        have hp : 20 * r * K ≤ (20 * r) * (52 * r ^ 4 * W ^ 2) :=
          mul_le_mul_of_nonneg_left hKbound (mul_nonneg (by norm_num : (0 : ℚ) ≤ 20) hr0.le)
        exact add_le_add (le_refl (2 * r)) hp
      _ = 2 * r + 1040 * r ^ 5 * W ^ 2 := by ring
  rw [relative_identity N _ hL]
  calc
    |N - (r - 2) * M ^ 2| / ((r - 2) * M ^ 2) ≤
        ((r - 2) * (2 * r + 20 * r * K) * M) / ((r - 2) * M ^ 2) :=
      div_le_div_of_nonneg_right hdeviation hL.le
    _ = (2 * r + 20 * r * K) / M := by field_simp [ne_of_gt hr2, ne_of_gt hM] <;> ring
    _ ≤ (2 * r + 1040 * r ^ 5 * W ^ 2) / M :=
      div_le_div_of_nonneg_right hKscaled hM.le
    _ ≤ (2 * r + 1040 * r ^ 5 * W ^ 2) / m :=
      div_le_div_of_nonneg_left (by positivity) hm hmM

private theorem row_deviation_sum (F : List (SourceContour A h)) (L B : ℚ)
    (hlocal : ∀ C ∈ F, |(C.rows.length : ℚ) - L| ≤ B * L) :
    |((sourceRows F).length : ℚ) - (F.length : ℚ) * L| ≤ (F.length : ℚ) * (B * L) := by
  induction F with
  | nil => simp [sourceRows]
  | cons C rest ih =>
    have hC := hlocal C (by simp)
    have hrest := ih (fun D hD => hlocal D (by simp [hD]))
    have hlen : (sourceRows (C :: rest)).length = C.rows.length + (sourceRows rest).length := by
      simp only [sourceRows, List.flatMap_cons, List.length_append]
    simp only [hlen, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      |(C.rows.length : ℚ) + ((sourceRows rest).length : ℚ) - ((rest.length : ℚ) + 1) * L| =
          |((C.rows.length : ℚ) - L) + (((sourceRows rest).length : ℚ) - (rest.length : ℚ) * L)| := by
        congr 1
        ring
      _ ≤ |(C.rows.length : ℚ) - L| + |((sourceRows rest).length : ℚ) - (rest.length : ℚ) * L| :=
        abs_add_le _ _
      _ ≤ B * L + (rest.length : ℚ) * (B * L) := add_le_add hC hrest
      _ = ((rest.length : ℚ) + 1) * (B * L) := by ring

/-- Average relative errors over the actual finite collection. This also
handles the empty collection, with relative error zero. -/
theorem averaged_relative_error (F : List (SourceContour A h)) (L B : ℚ)
    (hL : 0 < L) (hB : 0 ≤ B)
    (hlocal : ∀ C ∈ F, |(C.rows.length : ℚ) / L - 1| ≤ B) :
    ∃ u : ℚ, ((sourceRows F).length : ℚ) = (F.length : ℚ) * L * (1 + u) ∧ |u| ≤ B := by
  by_cases hnil : F = []
  · subst F
    exact ⟨0, by simp [sourceRows], by simpa only [abs_zero] using hB⟩
  have hcount : (0 : ℚ) < F.length := by exact_mod_cast List.length_pos_of_ne_nil hnil
  have hden : 0 < (F.length : ℚ) * L := mul_pos hcount hL
  have hlocal' : ∀ C ∈ F, |(C.rows.length : ℚ) - L| ≤ B * L := by
    intro C hC
    have hi := hlocal C hC
    rw [relative_identity _ _ hL] at hi
    exact (div_le_iff₀ hL).1 hi
  have hsum := row_deviation_sum F L B hlocal'
  let u := ((sourceRows F).length : ℚ) / ((F.length : ℚ) * L) - 1
  refine ⟨u, ?_, ?_⟩
  · dsimp only [u]
    field_simp [ne_of_gt hcount, ne_of_gt hL] <;> ring
  · rw [show u = ((sourceRows F).length : ℚ) / ((F.length : ℚ) * L) - 1 from rfl,
      relative_identity _ _ hden]
    apply (div_le_iff₀ hden).2
    calc
      |((sourceRows F).length : ℚ) - (F.length : ℚ) * L| ≤
          (F.length : ℚ) * (B * L) := hsum
      _ = B * ((F.length : ℚ) * L) := by ring

/-- The actual canonical source count has the precise averaged error used
in the global factorization. No uniform aggregate error is assumed. -/
theorem averaged_row_error (F : List (SourceContour A h)) (r m M W K : ℕ)
    (hr : 6 ≤ r) (hm : 0 < m) (hmM : m ≤ M) (hK : K ≤ 52 * r ^ 4 * W ^ 2)
    (hperturb : ∀ C ∈ F,
      |(C.rows.length : ℚ) - (((r : ℚ) - 2) * (M : ℚ) ^ 2 +
        ((r : ℚ) * ((r : ℚ) - 1) + 1) * (M : ℚ))| ≤
      10 * (r : ℚ) ^ 2 * (K : ℚ) * (M : ℚ)) :
    ∃ u : ℚ,
      ((sourceRows F).length : ℚ) =
        (F.length : ℚ) * (((r : ℚ) - 2) * (M : ℚ) ^ 2) * (1 + u) ∧
      |u| ≤ (2 * (r : ℚ) + 1040 * (r : ℚ) ^ 5 * (W : ℚ) ^ 2) / (m : ℚ) := by
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hM : (0 : ℚ) < M := by exact_mod_cast (lt_of_lt_of_le hm hmM)
  have hr2 : (0 : ℚ) < (r : ℚ) - 2 := by linarith only [hrQ]
  apply averaged_relative_error F _ _ (by positivity) (by positivity)
  intro C hC
  exact contour_relative_error (C.rows.length : ℚ) r m M W K hrQ hmQ
    (by exact_mod_cast hmM) (Nat.cast_nonneg K) (by exact_mod_cast hK) (hperturb C hC)

end CoefficientTwoPrecision.ContourAggregation

#print axioms CoefficientTwoPrecision.ContourAggregation.uniform_charge
#print axioms CoefficientTwoPrecision.ContourAggregation.connector_ratio
#print axioms CoefficientTwoPrecision.ContourAggregation.contour_relative_error
#print axioms CoefficientTwoPrecision.ContourAggregation.averaged_row_error
