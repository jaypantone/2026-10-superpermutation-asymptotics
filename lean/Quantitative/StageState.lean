import Quantitative.StageEndpoints
import Quantitative.StageNormalization
import Quantitative.DenseStageStep
import SuperpermutationUpperBound43586371.Uniform.Iterate

/-!
# Actual stages with canonical letters and an exact mass identity

`BuiltStage m` stores the lists in an actual Stage on `m` ordinary letters.
It also records the complete alphabet and the exact row-plus-pending mass.
The functions below construct new lists using the existing Stage operations;
the normalized identities are consequences of their exact integer counts.
-/

namespace CoefficientTwoPrecision.StageState

open SuperpermutationUpperBound SuperpermutationUpperBound43586371
open SuperpermutationUpperBound43586371.Uniform
open SourceUniverse StageExtension

/-- The fresh ordinary letters, in the order required by `empty_many`. -/
def freshExtra (m : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => (m + k + 3) :: freshExtra m k

@[simp] theorem freshExtra_length (m k : ℕ) : (freshExtra m k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [freshExtra, List.length_cons, ih]

private theorem letOK_one {A0 : List ℕ} {z : ℕ} (h : LetOK A0 z) :
    LetOK (z :: A0) (A0.length + 3) := by
  unfold LetOK
  rw [show (z :: A0).length + 3 = (A0.length + 3) + 1 by simp,
    List.range_succ]
  refine List.Perm.trans ?_ (h.append_right _)
  rw [← Multiset.coe_eq_coe]
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, List.cons_append, List.nil_append]
  simp only [← Multiset.singleton_add]
  abel

theorem letOK_fresh {A0 : List ℕ} {z m : ℕ} (h : LetOK A0 z)
    (hm : A0.length = m) (k : ℕ) :
    LetOK (freshExtra m k ++ z :: A0) (m + k + 3) := by
  induction k with
  | zero => simpa only [freshExtra, List.nil_append, Nat.add_zero, hm] using letOK_one h
  | succ k ih =>
    have hn := letOK_one ih
    simpa only [freshExtra, List.cons_append, List.length_append,
      freshExtra_length, List.length_cons, hm, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hn

/-- A stage is a concrete finite collection of rows, circles, and pending
charts, together with its original structural certificate. -/
structure BuiltStage (m : ℕ) where
  A0 : List ℕ
  z : ℕ
  comps : List (List (Row ℕ))
  circles : List (List ℕ)
  pending : List (List ℕ)
  R : ℕ
  Q : ℕ
  c : ℕ
  P : ℕ
  valid : Stage A0 z comps circles pending R Q c P
  size : A0.length = m
  labels : LetOK A0 z
  mass : R + m * P = m.factorial

def BuiltStage.p {m : ℕ} (S : BuiltStage m) : ℚ := (S.P : ℚ) / ((m - 1).factorial : ℚ)
def BuiltStage.y {m : ℕ} (S : BuiltStage m) : ℚ := (S.Q : ℚ) / (m.factorial : ℚ)
def BuiltStage.zmass {m : ℕ} (S : BuiltStage m) : ℚ := (S.c : ℚ) / ((m - 1).factorial : ℚ)
def BuiltStage.X {m : ℕ} (S : BuiltStage m) : ℚ := S.y + S.zmass

@[simp] theorem BuiltStage.p_nonneg {m : ℕ} (S : BuiltStage m) : 0 ≤ S.p := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
@[simp] theorem BuiltStage.zmass_nonneg {m : ℕ} (S : BuiltStage m) : 0 ≤ S.zmass := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
@[simp] theorem BuiltStage.X_nonneg {m : ℕ} (S : BuiltStage m) : 0 ≤ S.X := by
  exact add_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) S.zmass_nonneg

def BuiltStage.reindex {m k : ℕ} (S : BuiltStage m) (h : m = k) : BuiltStage k := h ▸ S
@[simp] theorem BuiltStage.reindex_p {m k : ℕ} (S : BuiltStage m) (h : m = k) :
    (S.reindex h).p = S.p := by subst k; rfl
@[simp] theorem BuiltStage.reindex_X {m k : ℕ} (S : BuiltStage m) (h : m = k) :
    (S.reindex h).X = S.X := by subst k; rfl
@[simp] theorem BuiltStage.reindex_zmass {m k : ℕ} (S : BuiltStage m) (h : m = k) :
    (S.reindex h).zmass = S.zmass := by subst k; rfl

/-- The no-seed initial stage is obtained from `initial_padded`, with the
canonical complete alphabet. Its pending mass is exactly one. -/
theorem initial (m : ℕ) (hm : 9 ≤ m) :
    ∃ S : BuiltStage m, S.p = 1 ∧ S.X = 0 ∧ S.zmass = 0 := by
  let base : List ℕ := [8, 7, 6, 5, 4, 2, 0, 1]
  have hbase : LetOK base 3 := by unfold LetOK base; decide
  let extra := freshExtra 8 (m - 9) ++ [3, 8, 7, 6, 5, 4]
  have hlen : (extra ++ [2, 0, 1]).length = m := by
    simp only [extra, List.length_append, freshExtra_length, List.length_cons, List.length_nil]
    omega
  have hL : LetOK (extra ++ [2, 0, 1]) (8 + (m - 9) + 3) := by
    simpa only [extra, base, List.append_assoc, List.cons_append, List.nil_append] using
      letOK_fresh hbase (by rfl) (m - 9)
  have S := StageEndpoints.initial_padded extra (8 + (m - 9) + 3)
    hL.nodup hL.nine hL.ten
  have hpindex : extra.length + 2 = m - 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  let T : BuiltStage m := {
    A0 := extra ++ [2, 0, 1], z := 8 + (m - 9) + 3
    comps := [], circles := [], pending := sourceUniverse (extra ++ [2]) [0, 1]
    R := 0, Q := 0, c := 0, P := (extra.length + 2).factorial
    valid := S, size := hlen, labels := hL
    mass := by simpa only [Nat.zero_add, hpindex] using Nat.mul_factorial_pred (by omega : m ≠ 0) }
  refine ⟨T, ?_, ?_, ?_⟩
  · change ((extra.length + 2).factorial : ℚ) / ((m - 1).factorial : ℚ) = 1
    rw [hpindex, div_self]
    exact_mod_cast Nat.factorial_ne_zero (m - 1)
  · simp only [T, BuiltStage.X, BuiltStage.y, BuiltStage.zmass,
      Nat.cast_zero, zero_div, zero_add]
  · simp only [T, BuiltStage.zmass, Nat.cast_zero, zero_div]

/-- The canonical actual block above a stage. -/
abbrev Block {m : ℕ} (S : BuiltStage m) (W : ℕ) :=
  WidthBlockFamily S.A0 (freshExtra m (W - 1) ++ [S.z]) (m + (W - 1) + 3)

/-- Apply an arbitrary-width family to the actual preceding stage. -/
def advance {m W : ℕ} (S : BuiltStage m) (hW : 0 < W) (K : Block S W) :
    BuiltStage (m + W) := by
  let extra := freshExtra m (W - 1)
  let next := m + (W - 1) + 3
  have hL := letOK_fresh S.labels S.size (W - 1)
  have hlen : (extra ++ S.z :: S.A0).length = m + W := by
    simp only [extra, List.length_append, freshExtra_length, List.length_cons, S.size]
    omega
  have hwidth : extra.length + 1 = W := by simp only [extra, freshExtra_length]; omega
  have hm : 0 < m := by have := S.valid.two; rw [S.size] at this; omega
  have hB : K.sourceRows ≤ risingCount m W := by
    simpa only [List.length_append, freshExtra_length, List.length_singleton, S.size,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hW))] using K.sourceBound
  exact {
    A0 := extra ++ S.z :: S.A0, z := next
    comps := transportSequence S.comps S.A0.length (next :: extra) ++ S.pending.flatMap K.comps
    circles := circleSequence S.circles (next :: extra) ++ S.pending.flatMap K.circles
    pending := S.pending.flatMap K.remaining
    R := risingCount (m + 1) W * S.R + (m + W) * S.P * K.sourceRows
    Q := risingCount (m + 1) W * S.Q + (m + W) * S.P * K.sourceCharge
    c := risingCount m W * S.c + S.P * K.advancedCircles
    P := S.P * (risingCount m W - K.sourceRows)
    valid := by
      simpa only [S.size, hwidth, Nat.add_assoc] using
        advance_width S.valid extra next hL.nodup hL.nine hL.ten K
    size := hlen, labels := hL
    mass := integer_update_mass_factorial m W S.R S.P K.sourceRows hm hB S.mass }

@[simp] theorem advance_p {m W : ℕ} (S : BuiltStage m) (hW : 0 < W) (K : Block S W) :
    (advance S hW K).p = S.p * (1 - (K.sourceRows : ℚ) / (risingCount m W : ℚ)) := by
  have hm : 0 < m := by have := S.valid.two; rw [S.size] at this; omega
  have hB : K.sourceRows ≤ risingCount m W := by
    simpa only [List.length_append, freshExtra_length, List.length_singleton, S.size,
      Nat.sub_add_cancel (show 1 ≤ W by omega)] using K.sourceBound
  exact normalized_pending_update m W S.P K.sourceRows hm hB

@[simp] theorem advance_X {m W : ℕ} (S : BuiltStage m) (hW : 0 < W) (K : Block S W) :
    (advance S hW K).X = S.X + S.p *
      (((K.sourceCharge : ℚ) + (K.advancedCircles : ℚ)) / (risingCount m W : ℚ)) := by
  have hm : 0 < m := by have := S.valid.two; rw [S.size] at this; omega
  exact normalized_total_update m W S.Q S.c S.P K.sourceCharge K.advancedCircles hm

@[simp] theorem advance_zmass {m W : ℕ} (S : BuiltStage m) (hW : 0 < W) (K : Block S W) :
    (advance S hW K).zmass = S.zmass + S.p *
      ((K.advancedCircles : ℚ) / (risingCount m W : ℚ)) := by
  have hm : 0 < m := by have := S.valid.two; rw [S.size] at this; omega
  exact normalized_circle_update m W S.c S.P K.advancedCircles hm

/-- Empty padding preserves all three normalized masses. -/
theorem empty_to {m : ℕ} (S : BuiltStage m) (k : ℕ) :
    ∃ T : BuiltStage (m + k), T.p = S.p ∧ T.X = S.X ∧ T.zmass = S.zmass := by
  cases k with
  | zero => exact ⟨S, rfl, rfl, rfl⟩
  | succ k =>
    let extra := freshExtra m k
    let next := m + k + 3
    have hL := letOK_fresh S.labels S.size k
    have hm : 0 < m := by have := S.valid.two; rw [S.size] at this; omega
    have hwidth : extra.length + 1 = k + 1 := by simp only [extra, freshExtra_length]
    have hlen : (extra ++ S.z :: S.A0).length = m + (k + 1) := by
      simp only [extra, List.length_append, freshExtra_length, List.length_cons, S.size] <;> omega
    let T : BuiltStage (m + (k + 1)) := {
      A0 := extra ++ S.z :: S.A0, z := next
      comps := transportSequence S.comps S.A0.length (next :: extra)
      circles := circleSequence S.circles (next :: extra)
      pending := pendingUniverse (extra ++ [S.z]) S.pending
      R := risingCount (m + 1) (k + 1) * S.R
      Q := risingCount (m + 1) (k + 1) * S.Q
      c := risingCount m (k + 1) * S.c
      P := risingCount m (k + 1) * S.P
      valid := by simpa only [S.size, hwidth] using
        empty_many S.valid extra next hL.nodup hL.nine hL.ten
      size := hlen, labels := hL
      mass := by simpa only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero,
          Nat.mul_comm S.P] using
        integer_update_mass_factorial m (k + 1) S.R S.P 0 hm (Nat.zero_le _) S.mass }
    refine ⟨T, ?_, ?_, ?_⟩
    · simpa only [T, BuiltStage.p, Nat.sub_zero, Nat.cast_zero, zero_div,
        sub_zero, mul_one, Nat.mul_comm S.P] using
        normalized_pending_update m (k + 1) S.P 0 hm (Nat.zero_le _)
    · simpa only [T, BuiltStage.X, BuiltStage.y, BuiltStage.zmass, BuiltStage.p,
        Nat.mul_zero, Nat.add_zero, Nat.cast_zero, zero_add, zero_div, mul_zero, add_zero] using
        normalized_total_update m (k + 1) S.Q S.c S.P 0 0 hm
    · simpa only [T, BuiltStage.zmass, BuiltStage.p, Nat.mul_zero, Nat.add_zero,
        Nat.cast_zero, zero_div, mul_zero, add_zero] using
        normalized_circle_update m (k + 1) S.c S.P 0 hm

/-- One dense step, using the original proved family and preserving mass. -/
theorem dense {m : ℕ} (S : BuiltStage m) (hm : 49 ≤ m) :
    ∃ T : BuiltStage (m + 3),
      T.p ≤ (3 / 4) * S.p ∧
      T.X - S.X ≤ (8 / (m : ℚ)) * (S.p - T.p) ∧
      T.zmass - S.zmass ≤ 8 * S.p / ((m : ℚ) * ((m : ℚ) + 1)) := by
  have ha : 49 ≤ S.A0.length := by rwa [S.size]
  obtain ⟨comps, circles, pending, R, Q, c, P, E, hp, hX, hz, hmass⟩ :=
    DenseStageStep.dense_step S.valid (frameAt S.A0 S.z)
      (frameAt_ok S.labels (by omega)) (List.Perm.refl _) rfl ha
  let T : BuiltStage (m + 3) := {
    A0 := (S.A0.length + 4) :: (S.A0.length + 3) :: S.z :: S.A0
    z := S.A0.length + 5, comps := comps, circles := circles, pending := pending
    R := R, Q := Q, c := c, P := P
    valid := E
    size := by simp only [List.length_cons, S.size]
    labels := S.labels.next
    mass := by simpa only [S.size] using hmass (by simpa only [S.size] using S.mass) }
  refine ⟨T, ?_, ?_, ?_⟩
  · simpa only [T, BuiltStage.p, S.size, show m + 3 - 1 = m + 2 by omega] using hp
  · simpa only [T, BuiltStage.X, BuiltStage.y, BuiltStage.zmass, BuiltStage.p,
      S.size, show m + 3 - 1 = m + 2 by omega] using hX
  · simpa only [T, BuiltStage.zmass, BuiltStage.p, S.size,
      show m + 3 - 1 = m + 2 by omega] using hz

end CoefficientTwoPrecision.StageState

#print axioms CoefficientTwoPrecision.StageState.initial
#print axioms CoefficientTwoPrecision.StageState.advance
#print axioms CoefficientTwoPrecision.StageState.advance_p
#print axioms CoefficientTwoPrecision.StageState.empty_to
#print axioms CoefficientTwoPrecision.StageState.dense
