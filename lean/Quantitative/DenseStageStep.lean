import Quantitative.CountNormalization
import SuperpermutationUpperBound43586371.UniR.RRate8

/-!
# The actual dense family advances an arbitrary existing Stage

The family is the original `UniR.rFam`, constructed by `Uniform.famS`
from the proved `rData_ok` and `rData_safe` certificates. We use the
original `Stage.advance` directly. Thus the dense tail starts from the
actual preceding Stage, with its existing rows, circles, and pending list;
it is not restarted from the no-seed sequence used in the older rate proof.

The final theorem returns an actual next Stage and the three normalized
inequalities used by the dense-tail transfer. The only frame hypotheses
are the ordinary alphabet/fresh-letter conditions required by the original
constructor.
-/

namespace CoefficientTwoPrecision.DenseStageStep

open SuperpermutationUpperBound SuperpermutationUpperBound43586371
open SuperpermutationUpperBound43586371.Uniform
open SuperpermutationUpperBound43586371.UniR
open SourceUniverse

theorem rising_three (a : ℕ) : risingCount a 3 = a * ((a + 1) * (a + 2)) := by
  simp only [risingCount, Nat.add_zero, Nat.one_mul]
  ring

private theorem dense_count_bounds (a Q c P : ℕ) (ha : 49 ≤ a) :
    let D := risingCount a 3
    let Qnext := risingCount (a + 1) 3 * Q + (a + 3) * P * chargeR a
    let cnext := D * c + P * ((a + 2) * ncycR a)
    let Pnext := P * (D - rowsR a)
    let p := (P : ℚ) / ((a - 1).factorial : ℚ)
    let pnext := (Pnext : ℚ) / ((a + 2).factorial : ℚ)
    let X := (Q : ℚ) / (a.factorial : ℚ) + (c : ℚ) / ((a - 1).factorial : ℚ)
    let Xnext := (Qnext : ℚ) / ((a + 3).factorial : ℚ) + (cnext : ℚ) / ((a + 2).factorial : ℚ)
    pnext ≤ (3 / 4) * p ∧
      Xnext - X ≤ (8 / (a : ℚ)) * (p - pnext) ∧
      (cnext : ℚ) / ((a + 2).factorial : ℚ) - (c : ℚ) / ((a - 1).factorial : ℚ) ≤
        8 * p / ((a : ℚ) * ((a : ℚ) + 1)) := by
  dsimp only
  let D := risingCount a 3
  let Qnext := risingCount (a + 1) 3 * Q + (a + 3) * P * chargeR a
  let cnext := D * c + P * ((a + 2) * ncycR a)
  let Pnext := P * (D - rowsR a)
  let p : ℚ := (P : ℚ) / ((a - 1).factorial : ℚ)
  let pnext : ℚ := (Pnext : ℚ) / ((a + 2).factorial : ℚ)
  let X : ℚ := (Q : ℚ) / (a.factorial : ℚ) + (c : ℚ) / ((a - 1).factorial : ℚ)
  let Xnext : ℚ := (Qnext : ℚ) / ((a + 3).factorial : ℚ) +
    (cnext : ℚ) / ((a + 2).factorial : ℚ)
  change pnext ≤ (3 / 4) * p ∧ Xnext - X ≤ (8 / (a : ℚ)) * (p - pnext) ∧ _
  have ha0 : 0 < a := by omega
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha0
  have hD : (0 : ℚ) < D := by exact_mod_cast risingCount_pos a 3 ha0
  have hB : rowsR a ≤ D := by simpa only [D, rising_three] using rowsR_le a (by omega)
  have hindex : a + 3 - 1 = a + 2 := by omega
  have hp0 : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpending : pnext = p * (1 - (rowsR a : ℚ) / (D : ℚ)) := by
    simpa only [pnext, Pnext, p, D, hindex] using
      normalized_pending_update a 3 P (rowsR a) ha0 hB
  have htotal : Xnext = X + p *
      (((chargeR a : ℚ) + ((a : ℚ) + 2) * (ncycR a : ℚ)) / (D : ℚ)) := by
    have h := normalized_total_update a 3 Q c P (chargeR a) ((a + 2) * ncycR a) ha0
    simpa only [Xnext, X, Qnext, cnext, p, D, hindex,
      Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using h
  have hcircle : (cnext : ℚ) / ((a + 2).factorial : ℚ) =
      (c : ℚ) / ((a - 1).factorial : ℚ) +
        p * ((((a : ℚ) + 2) * (ncycR a : ℚ)) / (D : ℚ)) := by
    simpa only [cnext, p, D, hindex, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
      normalized_circle_update a 3 c P ((a + 2) * ncycR a) ha0
  have hquarter : (D : ℚ) ≤ 4 * (rowsR a : ℚ) := by
    have h := rows_quarter a ha
    rw [← rising_three] at h
    exact_mod_cast h
  have hcost : ((chargeR a : ℚ) + ((a : ℚ) + 2) * (ncycR a : ℚ)) * (a : ℚ) ≤
      8 * (rowsR a : ℚ) := by exact_mod_cast cost_le8 a ha
  have hnu : (ncycR a : ℚ) ≤ 8 := by exact_mod_cast ncycR_le a
  have hfquarter : (1 / 4 : ℚ) ≤ (rowsR a : ℚ) / (D : ℚ) := by
    apply (le_div_iff₀ hD).2
    linarith only [hquarter]
  have hpdrop : p - pnext = p * (rowsR a : ℚ) / (D : ℚ) := by
    rw [hpending]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hpending]
    have h := mul_le_mul_of_nonneg_left
      (show (1 : ℚ) - (rowsR a : ℚ) / (D : ℚ) ≤ 3 / 4 by linarith only [hfquarter]) hp0
    simpa only [mul_comm p] using h
  · have hlocal : (chargeR a : ℚ) + ((a : ℚ) + 2) * (ncycR a : ℚ) ≤
        (8 / (a : ℚ)) * (rowsR a : ℚ) := by
      calc
        (chargeR a : ℚ) + ((a : ℚ) + 2) * (ncycR a : ℚ) ≤
            8 * (rowsR a : ℚ) / (a : ℚ) := (le_div_iff₀ haQ).2 hcost
        _ = (8 / (a : ℚ)) * (rowsR a : ℚ) := by ring
    calc
      Xnext - X = p *
          ((chargeR a : ℚ) + ((a : ℚ) + 2) * (ncycR a : ℚ)) / (D : ℚ) := by
        rw [htotal]
        ring
      _ ≤ p * ((8 / (a : ℚ)) * (rowsR a : ℚ)) / (D : ℚ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlocal hp0) hD.le
      _ = (8 / (a : ℚ)) * (p - pnext) := by rw [hpdrop]; ring
  · have hDvalue : (D : ℚ) = (a : ℚ) * (((a : ℚ) + 1) * ((a : ℚ) + 2)) := by
      exact_mod_cast rising_three a
    have ha1 : (0 : ℚ) < (a : ℚ) + 1 := by linarith only [haQ]
    have ha2 : (0 : ℚ) < (a : ℚ) + 2 := by linarith only [haQ]
    change (cnext : ℚ) / ((a + 2).factorial : ℚ) -
      (c : ℚ) / ((a - 1).factorial : ℚ) ≤ _
    calc
      (cnext : ℚ) / ((a + 2).factorial : ℚ) - (c : ℚ) / ((a - 1).factorial : ℚ) =
          p * (ncycR a : ℚ) / ((a : ℚ) * ((a : ℚ) + 1)) := by
        rw [hcircle, hDvalue]
        field_simp [ne_of_gt haQ, ne_of_gt ha1, ne_of_gt ha2] <;> ring
      _ ≤ 8 * p / ((a : ℚ) * ((a : ℚ) + 1)) := by
        apply div_le_div_of_nonneg_right _ (mul_nonneg haQ.le ha1.le)
        have h := mul_le_mul_of_nonneg_left hnu hp0
        simpa only [mul_comm p 8] using h

/-- Apply the original dense family to any actual preceding Stage. All
three tail inequalities concern the returned Stage's exact counts. -/
theorem dense_step {A0 : List ℕ} {z : ℕ} {comps : List (List (Row ℕ))}
    {circles pending : List (List ℕ)} {R Q c P : ℕ}
    (S : Stage A0 z comps circles pending R Q c P)
    (F : Frame) (hF : F.OK) (hbase : F.d0.Perm A0) (ht1 : F.t1 = z)
    (ha : 49 ≤ A0.length) :
    ∃ nextComps nextCircles nextPending Rnext Qnext cnext Pnext,
      Stage (F.t3 :: F.t2 :: z :: A0) F.z nextComps nextCircles nextPending
        Rnext Qnext cnext Pnext ∧
      (Pnext : ℚ) / ((A0.length + 2).factorial : ℚ) ≤
        (3 / 4) * ((P : ℚ) / ((A0.length - 1).factorial : ℚ)) ∧
      ((Qnext : ℚ) / ((A0.length + 3).factorial : ℚ) +
          (cnext : ℚ) / ((A0.length + 2).factorial : ℚ)) -
        ((Q : ℚ) / (A0.length.factorial : ℚ) + (c : ℚ) / ((A0.length - 1).factorial : ℚ)) ≤
        (8 / (A0.length : ℚ)) *
          ((P : ℚ) / ((A0.length - 1).factorial : ℚ) - (Pnext : ℚ) / ((A0.length + 2).factorial : ℚ)) ∧
      (cnext : ℚ) / ((A0.length + 2).factorial : ℚ) -
          (c : ℚ) / ((A0.length - 1).factorial : ℚ) ≤
        8 * ((P : ℚ) / ((A0.length - 1).factorial : ℚ)) /
          ((A0.length : ℚ) * ((A0.length : ℚ) + 1)) ∧
      (R + A0.length * P = A0.length.factorial →
        Rnext + (A0.length + 3) * Pnext = (A0.length + 3).factorial) := by
  have hlen := hbase.length_eq
  have hm : 7 ≤ F.d0.length := by omega
  let K := rFam F hF hm
  have hrows : K.nrows = rowsR A0.length := by simp only [K, rFam, famS, rData, hlen]
  have hcharge : K.nq = chargeR A0.length := by simp only [K, rFam, famS, rData, hlen]
  have hcircles : K.ncirc = (A0.length + 2) * ncycR A0.length := by
    simp only [K, rFam, famS, rData, Frame.h, hlen]
  have hpending : K.nd = risingCount A0.length 3 - rowsR A0.length := by
    simp only [K, rFam, famS, rData, hlen, rising_three]
  let Rnext := risingCount (A0.length + 1) 3 * R +
    (A0.length + 3) * P * rowsR A0.length
  let Qnext := risingCount (A0.length + 1) 3 * Q +
    (A0.length + 3) * P * chargeR A0.length
  let cnext := risingCount A0.length 3 * c + P * ((A0.length + 2) * ncycR A0.length)
  let Pnext := P * (risingCount A0.length 3 - rowsR A0.length)
  have E := S.advance K hbase ht1
  have Eactual : Stage (F.t3 :: F.t2 :: z :: A0) F.z
      (Stage.advComps comps pending K A0.length) (Stage.advCircles circles pending K)
      (Stage.advPending pending K) Rnext Qnext cnext Pnext := by
    apply E.congr
    · rw [hrows]
      dsimp only [Rnext]
      rw [rising_three]
      ring
    · rw [hcharge]
      dsimp only [Qnext]
      rw [rising_three]
      ring
    · rw [hcircles]
      dsimp only [cnext]
      rw [rising_three]
      ring
    · rw [hpending]
  refine ⟨_, _, _, Rnext, Qnext, cnext, Pnext, Eactual, ?_⟩
  obtain ⟨hp, hX, hz⟩ := dense_count_bounds A0.length Q c P ha
  refine ⟨hp, hX, hz, ?_⟩
  intro hmass
  have hB : rowsR A0.length ≤ risingCount A0.length 3 := by
    simpa only [rising_three] using rowsR_le A0.length (by omega)
  exact integer_update_mass_factorial A0.length 3 R P (rowsR A0.length)
    (by omega) hB hmass

end CoefficientTwoPrecision.DenseStageStep

#print axioms CoefficientTwoPrecision.DenseStageStep.dense_step
