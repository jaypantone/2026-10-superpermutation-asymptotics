import Quantitative.GuardEvents

/-!
# Active-slot coordinates and the second finite offset bound

An actual local slot is (q+t+phase) modulo m+G. Its quotient is zero or
one because q,t are residues and the phase is zero or one. Substituting
the original-cut coordinate gives an error between -2G and 1 modulo m.
Replacing the shared stationary coordinate in a foreign relation then
gives the primary-event bound C2=C1+(d-1)(2G+1).
-/

namespace CoefficientTwoPrecision.ActiveSlotEvents

open StationaryRelations StationaryCircle StationaryUpdate GuardCoordinates GuardPositions GuardEvents

theorem active_slot_offset (m G : Nat) (hm : 0 < m)
    (q t y : Fin (m + G)) (phase : Fin 2) (x : Fin m) (e : Nat) (he : e ≤ G)
    (hposition : y.val = x.val + e)
    (hy : y.val = (q.val + t.val + phase.val) % (m + G)) :
    ∃ error : Int, -(2 * (G : Int)) ≤ error ∧ error ≤ 1 ∧
      error.natAbs ≤ 2 * G + 1 ∧
      Int.ModEq (m : Int) x.val ((q.val : Int) + t.val + error) := by
  let total := q.val + t.val + phase.val
  let winding := total / (m + G)
  have hM : 0 < m + G := by omega
  have htotal : total < 2 * (m + G) := by
    have hq := q.isLt
    have ht := t.isLt
    have hp := phase.isLt
    dsimp [total]
    omega
  have hw : winding < 2 := (Nat.div_lt_iff_lt_mul hM).mpr (by simpa [Nat.mul_comm] using htotal)
  have hwG : winding * G ≤ G := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right G (by omega : winding ≤ 1)
  have hdiv := Nat.mod_add_div total (m + G)
  have hsumNat : x.val + e + (m + G) * winding = q.val + t.val + phase.val := by
    rw [← hposition, hy]
    exact hdiv
  have hsum : (x.val : Int) + e + ((m + G : Nat) : Int) * winding =
      (q.val : Int) + t.val + phase.val := by exact_mod_cast hsumNat
  let error : Int := (phase.val : Int) - e - (winding * G : Nat)
  have hlo : -(2 * (G : Int)) ≤ error := by dsimp [error]; omega
  have hhi : error ≤ 1 := by have hp := phase.isLt; dsimp [error]; omega
  refine ⟨error, hlo, hhi, by omega, ?_⟩
  apply Int.modEq_iff_dvd.mpr
  refine ⟨(winding : Int), ?_⟩
  dsimp [error]
  push_cast at hsum ⊢
  nlinarith only [hsum]

/-- The original cut used for an active slot is recovered from the actual
block decomposition of the guard background. -/
theorem rendered_active_slot {m G : Nat} {α : Type}
    (hm : 0 < m) (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (ho : Function.Injective old) (hg : Function.Injective guard)
    (hcross : ∀ j i, guard j ≠ old i)
    (q t y : Fin (m + G)) (phase : Fin 2)
    (hy : y.val = (q.val + t.val + phase.val) % (m + G)) :
    ∃ cut : Fin m, ∃ offset : Nat,
      offset < (block old guard cuts cut).length ∧
      y.val = blockStart old guard cuts cut + offset ∧
      ∃ error : Int, -(2 * (G : Int)) ≤ error ∧ error ≤ 1 ∧
        error.natAbs ≤ 2 * G + 1 ∧
        Int.ModEq (m : Int) cut.val ((q.val : Int) + t.val + error) := by
  have hlen : y.val < (render old guard cuts).length := by
    rw [render_length old guard cuts ho hg hcross]
    exact y.isLt
  obtain ⟨cut, offset, hoff, hp⟩ := position_has_cut old guard cuts y.val hlen
  obtain ⟨e, he, hpe⟩ := coordinate_offset old guard cuts ho hg hcross cut offset hoff
  exact ⟨cut, offset, hoff, hp, active_slot_offset m G hm q t y phase cut e he (hp.trans hpe) hy⟩

def primaryOffsetBound (d G : Nat) : Nat :=
  stationaryOffsetBound d G + (d - 1) * (2 * G + 1)

def remainingSum {d : Nat} (assignment : Assignment d) (shared : Fin (d + 2))
    (x : Fin (d + 2) → Int) : Int :=
  ∑ i, if i = shared then 0 else weight assignment i * x i

theorem split_shared {d : Nat} (assignment : Assignment d) (shared : Fin (d + 2))
    (x : Fin (d + 2) → Int) :
    (∑ i, weight assignment i * x i) =
      weight assignment shared * x shared + remainingSum assignment shared x := by
  calc
    (∑ i, weight assignment i * x i) =
        ∑ i, ((if i = shared then weight assignment shared * x shared else 0) +
          (if i = shared then 0 else weight assignment i * x i)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = shared
      · subst i; simp
      · simp [hi]
    _ = weight assignment shared * x shared + remainingSum assignment shared x := by
      simp [Finset.sum_add_distrib, remainingSum]

/-- Substitution at the actual shared control gives a member of the
bounded primary-event congruence catalogue. -/
theorem primary_relation {d : Nat} (m G : Nat) (hd : 2 ≤ d)
    (assignment : Assignment d) (shared : Fin (d + 2)) (x : Fin (d + 2) → Int)
    (q t error b : Int)
    (hforeign : Int.ModEq (m : Int) (∑ i, weight assignment i * x i) b)
    (hb : b.natAbs ≤ stationaryOffsetBound d G)
    (hshared : Int.ModEq (m : Int) (x shared) (q + t + error))
    (herror : error.natAbs ≤ 2 * G + 1) :
    ∃ b1 : Int, b1.natAbs ≤ primaryOffsetBound d G ∧
      Int.ModEq (m : Int)
        (weight assignment shared * (q + t) + remainingSum assignment shared x) b1 := by
  let a := weight assignment shared
  let b1 := b - a * error
  have hcoef : a.natAbs ≤ d - 1 := by
    dsimp [a]
    rw [weight_abs_formula hd]
    split_ifs <;> omega
  have hproduct : (a * error).natAbs ≤ (d - 1) * (2 * G + 1) := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hcoef herror
  have hb1 := Int.natAbs_sub_le b (a * error)
  refine ⟨b1, ?_, ?_⟩
  · dsimp [b1, primaryOffsetBound]
    omega
  · rw [split_shared] at hforeign
    have hsub := ((hshared.mul_left a).add_right (remainingSum assignment shared x)).symm.trans hforeign
    have h := hsub.sub_right (a * error)
    have hleft : a * (q + t + error) + remainingSum assignment shared x - a * error =
        a * (q + t) + remainingSum assignment shared x := by ring
    rw [hleft] at h
    exact h

end CoefficientTwoPrecision.ActiveSlotEvents

#print axioms CoefficientTwoPrecision.ActiveSlotEvents.active_slot_offset
#print axioms CoefficientTwoPrecision.ActiveSlotEvents.rendered_active_slot
#print axioms CoefficientTwoPrecision.ActiveSlotEvents.primary_relation
