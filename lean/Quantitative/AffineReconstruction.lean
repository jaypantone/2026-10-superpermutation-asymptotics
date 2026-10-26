import Quantitative.LinearCount

/-!
# Recovering one missing coordinate of a modular affine relation

The observed coordinates are already translated by the common unknown
translation. Because an affine relation has coefficient sum zero, this
translation does not change its equation. Once the missing coordinate is
reconstructed, the coordinate at the anchored zero cut recovers the
translation. This file proves the finite congruence count used in that
reconstruction, without any primality or distribution hypothesis.
-/

namespace CoefficientTwoPrecision.AffineReconstruction

open LinearCount

def completions (M k : Nat) (a : Fin k → Int) (observed : Fin k → Fin M)
    (missing : Fin k) : Finset (Fin k → Fin M) :=
  Finset.univ.filter (fun w =>
    (∀ i, i ≠ missing → w i = observed i) ∧
      Int.ModEq (M : Int) (∑ i, a i * (w i).val) 0)

theorem completions_card (M k : Nat) (hM : 0 < M)
    (a : Fin k → Int) (observed : Fin k → Fin M) (missing : Fin k)
    (ha : a missing ≠ 0) :
    (completions M k a observed missing).card ≤ (a missing).natAbs := by
  classical
  let R := restSum missing a (fun i => observed i.val)
  let T := Finset.univ.filter
    (fun x : Fin M => Int.ModEq (M : Int) (a missing * x.val) (-R))
  have hmap : Set.MapsTo (fun w : Fin k → Fin M => w missing)
      (completions M k a observed missing : Set (Fin k → Fin M)) (T : Set (Fin M)) := by
    intro w hw
    obtain ⟨hobserved, heq⟩ := (Finset.mem_filter.mp hw).2
    have hrest : (fun i : {i : Fin k // i ≠ missing} => w i.val) =
        (fun i => observed i.val) := by
      funext i
      exact hobserved i.val i.property
    rw [split_sum missing a w, hrest] at heq
    have h := heq.sub_right R
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [R, add_sub_cancel_right,
      zero_sub] using h⟩
  have hinj : ((completions M k a observed missing) : Set (Fin k → Fin M)).InjOn
      (fun w => w missing) := by
    intro w hw v hv hmissing
    funext i
    by_cases hi : i = missing
    · subst i; exact hmissing
    · exact ((Finset.mem_filter.mp hw).2.1 i hi).trans
        ((Finset.mem_filter.mp hv).2.1 i hi).symm
  exact (Finset.card_le_card_of_injOn _ hmap hinj).trans
    (FiniteFibers.fin_root_count M hM (a missing) (-R) ha)

/-- The physical-slot coefficients once the target sum slot is chosen.
Slot zero is the anchored cut, and all other nonsum slots are free cuts. -/
def frameWeight (d : Nat) (sumSlot slot : Fin (d + 2)) : Int :=
  if slot = 0 then (d : Int) - 1 else if slot = sumSlot then 1 else -1

theorem frameWeight_nonzero (d : Nat) (hd : 2 ≤ d)
    (sumSlot slot : Fin (d + 2)) : frameWeight d sumSlot slot ≠ 0 := by
  have hdI : (2 : Int) ≤ d := by exact_mod_cast hd
  simp only [frameWeight]
  split_ifs <;> omega

theorem frameWeight_abs_sum (d : Nat) (hd : 2 ≤ d) (sumSlot : Fin (d + 2)) :
    (∑ slot, (frameWeight d sumSlot slot).natAbs) = 2 * d := by
  have hdI : (2 : Int) ≤ d := by exact_mod_cast hd
  have hterm (slot : Fin (d + 2)) : (frameWeight d sumSlot slot).natAbs =
      1 + (if slot = 0 then d - 2 else 0) := by
    simp only [frameWeight]
    split_ifs <;> omega
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul, Nat.mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  omega

/-- Summing all missing-slot reconstruction multiplicities costs at most
2d, uniformly over the chosen sum position and observed coordinates. -/
theorem all_completions_count (M d : Nat) (hM : 0 < M) (hd : 2 ≤ d)
    (sumSlot : Fin (d + 2)) (observed : Fin (d + 2) → Fin M) :
    (∑ missing, (completions M (d + 2) (frameWeight d sumSlot) observed missing).card) ≤
      2 * d := by
  calc
    ∑ missing, (completions M (d + 2) (frameWeight d sumSlot) observed missing).card ≤
        ∑ missing, (frameWeight d sumSlot missing).natAbs := by
      apply Finset.sum_le_sum
      intro missing _
      exact completions_card M (d + 2) hM _ observed missing
        (frameWeight_nonzero d hd sumSlot missing)
    _ = 2 * d := frameWeight_abs_sum d hd sumSlot

end CoefficientTwoPrecision.AffineReconstruction

#print axioms CoefficientTwoPrecision.AffineReconstruction.completions_card
#print axioms CoefficientTwoPrecision.AffineReconstruction.all_completions_count
