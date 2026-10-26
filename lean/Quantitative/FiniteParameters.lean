import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer size conditions for the finite transfer

This file proves only inequalities between the explicit parameters. It does
not assume or assert the existence of a source family or a covering word.
In particular, the width bounds in `polynomial_threshold_conditions` still
have to be supplied by the geometric parameter construction.
-/

namespace CoefficientTwoPrecision

/-- For a positive integer `n`, this is the least integer `ell` such that
`n < 2 ^ ell`. Defining it with `Nat.log` uses integer arithmetic only. -/
def binaryLength (n : ℕ) : ℕ := Nat.log 2 n + 1

theorem binaryLength_bounds (n : ℕ) (hn : 0 < n) :
    2 ^ (binaryLength n - 1) ≤ n ∧ n < 2 ^ binaryLength n := by
  constructor
  · simpa [binaryLength] using Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  · simpa [binaryLength, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n)

theorem binaryLength_ge_seven (n : ℕ) (hn : 64 ≤ n) :
    7 ≤ binaryLength n := by
  have hpow : 2 ^ 6 ≤ n := by norm_num; exact hn
  have hlog : 6 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hpow
  dsimp [binaryLength]
  omega

/-- The elementary estimate used for the binary-length bound, with its
smallest needed case kept explicit. -/
theorem square_le_two_pow_pred (ell : ℕ) (hell : 7 ≤ ell) :
    ell ^ 2 ≤ 2 ^ (ell - 1) := by
  have shifted : ∀ k : ℕ, (k + 7) ^ 2 ≤ 2 ^ (k + 6) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hstep : (k + 1 + 7) ^ 2 ≤ 2 * (k + 7) ^ 2 := by
        have heq : 2 * (k + 7) ^ 2 =
            (k + 1 + 7) ^ 2 + (k ^ 2 + 12 * k + 34) := by ring
        omega
      calc
        (k + 1 + 7) ^ 2 ≤ 2 * (k + 7) ^ 2 := hstep
        _ ≤ 2 * 2 ^ (k + 6) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 6) * 2 := Nat.mul_comm _ _
        _ = 2 ^ ((k + 6) + 1) := (pow_succ 2 (k + 6)).symm
        _ = 2 ^ (k + 1 + 6) := by congr 1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ell = k + 7 := ⟨ell - 7, by omega⟩
  subst ell
  have he : k + 7 - 1 = k + 6 := by omega
  simpa only [he] using shifted k

theorem binaryLength_square_le (n : ℕ) (hn : 64 ≤ n) :
    binaryLength n ^ 2 ≤ n := by
  exact (square_le_two_pow_pred _ (binaryLength_ge_seven n hn)).trans
    (binaryLength_bounds n (by omega)).1

/-- Natural-number form of the room estimate. Multiplication by `2*r`
avoids division and can later be cast to the rational inequality. -/
theorem room_of_primitive_threshold (r W E n : ℕ) (hr : 6 ≤ r)
    (hW : r + 3 ≤ W) (hWE : W ≤ E) (hE : 2592 * r ≤ E)
    (hn : 8 * r * E ≤ n) :
    96 * r ^ 2 ≤ n ∧
      2 * r * (r + W + (3 + 36 * binaryLength n)) ≤ n := by
  have hmulE := Nat.mul_le_mul_left (8 * r) hE
  have hsquare : (144 * r) ^ 2 ≤ n := by nlinarith only [hmulE, hn]
  have hrpow : 1 ≤ r ^ 2 := Nat.one_le_pow 2 r (by omega)
  have hn64 : 64 ≤ n := by nlinarith only [hrpow, hsquare]
  have hell := binaryLength_square_le n hn64
  have hcross : 144 * r * binaryLength n ≤ n := by
    rcases le_total (binaryLength n) (144 * r) with h | h
    · have hm := Nat.mul_le_mul_left (144 * r) h
      nlinarith only [hm, hsquare]
    · have hm := Nat.mul_le_mul_right (binaryLength n) h
      nlinarith only [hm, hell]
  have hwidth : 4 * r * (r + W + 3) ≤ n := by
    have hsum : r + W + 3 ≤ 2 * W := by omega
    have hmulW := Nat.mul_le_mul_left (4 * r) hsum
    have hmulWE := Nat.mul_le_mul_left (8 * r) hWE
    nlinarith only [hmulW, hmulWE, hn]
  constructor
  · nlinarith only [hsquare]
  · nlinarith only [hwidth, hcross]

/-- The error numerator in the uniform source-family estimates. -/
def errorNumerator (r W : ℕ) : ℕ := 10 ^ 12 * r ^ 22 * W ^ 4

/-- A single absolute integer constant for the requested exponent 61. -/
def transferConstant : ℕ := 8 * 10 ^ 12 * 352 ^ 4

theorem errorNumerator_ge_width (r W : ℕ) (hr : 1 ≤ r) :
    W ≤ errorNumerator r W := by
  have hrpow : 1 ≤ r ^ 22 := Nat.one_le_pow 22 r (by omega)
  have hcoeff : 1 ≤ 10 ^ 12 * r ^ 22 := by nlinarith only [hrpow]
  have hm := Nat.mul_le_mul_right (W ^ 4) hcoeff
  calc
    W ≤ W ^ 4 := Nat.le_pow (by decide : 0 < 4)
    _ ≤ errorNumerator r W := by simpa [errorNumerator] using hm

theorem errorNumerator_ge_linear (r W : ℕ) (hW : 1 ≤ W) :
    2592 * r ≤ errorNumerator r W := by
  have hrpow : r ≤ r ^ 22 := Nat.le_pow (by decide : 0 < 22)
  have hWpow : 1 ≤ W ^ 4 := Nat.one_le_pow 4 W (by omega)
  have hlinear : 2592 * r ≤ 10 ^ 12 * r ^ 22 := by nlinarith only [hrpow]
  have hm := Nat.mul_le_mul_left (10 ^ 12 * r ^ 22) hWpow
  calc
    2592 * r ≤ 10 ^ 12 * r ^ 22 := hlinear
    _ ≤ errorNumerator r W := by simpa [errorNumerator] using hm

theorem errorNumerator_upper (r W : ℕ) (hW : W ≤ 352 * r ^ 9) :
    errorNumerator r W ≤ (10 ^ 12 * 352 ^ 4) * r ^ 58 := by
  have hWpow : W ^ 4 ≤ (352 * r ^ 9) ^ 4 := Nat.pow_le_pow_left hW 4
  calc
    errorNumerator r W = 10 ^ 12 * r ^ 22 * W ^ 4 := rfl
    _ ≤ 10 ^ 12 * r ^ 22 * (352 * r ^ 9) ^ 4 :=
      Nat.mul_le_mul_left _ hWpow
    _ = (10 ^ 12 * 352 ^ 4) * r ^ 58 := by ring

theorem primitive_threshold_le_polynomial (r W : ℕ) (hr : 1 ≤ r)
    (hW : W ≤ 352 * r ^ 9) :
    8 * r * errorNumerator r W ≤ transferConstant * r ^ 61 := by
  calc
    8 * r * errorNumerator r W
        ≤ 8 * r * ((10 ^ 12 * 352 ^ 4) * r ^ 58) :=
      Nat.mul_le_mul_left _ (errorNumerator_upper r W hW)
    _ = transferConstant * r ^ 59 := by unfold transferConstant; ring
    _ ≤ transferConstant * r ^ 61 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by decide : 59 ≤ 61))

/-- The complete integer size requirements of the rational transfer follow
from the explicit polynomial threshold and the geometric width bounds. -/
theorem polynomial_threshold_conditions (r W n : ℕ) (hr : 6 ≤ r)
    (hWlower : r ^ 2 ≤ W) (hWupper : W ≤ 352 * r ^ 9)
    (hn : transferConstant * r ^ 61 ≤ n) :
    8 * r * errorNumerator r W ≤ n ∧
      96 * r ^ 2 ≤ n ∧
      2 * r * (r + W + (3 + 36 * binaryLength n)) ≤ n := by
  have hrpos : 1 ≤ r := by omega
  have hrpow : 1 ≤ r ^ 2 := Nat.one_le_pow 2 r (by omega)
  have hWpos : 1 ≤ W := hrpow.trans hWlower
  have hmul := Nat.mul_le_mul_left r hr
  have hroomW : r + 3 ≤ W := by nlinarith only [hr, hmul, hWlower]
  have hprimitive : 8 * r * errorNumerator r W ≤ n :=
    (primitive_threshold_le_polynomial r W hrpos hWupper).trans hn
  exact ⟨hprimitive,
    room_of_primitive_threshold r W (errorNumerator r W) n hr hroomW
      (errorNumerator_ge_width r W hrpos) (errorNumerator_ge_linear r W hWpos)
      hprimitive⟩

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.binaryLength_square_le
#print axioms CoefficientTwoPrecision.room_of_primitive_threshold
#print axioms CoefficientTwoPrecision.polynomial_threshold_conditions
