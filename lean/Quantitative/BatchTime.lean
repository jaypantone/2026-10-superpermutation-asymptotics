import Quantitative.BatchPrefixes

/-!
# Batch-time arithmetic for the cyclic comparison

For ordered indices in M complete batches, modular neighbouring times
mean either the same or consecutive ordinary batches, or the first and
last batches. In the latter case shifting the first index into a second
copy of the schedule makes the comparison consecutive again.
-/

namespace CoefficientTwoPrecision.BatchTime

variable {M k : Nat}

theorem batches_length (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k)) :
    batches.flatten.length = batches.length * k := by
  induction batches with
  | nil => simp
  | cons order batches ih =>
    have horder := horders order (by simp)
    have hlength : order.length = k := by simpa only [List.length_finRange] using horder.length_eq
    have htail := ih (fun next hnext => horders next (by simp [hnext]))
    rw [List.flatten_cons, List.length_append, hlength, htail, List.length_cons, Nat.succ_mul]
    omega

theorem batch_time_lt (hk : 0 < k) (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (hnumber : batches.length = M) (n : Nat) (hn : n < batches.flatten.length) : n / k < M := by
  rw [batches_length batches horders, hnumber] at hn
  exact (Nat.div_lt_iff_lt_mul hk).mpr hn

theorem ordered_neighbor_times (hM : 3 ≤ M) (first last : Nat)
    (hfirst : first < M) (hlast : last < M) (horder : first ≤ last)
    (hnear : (last : ZMod M) - first = 0 ∨ (last : ZMod M) - first = 1 ∨
      (last : ZMod M) - first = -1) :
    last ≤ first + 1 ∨ (first = 0 ∧ last = M - 1) := by
  have hdiff : last - first < M := by omega
  have hcast : ((last - first : Nat) : ZMod M) = (last : ZMod M) - first := Nat.cast_sub horder
  simp only [← hcast] at hnear
  rcases hnear with hzero | hone | hminus
  · have hval := congrArg ZMod.val hzero
    rw [ZMod.val_natCast_of_lt hdiff, ZMod.val_zero] at hval
    left
    omega
  · have hval := congrArg ZMod.val hone
    rw [ZMod.val_natCast_of_lt hdiff, ZMod.val_one_eq_one_mod,
      Nat.mod_eq_of_lt (by omega : 1 < M)] at hval
    left
    omega
  · cases M with
    | zero => omega
    | succ modulus =>
      have hval := congrArg ZMod.val hminus
      rw [ZMod.val_natCast_of_lt hdiff, ZMod.val_neg_one] at hval
      right
      omega

theorem shifted_batch_div (hk : 0 < k) (M n : Nat) :
    (M * k + n) / k = M + n / k := by
  calc
    (M * k + n) / k = (n + M * k) / k := by rw [Nat.add_comm]
    _ = n / k + M := Nat.add_mul_div_right n M hk
    _ = M + n / k := Nat.add_comm _ _

end CoefficientTwoPrecision.BatchTime

#print axioms CoefficientTwoPrecision.BatchTime.ordered_neighbor_times
