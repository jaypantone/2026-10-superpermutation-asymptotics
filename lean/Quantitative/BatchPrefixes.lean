import Quantitative.CutPersistence

/-!
# Chronological batch phases of actual target-word prefixes

Every batch is a permutation of all stationary positions. At target-word
index n, each position has been updated floor(n/k) or floor(n/k)+1 times.
These exact bounds supply the binary phase representation of the actual
cut function. Between prefixes in the same or consecutive batches, each
position is updated at most twice.
-/

namespace CoefficientTwoPrecision.BatchPrefixes

open LiteralSchedule BatchSafety RobustMatching RobustSafety

variable {M k : Nat}

theorem prefix_count_bounds (hk : 0 < k) (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (n : Nat) (hn : n ≤ batches.flatten.length) (target : Fin k) :
    n / k ≤ (batches.flatten.take n).count target ∧
      (batches.flatten.take n).count target ≤ n / k + 1 := by
  induction batches generalizing n with
  | nil =>
    have hnzero : n = 0 := by simpa using hn
    subst n
    simp
  | cons order batches ih =>
    have horder := horders order (by simp)
    have hlength : order.length = k := by simpa only [List.length_finRange] using horder.length_eq
    have htail : ∀ next ∈ batches, next.Perm (List.finRange k) :=
      fun next hnext => horders next (by simp [hnext])
    have hcount : order.count target = 1 := by
      rw [horder.count_eq]
      exact List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange target)
    change n ≤ (order ++ batches.flatten).length at hn
    change n / k ≤ ((order ++ batches.flatten).take n).count target ∧
      ((order ++ batches.flatten).take n).count target ≤ n / k + 1
    by_cases hfirst : n < k
    · have hle : n ≤ order.length := by omega
      rw [List.take_append_of_le_length hle, Nat.div_eq_of_lt hfirst]
      refine ⟨Nat.zero_le _, ?_⟩
      exact List.nodup_iff_count_le_one.mp
        (List.Nodup.sublist (List.take_sublist _ _)
          (horder.nodup_iff.mpr (List.nodup_finRange k))) target
    · have hrest : n - k ≤ batches.flatten.length := by
        rw [List.length_append, hlength] at hn
        omega
      have hb := ih htail (n - k) hrest
      have hn' : n = order.length + (n - k) := by omega
      have hdiv : n / k = (n - k) / k + 1 := by
        conv_lhs => rw [hn', hlength]
        exact Nat.add_div_left _ hk
      rw [hn', List.take_length_add_append, List.count_append, hcount]
      rw [← hn', hdiv]
      omega

def prefixPhases (batches : List (List (Fin k))) (n : Nat) : Fin k → Bool :=
  fun target => decide ((batches.flatten.take n).count target = n / k + 1)

theorem prefix_count_phase (hk : 0 < k) (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (n : Nat) (hn : n ≤ batches.flatten.length) (target : Fin k) :
    ((batches.flatten.take n).count target : ZMod M) =
      (n / k : Nat) + (bit (prefixPhases batches n target) : ZMod M) := by
  have hb := prefix_count_bounds hk batches horders n hn target
  by_cases hhigh : (batches.flatten.take n).count target = n / k + 1
  · simp only [prefixPhases, hhigh, decide_true, bit, Int.cast_one, Nat.cast_add, Nat.cast_one]
  · have heq : (batches.flatten.take n).count target = n / k := by omega
    simp [prefixPhases, heq, bit]

/-- The actual recursively advanced cuts have the binary batch phases. -/
theorem represents_prefix (hM : 0 < M) (hk : 0 < k)
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (n : Nat) (hn : n ≤ batches.flatten.length) (cuts : Fin k → Fin M) :
    Represents (fun target => cutValue (cuts target)) (n / k : Nat)
      (prefixPhases batches n) (executeCuts hM (batches.flatten.take n) cuts) := by
  intro target
  unfold cutValue
  rw [executeCuts_count, ZMod.natCast_mod, Nat.cast_add,
    prefix_count_phase hk batches horders n hn target]
  change _ = ((cuts target).val : ZMod M) + (n / k : Nat) +
    (bit (prefixPhases batches n target) : ZMod M)
  ring

/-- This is an actual interval of the flattened target word, not an
assumed bound on an unrelated list. -/
theorem consecutive_interval_count (hk : 0 < k) (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (first last : Nat) (horder : first ≤ last) (hlast : last ≤ batches.flatten.length)
    (hconsecutive : last / k ≤ first / k + 1) (target : Fin k) :
    ((batches.flatten.drop first).take (last - first)).count target ≤ 2 := by
  have hfirst := prefix_count_bounds hk batches horders first (by omega) target
  have hlast' := prefix_count_bounds hk batches horders last hlast target
  have hsplit : batches.flatten.take last = batches.flatten.take first ++
      (batches.flatten.drop first).take (last - first) := by
    have heq : last = first + (last - first) := by omega
    conv_lhs => rw [heq, List.take_add]
  have hcounts := congrArg (fun word : List (Fin k) => word.count target) hsplit
  rw [List.count_append] at hcounts
  omega

end CoefficientTwoPrecision.BatchPrefixes

#print axioms CoefficientTwoPrecision.BatchPrefixes.represents_prefix
#print axioms CoefficientTwoPrecision.BatchPrefixes.consecutive_interval_count
