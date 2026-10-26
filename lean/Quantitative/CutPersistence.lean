import Quantitative.RoleComparison
import Quantitative.BatchSafety

/-!
# An equal-cut interval has at most one actual role update

For an interval contained in two consecutive batches, each target occurs
at most twice. A stationary cut cannot return during that interval unless
its target is absent. If common stationary labels have been forced into
the same positions, every intervening update is consequently at the sole
exceptional position. The actual role action then leaves either no update
or exactly one update, since two equal exchanges cancel.
-/

namespace CoefficientTwoPrecision.CutPersistence

open LiteralSchedule BatchSafety FiniteRoles

variable {M k : Nat} {Control : Type}

theorem fixed_cut_iff_absent (hM : 0 < M) (word : List (Fin k))
    (cuts : Fin k → Fin M) (target : Fin k) (hcount : word.count target < M) :
    executeCuts hM word cuts target = cuts target ↔ target ∉ word := by
  constructor
  · intro hfixed
    have hc := congrArg cutValue hfixed
    have hvalue : cutValue (executeCuts hM word cuts target) =
        cutValue (cuts target) + (word.count target : ZMod M) := by
      unfold cutValue
      rw [executeCuts_count, ZMod.natCast_mod, Nat.cast_add]
    rw [hvalue] at hc
    have hz : (word.count target : ZMod M) = 0 := by linear_combination hc
    have hd := (ZMod.natCast_eq_zero_iff (word.count target) M).mp hz
    exact List.count_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hd hcount)
  · intro hnot
    apply Fin.ext
    rw [executeCuts_count, List.count_eq_zero.mpr hnot, Nat.add_zero,
      Nat.mod_eq_of_lt (cuts target).isLt]

theorem two_batch_interval_count (first second : List (Fin k))
    (hfirst : first.Nodup) (hsecond : second.Nodup) (start stop : Nat) (target : Fin k) :
    (first.drop start ++ second.take stop).count target ≤ 2 := by
  have h₁ : (first.drop start).count target ≤ 1 :=
    List.nodup_iff_count_le_one.mp (List.Nodup.sublist (List.drop_sublist _ _) hfirst) target
  have h₂ : (second.take stop).count target ≤ 1 :=
    List.nodup_iff_count_le_one.mp (List.Nodup.sublist (List.take_sublist _ _) hsecond) target
  rw [List.count_append]
  omega

theorem update_twice (target : Fin k) (assignment : Role k ≃ Control) :
    update target (update target assignment) = assignment := by
  apply Equiv.ext
  intro role
  simp only [update, Equiv.trans_apply, Equiv.swap_apply_self]

/-- This is the exact target-word consequence used after extracting
diagonal matches from two equal cyclic bases. -/
theorem interval_empty_or_single (hM : 3 ≤ M) (word : List (Fin k))
    (first second : Role k ≃ Control) (cuts : Fin k → Fin M)
    (hsecond : second = FiniteRoles.execute word first)
    (hdiag : ∀ i j, Matches first second i j → i = j)
    (hmatchCuts : ∀ i, Matches first second i i →
      executeCuts (by omega) word cuts i = cuts i)
    (hcounts : ∀ i, word.count i ≤ 2) :
    word = [] ∨ ∃ target, word = [target] := by
  have habsent (i : Fin k) (hmatch : Matches first second i i) : i ∉ word :=
    (fixed_cut_iff_absent (by omega) word cuts i (by have := hcounts i; omega)).mp
      (hmatchCuts i hmatch)
  by_cases hmobile : first none = second none
  · have hassign := equal_of_diagonal_matches_of_mobile_eq first second hdiag hmobile
    left
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    exact habsent i (by rw [hassign]; rfl) hi
  · obtain ⟨target, _, _, _, hother⟩ :=
      exchange_of_diagonal_matches_of_mobile_ne first second hdiag hmobile
    have hall : ∀ i ∈ word, i = target := by
      intro i hi
      by_contra hne
      exact habsent i (hother i hne) hi
    have hrep : word = List.replicate word.length target := List.eq_replicate_of_mem hall
    have hlength : word.length ≤ 2 := by
      have hc : word.count target = word.length :=
        List.count_eq_length.mpr (fun i hi => (hall i hi).symm)
      rw [← hc]
      exact hcounts target
    have hcases : word.length = 0 ∨ word.length = 1 ∨ word.length = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · have hw : word = [] := by simpa only [hzero, List.replicate_zero] using hrep
      rw [hw] at hsecond
      exact False.elim (hmobile (congrArg (fun e : Role k ≃ Control => e none) hsecond).symm)
    · right
      exact ⟨target, by simpa only [hone, List.replicate_one] using hrep⟩
    · have hw : word = [target, target] := by simpa [htwo] using hrep
      rw [hw] at hsecond
      change second = update target (update target first) at hsecond
      rw [update_twice] at hsecond
      exact False.elim (hmobile (congrArg (fun e : Role k ≃ Control => e none) hsecond).symm)

end CoefficientTwoPrecision.CutPersistence

#print axioms CoefficientTwoPrecision.CutPersistence.fixed_cut_iff_absent
#print axioms CoefficientTwoPrecision.CutPersistence.interval_empty_or_single
