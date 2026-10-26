import Quantitative.ClosedPositive

/-!
# A constructed closed normal positive contour

Stationary indices are ranks in the normal target order. To obtain the
reverse cyclic order of the manuscript, assign rank zero to its first
target and so on. This theorem discharges the complete-batch, count, role
period, and final-target hypotheses of `closed_complete_batches` for a
normal word of M batches. Source-class simplicity and the exact full-run
count are still separate quantitative statements.
-/

namespace CoefficientTwoPrecision.NormalContour

open PositiveParking LiteralSchedule PositiveSchedule ClosedPositive
open RobustMatching BatchSafety
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type}

theorem map_finRange_val (k : Nat) : (List.finRange k).map Fin.val = List.range k := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem repeatWord_map {β γ : Type} (f : β → γ) (n : Nat) (word : List β) :
    (repeatWord n word).map f = repeatWord n (word.map f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatWord, ih]

theorem flatten_replicate {β : Type} (n : Nat) (word : List β) :
    (List.replicate n word).flatten = repeatWord n word := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatWord, List.replicate_succ, ih]

theorem normal_word_count (M k : Nat) (target : Fin k) :
    (repeatWord M (List.finRange k)).count target = M := by
  rw [count_repeatWord]
  have hcount : (List.finRange k).count target = 1 :=
    List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange target)
  simp [hcount]

theorem normal_word_labels (M k : Nat) (hdiv : k + 1 ∣ M) (labels : Option Nat → α) :
    executeLabels (repeatWord M (List.finRange k)) labels = labels := by
  rw [executeLabels_eq_execute, repeatWord_map, map_finRange_val]
  obtain ⟨cycles, hcycles⟩ := hdiv
  rw [hcycles, Nat.mul_comm]
  exact execute_multiple_period updateLabels (List.range k) (k + 1)
    (normal_labels_period k) cycles labels

theorem normal_word_last (M k : Nat) (hM : 0 < M) (hk : 0 < k) :
    ∃ target : Fin k, (repeatWord M (List.finRange k)).getLast? = some target := by
  have hne : repeatWord M (List.finRange k) ≠ [] := by
    intro hnil
    have hlen := length_repeatWord M (List.finRange k)
    simp [hnil] at hlen
    omega
  cases hlast : (repeatWord M (List.finRange k)).getLast? with
  | none => exact False.elim (hne (List.getLast?_eq_none_iff.mp hlast))
  | some target => exact ⟨target, rfl⟩

/-- The actual normal word gives a literally closed contour. No role
period or cut-count hypothesis remains to be instantiated. -/
theorem normal_closed_contour (hM : 2 ≤ M) (hk : 0 < k) (hdiv : k + 1 ∣ M)
    (background : Fin M → α) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (hbackground : Function.Injective background)
    (hresident : Function.Injective (residents (k := k) labels))
    (hcross : ∀ (j : Fin k) (i : Fin M), residents labels j ≠ background i)
    (hrobust : Robust (fun j => cutValue (cuts j))) (satellite : α) :
    ∃ sweeps : List Nat, ∃ base : List α,
      sweeps.length = M * k ∧
      LiteralTrail.SuffixSchedule sweeps base ∧
      scheduleEnd sweeps base = base ∧
      ClosedTrail (scheduleRows satellite sweeps base) := by
  let batches := List.replicate M (List.finRange k)
  have hword : batches.flatten = repeatWord M (List.finRange k) := flatten_replicate _ _
  have horders : ∀ order ∈ batches, order.Perm (List.finRange k) := by
    intro order horder
    have heq : order = List.finRange k := List.eq_of_mem_replicate horder
    simpa only [heq] using List.Perm.refl (List.finRange k)
  have hcounts : ∀ target, batches.flatten.count target = M := by
    intro target
    rw [hword]
    exact normal_word_count M k target
  have hlabels : executeLabels batches.flatten labels = labels := by
    rw [hword]
    exact normal_word_labels M k hdiv labels
  obtain ⟨lastTarget, hlast⟩ := normal_word_last M k (by omega) hk
  obtain ⟨sweeps, base, hlength, hvalid, hend, hclosed⟩ :=
    closed_complete_batches hM background labels cuts hbackground hresident hcross hrobust
      batches horders hcounts hlabels lastTarget (by simpa only [hword] using hlast) satellite
  refine ⟨sweeps, base, ?_, hvalid, hend, hclosed⟩
  rw [hlength, hword, length_repeatWord, List.length_finRange]

end CoefficientTwoPrecision.NormalContour

#print axioms CoefficientTwoPrecision.NormalContour.normal_word_labels
#print axioms CoefficientTwoPrecision.NormalContour.normal_closed_contour
