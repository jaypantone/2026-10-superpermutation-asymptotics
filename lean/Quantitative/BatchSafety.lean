import Quantitative.PositiveSchedule
import Quantitative.RobustSafety

/-!
# Robust cuts permit every complete-batch target schedule

The literal positive-update existence theorem requires an empty successor
cut. Here that premise is proved for every sequence of batches that visits
each stationary position once. Within a batch the cut representation has
binary phases; at its end the common translation increases by one and the
phase vector resets. This theorem supplies `SafeTargets` for normal orders,
parking orders, their reverses, and arbitrary mixtures of those orders.
-/

namespace CoefficientTwoPrecision.BatchSafety

open PositiveParking StationaryUpdate StationarySuccessor LiteralSchedule PositiveSchedule
open RobustMatching RobustSafety

variable {M k : Nat}

def cutValue (cut : Fin M) : ZMod M := (cut.val : ZMod M)

theorem successor_cutValue (hM : 0 < M) (cut : Fin M) :
    cutValue (successor hM cut) = cutValue cut + 1 := by
  simp [cutValue, successor, ZMod.natCast_mod, Nat.cast_add]

def Represents (q : Fin k → ZMod M) (translation : ZMod M)
    (phases : Fin k → Bool) (cuts : Fin k → Fin M) : Prop :=
  ∀ j, cutValue (cuts j) = perturbed q translation phases j

theorem represented_successor_free (hM : 2 ≤ M) (q : Fin k → ZMod M)
    (hrobust : Robust q) (translation : ZMod M) (phases : Fin k → Bool)
    (cuts : Fin k → Fin M) (hrep : Represents q translation phases cuts)
    (target : Fin k) : ∀ j, cuts j ≠ successor (by omega) (cuts target) := by
  intro j h
  have hc := congrArg cutValue h
  rw [successor_cutValue, hrep j, hrep target] at hc
  exact successor_unoccupied hM q hrobust translation phases j target hc

def mark (phases : Fin k → Bool) (target : Fin k) : Fin k → Bool :=
  fun j => if j = target then true else phases j

theorem represents_advance (hM : 0 < M) (q : Fin k → ZMod M)
    (translation : ZMod M) (phases : Fin k → Bool) (cuts : Fin k → Fin M)
    (hrep : Represents q translation phases cuts) (target : Fin k)
    (hzero : phases target = false) :
    Represents q translation (mark phases target) (advanceCuts hM target cuts) := by
  intro j
  by_cases hj : j = target
  · subst j
    simp only [advanceCuts, moveCut, ↓reduceIte]
    rw [successor_cutValue, hrep]
    simp [perturbed, mark, hzero, bit]
  · simpa only [advanceCuts, moveCut, if_neg hj, perturbed, mark] using hrep j

/-- Every list of distinct not-yet-updated targets is geometrically safe. -/
theorem nodup_targets_safe (hM : 2 ≤ M) (q : Fin k → ZMod M) (hrobust : Robust q)
    (translation : ZMod M) (word : List (Fin k)) (hword : word.Nodup)
    (phases : Fin k → Bool) (cuts : Fin k → Fin M)
    (hrep : Represents q translation phases cuts)
    (hzero : ∀ j ∈ word, phases j = false) : SafeTargets (by omega) word cuts := by
  induction word generalizing phases cuts with
  | nil => trivial
  | cons target word ih =>
    refine ⟨represented_successor_free hM q hrobust translation phases cuts hrep target, ?_⟩
    have hnd := List.nodup_cons.mp hword
    apply ih hnd.2 (mark phases target) (advanceCuts (by omega) target cuts)
    · exact represents_advance (by omega) q translation phases cuts hrep target
        (hzero target (by simp))
    · intro j hj
      have hne : j ≠ target := by
        intro heq
        subst j
        exact hnd.1 hj
      simpa [mark, hne] using hzero j (by simp [hj])

theorem safeTargets_append (hM : 0 < M) (first second : List (Fin k))
    (cuts : Fin k → Fin M) (hfirst : SafeTargets hM first cuts)
    (hsecond : SafeTargets hM second (executeCuts hM first cuts)) :
    SafeTargets hM (first ++ second) cuts := by
  induction first generalizing cuts with
  | nil => exact hsecond
  | cons target first ih =>
    exact ⟨hfirst.1, ih _ hfirst.2 hsecond⟩

theorem represents_after_complete_batch (hM : 0 < M) (q : Fin k → ZMod M)
    (translation : ZMod M) (word : List (Fin k))
    (hword : word.Perm (List.finRange k)) (cuts : Fin k → Fin M)
    (hrep : Represents q translation (fun _ => false) cuts) :
    Represents q (translation + 1) (fun _ => false) (executeCuts hM word cuts) := by
  intro j
  have hcount : word.count j = 1 := by
    rw [hword.count_eq j]
    exact List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange j)
  have hbase := hrep j
  simp only [perturbed, bit, Int.cast_zero, add_zero] at hbase ⊢
  unfold cutValue
  rw [executeCuts_count, hcount, ZMod.natCast_mod, Nat.cast_add, Nat.cast_one]
  change cutValue (cuts j) + 1 = _
  rw [hbase]
  ring

theorem executeCuts_append (hM : 0 < M) (first second : List (Fin k))
    (cuts : Fin k → Fin M) :
    executeCuts hM (first ++ second) cuts = executeCuts hM second (executeCuts hM first cuts) := by
  induction first generalizing cuts with
  | nil => rfl
  | cons target first ih => simpa only [List.cons_append, executeCuts] using ih _

/-- Every sequence of complete target orders is safe from robust initial
cuts. No restriction on the order of the stationary targets is needed. -/
theorem complete_batches_safe (hM : 2 ≤ M) (q : Fin k → ZMod M) (hrobust : Robust q)
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (translation : ZMod M) (cuts : Fin k → Fin M)
    (hrep : Represents q translation (fun _ => false) cuts) :
    SafeTargets (by omega) batches.flatten cuts := by
  induction batches generalizing translation cuts with
  | nil => trivial
  | cons order batches ih =>
    have horder := horders order (by simp)
    have hsafe : SafeTargets (show 0 < M by omega) order cuts :=
      nodup_targets_safe hM q hrobust translation order
        (horder.nodup_iff.mpr (List.nodup_finRange k)) (fun _ => false) cuts hrep
        (fun _ _ => rfl)
    apply safeTargets_append (by omega) order batches.flatten cuts hsafe
    apply ih (fun next hnext => horders next (by simp [hnext])) (translation + 1)
      (executeCuts (by omega) order cuts)
    exact represents_after_complete_batch (by omega) q translation order horder cuts hrep

end CoefficientTwoPrecision.BatchSafety

#print axioms CoefficientTwoPrecision.BatchSafety.nodup_targets_safe
#print axioms CoefficientTwoPrecision.BatchSafety.represents_after_complete_batch
#print axioms CoefficientTwoPrecision.BatchSafety.complete_batches_safe
