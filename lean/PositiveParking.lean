import Std

/-!
# Kernel-checked algebra for positive-slot parking

This file formalizes the star-transposition part of sections 5--6 of
`POSITIVE_SLOT_SEED_AND_PARKING.txt`.  It uses only Lean's standard library.
It is not a formalization of literal F/S rows, source-class simplicity,
affine amplification, the generalized Stage interface, or coefficient two.

`none` is the mobile role and `some a` is stationary slot `a`.  A target
word is executed from left to right.  A parking pair is a target word
followed by its reverse.  We prove full-assignment cancellation, avoidance
of every stationary slot other than the first target throughout the pair,
and exact label/count/length agreement after a normal cleanup batch.
-/

namespace PositiveParking

variable {Slot State Label : Type}

/-- Execute a list of updates in chronological order. -/
def execute (act : Slot → State → State) : List Slot → State → State
  | [], s => s
  | a :: w, s => execute act w (act a s)

@[simp] theorem execute_nil (act : Slot → State → State) (s : State) :
    execute act [] s = s := rfl

@[simp] theorem execute_cons (act : Slot → State → State) (a : Slot)
    (w : List Slot) (s : State) :
    execute act (a :: w) s = execute act w (act a s) := rfl

theorem execute_append (act : Slot → State → State) (u v : List Slot) (s : State) :
    execute act (u ++ v) s = execute act v (execute act u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, execute_cons, ih]

/-- A chronological word followed by its reverse cancels for any involutive actions. -/
theorem execute_reverse_cancel (act : Slot → State → State)
    (hinv : ∀ a s, act a (act a s) = s) (w : List Slot) (s : State) :
    execute act (w ++ w.reverse) s = s := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    calc
      execute act ((a :: w) ++ (a :: w).reverse) s =
          act a (execute act (w ++ w.reverse) (act a s)) := by
        simp only [List.reverse_cons, List.cons_append, execute_cons,
          execute_append, execute_nil]
      _ = act a (act a s) := by rw [ih]
      _ = s := hinv a s

/-- Repeat a word a specified number of times. -/
def repeatWord : Nat → List Slot → List Slot
  | 0, _ => []
  | n + 1, w => w ++ repeatWord n w

theorem repeatWord_add (a b : Nat) (w : List Slot) :
    repeatWord (a + b) w = repeatWord a w ++ repeatWord b w := by
  induction a with
  | zero => simp [repeatWord]
  | succ a ih => simp [Nat.succ_add, repeatWord, ih, List.append_assoc]

theorem execute_repeat_identity (act : Slot → State → State) (w : List Slot)
    (hid : ∀ s, execute act w s = s) (n : Nat) (s : State) :
    execute act (repeatWord n w) s = s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [repeatWord, execute_append, hid, ih]

theorem execute_multiple_period (act : Slot → State → State) (normal : List Slot)
    (r : Nat) (hperiod : ∀ s, execute act (repeatWord r normal) s = s)
    (n : Nat) (s : State) :
    execute act (repeatWord (n * r) normal) s = s := by
  induction n generalizing s with
  | zero => simp [repeatWord]
  | succ n ih =>
    rw [Nat.succ_mul, repeatWord_add, execute_append, ih, hperiod]

/-- Both words have identical role action after the final normal batch.
The normal-period hypothesis is explicit; it is not an axiom about normal batches. -/
theorem cleanup_action (act : Slot → State → State)
    (hinv : ∀ a s, act a (act a s) = s) (parking normal : List Slot)
    (r T : Nat) (hperiod : ∀ s, execute act (repeatWord r normal) s = s)
    (s : State) :
    execute act (repeatWord (r * T) (parking ++ parking.reverse) ++ normal) s =
      execute act (repeatWord (2 * (r * T) + 1) normal) s := by
  have hid : ∀ s, execute act (parking ++ parking.reverse) s = s :=
    execute_reverse_cancel act hinv parking
  have hmul : 2 * (r * T) = (2 * T) * r := by
    simp [Nat.mul_assoc, Nat.mul_comm]
  rw [execute_append, execute_repeat_identity act _ hid]
  rw [repeatWord_add, execute_append, hmul,
    execute_multiple_period act normal r hperiod]
  simp [repeatWord]

section Roles

variable [DecidableEq Slot]

/-- The star transposition exchanging mobile and target slot. -/
def star (a : Slot) : Option Slot → Option Slot
  | none => some a
  | some b => if b = a then none else some b

@[simp] theorem star_mobile (a : Slot) : star a none = some a := rfl

@[simp] theorem star_target (a : Slot) : star a (some a) = none := by simp [star]

theorem star_other (a b : Slot) (h : b ≠ a) : star a (some b) = some b := by
  simp [star, h]

theorem star_involutive (a : Slot) (p : Option Slot) : star a (star a p) = p := by
  cases p with
  | none => simp [star]
  | some b =>
    by_cases h : b = a
    · subst b; simp [star]
    · simp [star, h]

/-- Resident labels are pulled back by the transposition of roles. -/
def updateLabels (a : Slot) (s : Option Slot → Label) : Option Slot → Label :=
  fun p => s (star a p)

theorem updateLabels_involutive (a : Slot) (s : Option Slot → Label) :
    updateLabels a (updateLabels a s) = s := by
  funext p
  simp only [updateLabels, star_involutive]

theorem parking_restores_all_labels (w : List Slot) (s : Option Slot → Label) :
    execute updateLabels (w ++ w.reverse) s = s :=
  execute_reverse_cancel updateLabels updateLabels_involutive w s

theorem parking_returns_mobile (w : List Slot) :
    execute star (w ++ w.reverse) none = none :=
  execute_reverse_cancel star star_involutive w none

/-- Every role occupied after an update, in chronological order. -/
def positions : List Slot → Option Slot → List (Option Slot)
  | [], _ => []
  | a :: w, p => star a p :: positions w (star a p)

theorem positions_append (u v : List Slot) (p : Option Slot) :
    positions (u ++ v) p = positions u p ++ positions v (execute star u p) := by
  induction u generalizing p with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, positions, execute_cons, ih]

theorem execute_fixes_unused_slot (w : List Slot) (a : Slot) (h : a ∉ w) :
    execute star w (some a) = some a := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hab : a ≠ b := fun hab => h (by simp [hab])
    have haw : a ∉ w := fun haw => h (by simp [haw])
    simp only [execute_cons, star_other b a hab, ih haw]

theorem positions_fixes_unused_slot (w : List Slot) (a : Slot) (h : a ∉ w)
    (p : Option Slot) (hp : p ∈ positions w (some a)) : p = some a := by
  induction w with
  | nil => simp [positions] at hp
  | cons b w ih =>
    have hab : a ≠ b := fun hab => h (by simp [hab])
    have haw : a ∉ w := fun haw => h (by simp [haw])
    simp only [positions, star_other b a hab, List.mem_cons] at hp
    rcases hp with hp | hp
    · exact hp
    · exact ih haw hp

/-- A marked mobile token is only mobile or in the first target slot at every
update boundary of the pair.  The only required uniqueness is that the first
target is absent from the rest of the order. -/
theorem parking_positions (a : Slot) (rest : List Slot) (h : a ∉ rest)
    (p : Option Slot)
    (hp : p ∈ positions ((a :: rest) ++ (a :: rest).reverse) none) :
    p = none ∨ p = some a := by
  have hrest : a ∉ rest ++ rest.reverse := by simp [h]
  have hword : (a :: rest) ++ (a :: rest).reverse =
      a :: ((rest ++ rest.reverse) ++ [a]) := by
    simp [List.reverse_cons, List.append_assoc]
  rw [hword] at hp
  change p ∈ some a :: positions ((rest ++ rest.reverse) ++ [a]) (some a) at hp
  rw [positions_append, execute_fixes_unused_slot _ a hrest] at hp
  simp only [positions, star_target, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp
  · exact Or.inr hp
  · exact Or.inr (positions_fixes_unused_slot _ a hrest p hp)
  · exact Or.inl hp

/-- In particular the protected token never resides in any forbidden slot
different from the first target.  This includes all update boundaries. -/
theorem parking_avoids (a forbidden : Slot) (rest : List Slot)
    (h : a ∉ rest) (haf : a ≠ forbidden) :
    some forbidden ∉ positions ((a :: rest) ++ (a :: rest).reverse) none := by
  intro hp
  rcases parking_positions a rest h (some forbidden) hp with hnone | hsome
  · cases hnone
  · exact haf (Option.some.inj hsome).symm

/-- The protected token avoids the forbidden slot throughout arbitrarily many
parking pairs, because each pair returns it to the mobile role. -/
theorem repeated_parking_avoids (a forbidden : Slot) (rest : List Slot)
    (h : a ∉ rest) (haf : a ≠ forbidden) (n : Nat) :
    some forbidden ∉
      positions (repeatWord n ((a :: rest) ++ (a :: rest).reverse)) none := by
  induction n with
  | zero => simp [repeatWord, positions]
  | succ n ih =>
    rw [repeatWord, positions_append, parking_returns_mobile]
    intro hp
    rcases List.mem_append.mp hp with hp | hp
    · exact parking_avoids a forbidden rest h haf hp
    · exact ih hp

end Roles

section Counts

variable [DecidableEq Slot]

omit [DecidableEq Slot] in
theorem length_repeatWord (n : Nat) (w : List Slot) :
    (repeatWord n w).length = n * w.length := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord, ih, Nat.succ_mul, Nat.add_comm]

theorem count_repeatWord (n : Nat) (w : List Slot) (a : Slot) :
    (repeatWord n w).count a = n * w.count a := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord, ih, Nat.succ_mul, Nat.add_comm]

/-- A parking pair updates every target exactly twice as often as its first half. -/
theorem count_parking_pair (w : List Slot) (a : Slot) :
    (w ++ w.reverse).count a = 2 * w.count a := by
  simp [Nat.two_mul]

theorem cleanup_count (parking normal : List Slot)
    (hcount : ∀ a, parking.count a = normal.count a) (r T : Nat) (a : Slot) :
    (repeatWord (r * T) (parking ++ parking.reverse) ++ normal).count a =
      (repeatWord (2 * (r * T) + 1) normal).count a := by
  simp only [List.count_append, count_repeatWord, List.count_reverse, hcount]
  simp [Nat.add_mul, Nat.mul_add, Nat.two_mul]

omit [DecidableEq Slot] in
theorem cleanup_length (parking normal : List Slot)
    (hlen : parking.length = normal.length) (r T : Nat) :
    (repeatWord (r * T) (parking ++ parking.reverse) ++ normal).length =
      (repeatWord (2 * (r * T) + 1) normal).length := by
  simp only [List.length_append, length_repeatWord, List.length_reverse, hlen]
  simp [Nat.add_mul, Nat.mul_add, Nat.two_mul]

end Counts

section NormalOrder

/-- Encode mobile as zero and stationary slot i as i+1. -/
def roleIndex : Option Nat → Nat
  | none => 0
  | some i => i + 1

theorem roleIndex_injective {p q : Option Nat} (h : roleIndex p = roleIndex q) : p = q := by
  cases p <;> cases q <;> simp_all [roleIndex]

def starIndex (a p : Nat) : Nat :=
  if p = 0 then a + 1 else if p = a + 1 then 0 else p

def cyclicSuccessor (k p : Nat) : Nat :=
  if p < k then p + 1 else if p = k then 0 else p

theorem star_roleIndex (a : Nat) (p : Option Nat) :
    roleIndex (star a p) = starIndex a (roleIndex p) := by
  cases p with
  | none => simp [star, roleIndex, starIndex]
  | some b =>
    by_cases hab : b = a <;> simp [star, roleIndex, starIndex, hab]

theorem cyclicSuccessor_succ (k p : Nat) :
    starIndex k (cyclicSuccessor k p) = cyclicSuccessor (k + 1) p := by
  by_cases hlt : p < k
  · have hlt' : p < k + 1 := by omega
    have he : p ≠ k := by omega
    simp [cyclicSuccessor, starIndex, hlt, hlt', he]
  · by_cases he : p = k
    · subst p
      simp [cyclicSuccessor, starIndex]
    · by_cases he' : p = k + 1
      · subst p
        have hnk : ¬ k + 1 < k := by omega
        simp [cyclicSuccessor, starIndex, hnk]
      · have hgt : ¬ p < k + 1 := by omega
        have hn : p ≠ 0 := by omega
        simp [cyclicSuccessor, starIndex, hlt, he, he', hgt, hn]

/-- One normal batch is the cycle 0→1→...→k→0 on mobile/slot ranks.
Any stationary indices outside the chosen k slots are fixed. -/
theorem normal_batch_roleIndex (k : Nat) (p : Option Nat) :
    roleIndex (execute star (List.range k) p) = cyclicSuccessor k (roleIndex p) := by
  induction k with
  | zero => cases p <;> simp [roleIndex, cyclicSuccessor]
  | succ k ih =>
    rw [List.range_succ, execute_append]
    simp only [execute_cons, execute_nil, star_roleIndex, ih]
    exact cyclicSuccessor_succ k (roleIndex p)

theorem cyclicSuccessor_in_range (k p : Nat) (hp : p ≤ k) :
    cyclicSuccessor k p ≤ k := by
  unfold cyclicSuccessor
  split <;> (try split) <;> omega

theorem normal_repeated_roleIndex (k n : Nat) (p : Option Nat) (hp : roleIndex p ≤ k) :
    roleIndex (execute star (repeatWord n (List.range k)) p) =
      (roleIndex p + n) % (k + 1) := by
  induction n generalizing p with
  | zero => simpa [repeatWord] using (Nat.mod_eq_of_lt (show roleIndex p < k + 1 by omega)).symm
  | succ n ih =>
    rw [repeatWord, execute_append]
    have hp' : roleIndex (execute star (List.range k) p) ≤ k := by
      rw [normal_batch_roleIndex]
      exact cyclicSuccessor_in_range k (roleIndex p) hp
    rw [ih _ hp', normal_batch_roleIndex]
    by_cases hlt : roleIndex p < k
    · simp only [cyclicSuccessor, hlt, ↓reduceIte]
      congr 1
      omega
    · have he : roleIndex p = k := by omega
      simp only [cyclicSuccessor, he, Nat.lt_irrefl, ↓reduceIte, Nat.zero_add]
      have hadd : k + (n + 1) = n + (k + 1) := by omega
      rw [hadd, Nat.add_mod_right]

theorem normal_repeated_fixes_outside (k n : Nat) (p : Option Nat)
    (hp : k < roleIndex p) :
    execute star (repeatWord n (List.range k)) p = p := by
  have hone : execute star (List.range k) p = p := by
    apply roleIndex_injective
    rw [normal_batch_roleIndex]
    simp [cyclicSuccessor, show ¬ roleIndex p < k by omega, show roleIndex p ≠ k by omega]
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatWord, execute_append, hone, ih]

/-- The normal batch has period exactly dividing k+1 on all role positions.
No period hypothesis is needed for the canonical normal target order. -/
theorem normal_position_period (k : Nat) (p : Option Nat) :
    execute star (repeatWord (k + 1) (List.range k)) p = p := by
  by_cases hp : roleIndex p ≤ k
  · apply roleIndex_injective
    rw [normal_repeated_roleIndex k (k + 1) p hp, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · exact normal_repeated_fixes_outside k (k + 1) p (by omega)

/-- At the first k+1 normal boundaries the initially mobile token visits
every role once, in rank order.  Thus the cycle has exactly k+1 roles. -/
theorem normal_mobile_orbit (k n : Nat) (hn : n < k + 1) :
    roleIndex (execute star (repeatWord n (List.range k)) none) = n := by
  rw [normal_repeated_roleIndex k n none (by simp [roleIndex])]
  simpa [roleIndex] using Nat.mod_eq_of_lt hn

theorem labels_follow_positions [DecidableEq Slot] (w : List Slot)
    (s : Option Slot → Label) (p : Option Slot) :
    (execute updateLabels w s) (execute star w p) = s p := by
  induction w generalizing s p with
  | nil => rfl
  | cons a w ih =>
    simp only [execute_cons, ih, updateLabels, star_involutive]

/-- The entire label assignment returns after k+1 canonical normal batches. -/
theorem normal_labels_period (k : Nat) (s : Option Nat → Label) :
    execute updateLabels (repeatWord (k + 1) (List.range k)) s = s := by
  funext p
  have h := labels_follow_positions (repeatWord (k + 1) (List.range k)) s p
  rw [normal_position_period] at h
  exact h

/-- Fully discharged normal-cycle version of the parking-and-cleanup endpoint. -/
theorem normal_cleanup_labels (parking : List Nat) (k T : Nat)
    (s : Option Nat → Label) :
    execute updateLabels
        (repeatWord ((k + 1) * T) (parking ++ parking.reverse) ++ List.range k) s =
      execute updateLabels
        (repeatWord (2 * ((k + 1) * T) + 1) (List.range k)) s :=
  cleanup_action updateLabels updateLabels_involutive parking (List.range k)
    (k + 1) T (normal_labels_period k) s

/-- The last target in a positive number of complete batches is the batch's
last target, also when the batch is empty. -/
theorem last_repeatWord_succ (n : Nat) (w : List Slot) :
    (repeatWord (n + 1) w).getLast? = w.getLast? := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih =>
    rw [repeatWord, List.getLast?_append, ih]
    cases w.getLast? <;> rfl

/-- The complete discrete endpoint data agree: all labels, every slot's
positive advance count, the number of shorts, and the final target slot.
Reconstructing a literal F/S base from these data is outside this module. -/
theorem normal_cleanup_endpoint (parking : List Nat) (k T : Nat)
    (hk : 0 < k) (horder : parking.Perm (List.range k))
    (s : Option Nat → Label) :
    let patched := repeatWord ((k + 1) * T) (parking ++ parking.reverse) ++ List.range k
    let nominal := repeatWord (2 * ((k + 1) * T) + 1) (List.range k)
    execute updateLabels patched s = execute updateLabels nominal s ∧
      (∀ a, patched.count a = nominal.count a) ∧
      patched.length = nominal.length ∧
      patched.getLast? = nominal.getLast? := by
  dsimp only
  refine ⟨normal_cleanup_labels parking k T s, ?_, ?_, ?_⟩
  · exact cleanup_count parking (List.range k) (fun a => horder.count_eq a) (k + 1) T
  · exact cleanup_length parking (List.range k) horder.length_eq (k + 1) T
  · rw [List.getLast?_append, last_repeatWord_succ, List.getLast?_range]
    simp [show k ≠ 0 by omega]

end NormalOrder

end PositiveParking

#print axioms PositiveParking.parking_restores_all_labels
#print axioms PositiveParking.parking_avoids
#print axioms PositiveParking.repeated_parking_avoids
#print axioms PositiveParking.cleanup_action
#print axioms PositiveParking.cleanup_count
#print axioms PositiveParking.cleanup_length
#print axioms PositiveParking.normal_labels_period
#print axioms PositiveParking.normal_cleanup_labels
#print axioms PositiveParking.normal_cleanup_endpoint
