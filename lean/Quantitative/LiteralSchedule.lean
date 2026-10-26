import Quantitative.StationarySuccessor
import SuperpermutationUpperBound.Transport.Ports

/-!
# Literal row lists and target-update schedules

The row lists here use the original `SuperpermutationUpperBound.Row`.
Every update emits its actual full source rows and its final short source
row. Counts and role updates are executable recursive definitions.

The geometric existence theorem in `StationarySuccessor` supplies a valid
number of full moves at each step when the successor cut is unoccupied.
This module does not assume that an arbitrary list of sweep lengths is a
closed contour, and does not assume source-class distinctness. Those are
additional schedule theorems, not fields hidden in a new row structure.
-/

namespace CoefficientTwoPrecision.LiteralSchedule

open PositiveParking JointStates LiteralState StationaryCircle StationaryUpdate StationarySuccessor
open SuperpermutationUpperBound SuperpermutationUpperBound.Transport

variable {M k : Nat} {α : Type}

/-- Restrict the role assignment to the actual stationary positions. -/
def residents (labels : Option Nat → α) : Fin k → α := fun j => labels (some j.val)

theorem updateLabels_residents (labels : Option Nat → α) (target : Fin k) :
    residents (k := k) (updateLabels target.val labels) =
      moveResident (residents labels) target (labels none) := by
  funext j
  by_cases h : j = target
  · subst j
    simp [residents, updateLabels, moveResident]
  · have hval : j.val ≠ target.val := fun heq => h (Fin.ext heq)
    simp [residents, updateLabels, PositiveParking.star, moveResident, h, hval]

theorem updateLabels_mobile (labels : Option Nat → α) (target : Fin k) :
    updateLabels target.val labels none = residents labels target := rfl

/-- Advance one physical cut by one background symbol. -/
def advanceCuts (hM : 0 < M) (target : Fin k) (cuts : Fin k → Fin M) : Fin k → Fin M :=
  moveCut cuts target (successor hM (cuts target))

/-- The cut vector after an actual chronological word of target updates. -/
def executeCuts (hM : 0 < M) : List (Fin k) → (Fin k → Fin M) → Fin k → Fin M
  | [], cuts => cuts
  | target :: word, cuts => executeCuts hM word (advanceCuts hM target cuts)

theorem executeCuts_count (hM : 0 < M) (word : List (Fin k)) (cuts : Fin k → Fin M)
    (j : Fin k) :
    (executeCuts hM word cuts j).val = ((cuts j).val + word.count j) % M := by
  induction word generalizing cuts with
  | nil => simp [executeCuts, Nat.mod_eq_of_lt (cuts j).isLt]
  | cons target word ih =>
    rw [executeCuts, ih]
    by_cases h : j = target
    · subst target
      simp only [advanceCuts, moveCut, ↓reduceIte, successor, List.count_cons_self]
      rw [Nat.mod_add_mod]
      congr 1
      omega
    · have hother : target ≠ j := Ne.symm h
      simp [advanceCuts, moveCut, h, List.count_cons_of_ne hother]

/-- A complete schedule that advances each position by M returns its cuts. -/
theorem executeCuts_closed (hM : 0 < M) (word : List (Fin k)) (cuts : Fin k → Fin M)
    (hcounts : ∀ j, word.count j = M) : executeCuts hM word cuts = cuts := by
  funext j
  apply Fin.ext
  rw [executeCuts_count, hcounts, Nat.add_mod_right, Nat.mod_eq_of_lt (cuts j).isLt]

/-- The actual positive update agrees with the same assignment update used
by the compiled parking-word algebra. -/
theorem positive_update_with_labels (hM : 2 ≤ M) (background : Fin M → α)
    (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (hcuts : Function.Injective cuts) (target : Fin k) (gap : Nat)
    (hfree : ∀ j, cuts j ≠ successor (by omega) (cuts target)) :
    ∃ moves < (render background (residents labels) cuts).length, ∃ nextGap : Nat,
      shortStep (fullIterate moves
        ((render background (residents labels) cuts).rotateLeft gap ++ [labels none])) =
      (render background (residents (updateLabels target.val labels))
        (advanceCuts (by omega) target cuts)).rotateLeft nextGap ++
          [updateLabels target.val labels none] := by
  simpa only [updateLabels_residents, updateLabels_mobile, advanceCuts] using
    positive_update_realizes hM background (residents labels) cuts hcuts target (labels none) gap hfree

def fullRow (base : List α) (satellite : α) : Row α :=
  ⟨base, satellite, base.length⟩

def shortRow (base : List α) (satellite : α) : Row α :=
  ⟨base, satellite, base.length - 2⟩

/-- The actual source occurrences of one update, including its final short row. -/
def updateRows (satellite : α) (moves : Nat) (base : List α) : List (Row α) :=
  (List.range moves).map (fun i => fullRow (fullIterate i base) satellite) ++
    [shortRow (fullIterate moves base) satellite]

def updateEnd (moves : Nat) (base : List α) : List α :=
  shortStep (fullIterate moves base)

/-- A concrete row-list recursion, preserving every source occurrence. -/
def scheduleRows (satellite : α) : List Nat → List α → List (Row α)
  | [], _ => []
  | moves :: rest, base => updateRows satellite moves base ++
      scheduleRows satellite rest (updateEnd moves base)

def scheduleEnd : List Nat → List α → List α
  | [], base => base
  | moves :: rest, base => scheduleEnd rest (updateEnd moves base)

theorem updateRows_length (satellite : α) (moves : Nat) (base : List α) :
    (updateRows satellite moves base).length = moves + 1 := by
  simp [updateRows]

theorem scheduleRows_length (satellite : α) (sweeps : List Nat) (base : List α) :
    (scheduleRows satellite sweeps base).length = sweeps.sum + sweeps.length := by
  induction sweeps generalizing base with
  | nil => simp [scheduleRows]
  | cons moves rest ih =>
    simp only [scheduleRows, List.length_append, updateRows_length, ih,
      List.sum_cons, List.length_cons]
    omega

theorem fullRow_charge (base : List α) (satellite : α) :
    (fullRow base satellite).charge = 0 := by simp [fullRow, Row.charge]

theorem shortRow_charge (base : List α) (satellite : α) (hlen : 2 ≤ base.length) :
    (shortRow base satellite).charge = 2 := by
  simp only [shortRow, Row.charge]
  omega

/-- Every local F transition satisfies the original literal row compatibility. -/
theorem fullRow_compatible (stationary : List α) (mobile satellite : α) (visible : Nat)
    (hlen : 1 ≤ stationary.length) :
    (fullRow (stationary ++ [mobile]) satellite).Compatible
      ⟨literalFullStep (stationary ++ [mobile]), satellite, visible⟩ := by
  unfold Row.Compatible
  rw [literalFullStep_mobile_last]
  change (Row.mk (stationary ++ [mobile]) satellite (stationary ++ [mobile]).length).tail = _
  rw [row_full_tail _ _ (by simp; omega)]
  have hsize : (stationary ++ [mobile]).length - 2 = stationary.length - 1 := by simp
  rw [hsize, List.drop_append_of_le_length (by omega)]
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  change stationary.drop 1 =
    (stationary.rotateLeft 1 ++ [mobile]).take
      ((stationary.rotateLeft 1 ++ [mobile]).length - 2)
  have hrotlen : (stationary.rotateLeft 1).length = stationary.length := by
    rw [LiteralState.rotateLeft_eq_rotate, List.length_rotate]
  rw [List.length_append, List.length_singleton, hrotlen]
  rw [show stationary.length + 1 - 2 = stationary.length - 1 by omega,
    List.take_append_of_le_length (by omega)]
  exact (take_rot_eq_drop stationary 1 hlen).symm

/-- Every local S transition with its specified suffix satisfies literal compatibility. -/
theorem shortRow_compatible (pre : List α) (resident crossed mobile satellite : α)
    (visible : Nat) :
    (shortRow (pre ++ [resident, crossed, mobile]) satellite).Compatible
      ⟨shortStep (pre ++ [resident, crossed, mobile]), satellite, visible⟩ := by
  unfold Row.Compatible
  have hbase : pre ++ [resident, crossed, mobile] = (pre ++ [resident]) ++ [crossed, mobile] := by
    simp [List.append_assoc]
  have hrow : shortRow (pre ++ [resident, crossed, mobile]) satellite =
      Row.mk ((pre ++ [resident]) ++ [crossed, mobile]) satellite (pre ++ [resident]).length := by
    unfold shortRow
    rw [hbase]
    congr 1
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rw [hrow, row_short_tail_append_two _ _ _ _ (by simp), shortStep_suffix]
  simp only [List.length_append, List.length_singleton]
  rw [show pre.length + 1 - 1 = pre.length by omega, List.take_append_length]
  change mobile :: pre =
    (mobile :: (pre ++ [crossed, resident])).take
      ((mobile :: (pre ++ [crossed, resident])).length - 2)
  simp only [List.length_cons, List.length_append, List.length_singleton,
    List.length_nil]
  rw [show pre.length + (0 + 1 + 1) + 1 - 2 = pre.length + 1 by omega,
    List.take_succ_cons, List.take_append_length]

end CoefficientTwoPrecision.LiteralSchedule

#print axioms CoefficientTwoPrecision.LiteralSchedule.executeCuts_count
#print axioms CoefficientTwoPrecision.LiteralSchedule.executeCuts_closed
#print axioms CoefficientTwoPrecision.LiteralSchedule.positive_update_with_labels
#print axioms CoefficientTwoPrecision.LiteralSchedule.scheduleRows_length
#print axioms CoefficientTwoPrecision.LiteralSchedule.fullRow_compatible
#print axioms CoefficientTwoPrecision.LiteralSchedule.shortRow_compatible
