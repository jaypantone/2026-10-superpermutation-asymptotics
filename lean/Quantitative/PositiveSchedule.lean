import Quantitative.LiteralTrail

/-!
# Constructing an actual row schedule from a safe target word

The safety predicate below concerns only the explicit cut vectors: at each
update, the next background cut is unoccupied. It is not a word-existence
or row-containment premise. Recursion chooses the actual full sweep supplied
by `positive_update_with_labels`, constructs its source rows, and proves the
literal endpoint is the rendered state after all target updates.

To specialize to normal and parking contours, one must still prove this
cut-safety predicate from robust separation and complete-batch prefixes,
identify the final post-update gap, and prove source-class simplicity.
-/

namespace CoefficientTwoPrecision.PositiveSchedule

open PositiveParking JointStates LiteralState StationaryCircle StationaryUpdate
open StationarySuccessor LiteralSchedule LiteralTrail

variable {M k : Nat} {α : Type}

/-- Every intended target can advance to a currently unoccupied cut. -/
def SafeTargets (hM : 0 < M) : List (Fin k) → (Fin k → Fin M) → Prop
  | [], _ => True
  | target :: word, cuts =>
      (∀ j, cuts j ≠ successor hM (cuts target)) ∧
      SafeTargets hM word (advanceCuts hM target cuts)

/-- The actual label assignment after a chronological word of finite targets. -/
def executeLabels : List (Fin k) → (Option Nat → α) → Option Nat → α
  | [], labels => labels
  | target :: word, labels => executeLabels word (updateLabels target.val labels)

theorem executeLabels_eq_execute (word : List (Fin k)) (labels : Option Nat → α) :
    executeLabels word labels = execute updateLabels (word.map Fin.val) labels := by
  induction word generalizing labels with
  | nil => rfl
  | cons target word ih =>
    simp only [executeLabels, List.map_cons, execute_cons, ih]

/-- A small lower length bound needs no label injectivity: every cut block
contains its background symbol. -/
theorem render_length_ge_background (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) : M ≤ (render background resident cuts).length := by
  have hlist (order : List (Fin M)) :
      order.length ≤ (order.flatMap (block background resident cuts)).length := by
    induction order with
    | nil => simp
    | cons cut order ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hb : 1 ≤ (block background resident cuts cut).length := by simp [block]
      omega
  simpa [render] using hlist (List.finRange M)

/-- Safe target words preserve injective stationary cuts. -/
theorem executeCuts_injective (hM : 0 < M) (word : List (Fin k))
    (cuts : Fin k → Fin M) (hcuts : Function.Injective cuts)
    (hsafe : SafeTargets hM word cuts) :
    Function.Injective (executeCuts hM word cuts) := by
  induction word generalizing cuts with
  | nil => exact hcuts
  | cons target word ih =>
    exact ih (advanceCuts hM target cuts)
      (moveCut_injective cuts hcuts target _ hsafe.1) hsafe.2

/-- Keep the actual suffix witness together with the endpoint equality;
both must refer to the same chosen number of full moves. -/
theorem positive_update_with_suffix (hM : 2 ≤ M) (background : Fin M → α)
    (resident : Fin k → α) (cuts : Fin k → Fin M)
    (hcuts : Function.Injective cuts) (target : Fin k) (mobile : α) (gap : Nat)
    (hfree : ∀ j, cuts j ≠ successor (by omega) (cuts target)) :
    ∃ moves < (render background resident cuts).length, ∃ nextGap : Nat, ∃ pre : List α,
      fullIterate moves ((render background resident cuts).rotateLeft gap ++ [mobile]) =
        pre ++ [resident target, background (cuts target), mobile] ∧
      shortStep (fullIterate moves ((render background resident cuts).rotateLeft gap ++ [mobile])) =
        (render background (moveResident resident target mobile)
          (moveCut cuts target (successor (by omega) (cuts target)))).rotateLeft nextGap ++
            [resident target] := by
  obtain ⟨rest, hold, hnew⟩ := positive_local_forms hM background resident cuts hcuts target mobile hfree
  have holdTarget : List.IsRotated (render background resident cuts)
      ((background (successor (by omega) (cuts target)) :: rest) ++
        [resident target, background (cuts target)]) :=
    hold.trans (List.isRotated_append
      (l := [resident target, background (cuts target)])
      (l' := background (successor (by omega) (cuts target)) :: rest))
  have hnewTarget : List.IsRotated
      (render background (moveResident resident target mobile)
        (moveCut cuts target (successor (by omega) (cuts target))))
      ((mobile :: background (successor (by omega) (cuts target)) :: rest) ++
        [background (cuts target)]) :=
    hnew.trans (List.isRotated_append
      (l := [background (cuts target)])
      (l' := mobile :: background (successor (by omega) (cuts target)) :: rest))
  obtain ⟨desired, hdesired⟩ := holdTarget
  obtain ⟨nextGap, hafter⟩ := hnewTarget
  have hlen : 0 < (render background resident cuts).length := by
    have h := render_length_ge_background background resident cuts
    omega
  obtain ⟨moves, hmoves, hreach⟩ :=
    rotation_reachable (render background resident cuts) hlen gap desired
  have hfull : fullIterate moves ((render background resident cuts).rotateLeft gap ++ [mobile]) =
      (background (successor (by omega) (cuts target)) :: rest) ++
        [resident target, background (cuts target), mobile] := by
    rw [fullIterate_formula, hreach, LiteralState.rotateLeft_eq_rotate, hdesired]
    simp [List.append_assoc]
  refine ⟨moves, hmoves, nextGap,
    background (successor (by omega) (cuts target)) :: rest, hfull, ?_⟩
  rw [hfull, shortStep_suffix, LiteralState.rotateLeft_eq_rotate, hafter]
  simp [List.append_assoc]

/-- Construct actual full/short source rows for every safe target word,
with exact role and cut endpoints and the correct number of short updates. -/
theorem realize_targets (hM : 2 ≤ M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (hcuts : Function.Injective cuts) (gap : Nat)
    (hsafe : SafeTargets (by omega) word cuts) :
    ∃ sweeps : List Nat, ∃ finalGap : Nat,
      sweeps.length = word.length ∧
      SuffixSchedule sweeps ((render background (residents labels) cuts).rotateLeft gap ++ [labels none]) ∧
      scheduleEnd sweeps ((render background (residents labels) cuts).rotateLeft gap ++ [labels none]) =
        (render background (residents (executeLabels word labels))
          (executeCuts (by omega) word cuts)).rotateLeft finalGap ++ [executeLabels word labels none] := by
  induction word generalizing labels cuts gap with
  | nil => exact ⟨[], gap, rfl, True.intro, rfl⟩
  | cons target word ih =>
    let newCuts := advanceCuts (show 0 < M by omega) target cuts
    let newLabels := updateLabels target.val labels
    obtain ⟨moves, hmoves, nextGap, pre, hpre, hstep⟩ :=
      positive_update_with_suffix hM background (residents labels) cuts hcuts target (labels none) gap hsafe.1
    have hnext : updateEnd moves
        ((render background (residents labels) cuts).rotateLeft gap ++ [labels none]) =
        (render background (residents newLabels) newCuts).rotateLeft nextGap ++ [newLabels none] := by
      simpa only [updateEnd, newLabels, newCuts, updateLabels_residents,
        updateLabels_mobile, advanceCuts] using hstep
    have hnewCuts : Function.Injective newCuts :=
      moveCut_injective cuts hcuts target _ hsafe.1
    obtain ⟨sweeps, finalGap, hlength, hvalid, hend⟩ :=
      ih newLabels newCuts hnewCuts nextGap hsafe.2
    refine ⟨moves :: sweeps, finalGap, by simp [hlength], ?_, ?_⟩
    · refine ⟨⟨(render background (residents labels) cuts).rotateLeft gap,
        labels none, rfl, ?_⟩, ?_, ?_⟩
      · have hlen := render_length_ge_background background (residents labels) cuts
        rw [LiteralState.rotateLeft_eq_rotate, List.length_rotate]
        omega
      · exact ⟨pre, residents labels target, background (cuts target), labels none, hpre⟩
      · rw [hnext]
        exact hvalid
    · change scheduleEnd sweeps (updateEnd moves _) = _
      rw [hnext]
      exact hend

end CoefficientTwoPrecision.PositiveSchedule

#print axioms CoefficientTwoPrecision.PositiveSchedule.executeCuts_injective
#print axioms CoefficientTwoPrecision.PositiveSchedule.positive_update_with_suffix
#print axioms CoefficientTwoPrecision.PositiveSchedule.realize_targets
