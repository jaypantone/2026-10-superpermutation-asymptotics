import Quantitative.PositiveSchedule

/-!
# A constructed target trace retains every actual row's prefix state

The recursive relation records the concrete suffix and the exact rendered
endpoint at each update. It is constructed from `SafeTargets`; no existence
or row-containment assumption is hidden in the relation. The extraction
theorem identifies every emitted row with a prefix of the target word.
-/

namespace CoefficientTwoPrecision.TargetTrace

open PositiveParking JointStates LiteralState StationaryCircle StationaryUpdate
open StationarySuccessor LiteralSchedule LiteralTrail PositiveSchedule
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type}

def renderedBase (background : Fin M → α) (labels : Option Nat → α)
    (cuts : Fin k → Fin M) (gap : Nat) : List α :=
  (render background (residents labels) cuts).rotateLeft gap ++ [labels none]

def Trace (hM : 0 < M) (background : Fin M → α) :
    List (Fin k) → (Option Nat → α) → (Fin k → Fin M) → Nat → List Nat → Nat → Prop
  | [], _, _, gap, sweeps, finalGap => sweeps = [] ∧ finalGap = gap
  | target :: word, labels, cuts, gap, sweeps, finalGap =>
      ∃ moves rest nextGap pre,
        sweeps = moves :: rest ∧
        moves < (render background (residents labels) cuts).length ∧
        fullIterate moves (renderedBase background labels cuts gap) =
          pre ++ [residents labels target, background (cuts target), labels none] ∧
        updateEnd moves (renderedBase background labels cuts gap) =
          renderedBase background (updateLabels target.val labels)
            (advanceCuts hM target cuts) nextGap ∧
        Trace hM background word (updateLabels target.val labels)
          (advanceCuts hM target cuts) nextGap rest finalGap

/-- Construct the aligned target and literal-row transcript. -/
theorem exists_trace (hM : 2 ≤ M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (hcuts : Function.Injective cuts) (gap : Nat)
    (hsafe : SafeTargets (by omega) word cuts) :
    ∃ sweeps finalGap, Trace (by omega) background word labels cuts gap sweeps finalGap := by
  induction word generalizing labels cuts gap with
  | nil => exact ⟨[], gap, rfl, rfl⟩
  | cons target word ih =>
    obtain ⟨moves, hmoves, nextGap, pre, hpre, hstep⟩ :=
      positive_update_with_suffix hM background (residents labels) cuts hcuts target (labels none) gap hsafe.1
    have hnewCuts : Function.Injective (advanceCuts (show 0 < M by omega) target cuts) :=
      moveCut_injective cuts hcuts target _ hsafe.1
    obtain ⟨rest, finalGap, hrest⟩ :=
      ih (updateLabels target.val labels) (advanceCuts (by omega) target cuts)
        hnewCuts nextGap hsafe.2
    refine ⟨moves :: rest, finalGap, moves, rest, nextGap, pre, rfl, hmoves, hpre, ?_, hrest⟩
    simpa only [updateEnd, renderedBase, updateLabels_residents, updateLabels_mobile, advanceCuts] using hstep

theorem trace_length (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace hM background word labels cuts gap sweeps finalGap) :
    sweeps.length = word.length := by
  induction word generalizing labels cuts gap sweeps with
  | nil => rcases htrace with ⟨rfl, _⟩; rfl
  | cons target word ih =>
    obtain ⟨moves, rest, nextGap, pre, rfl, _, _, _, hrest⟩ := htrace
    simp only [List.length_cons, ih _ _ _ _ hrest]

theorem trace_endpoint (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace hM background word labels cuts gap sweeps finalGap) :
    scheduleEnd sweeps (renderedBase background labels cuts gap) =
      renderedBase background (executeLabels word labels) (executeCuts hM word cuts) finalGap := by
  induction word generalizing labels cuts gap sweeps with
  | nil => rcases htrace with ⟨rfl, rfl⟩; rfl
  | cons target word ih =>
    obtain ⟨moves, rest, nextGap, pre, rfl, _, _, hnext, hrest⟩ := htrace
    change scheduleEnd rest (updateEnd moves _) = _
    rw [hnext]
    exact ih _ _ _ _ hrest

theorem trace_suffixSchedule (hM : 2 ≤ M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background word labels cuts gap sweeps finalGap) :
    SuffixSchedule sweeps (renderedBase background labels cuts gap) := by
  induction word generalizing labels cuts gap sweeps with
  | nil => rcases htrace with ⟨rfl, _⟩; trivial
  | cons target word ih =>
    obtain ⟨moves, rest, nextGap, pre, rfl, _, hpre, hnext, hrest⟩ := htrace
    refine ⟨⟨(render background (residents labels) cuts).rotateLeft gap, labels none, rfl, ?_⟩,
      ⟨pre, residents labels target, background (cuts target), labels none, hpre⟩, ?_⟩
    · rw [LiteralState.rotateLeft_eq_rotate, List.length_rotate]
      have hlen := render_length_ge_background background (residents labels) cuts
      omega
    · rw [hnext]
      exact ih _ _ _ _ hrest

theorem updateRows_base (satellite : α) (moves : Nat) (initial : List α) (row : Row α)
    (hrow : row ∈ updateRows satellite moves initial) :
    ∃ i ≤ moves, row.base = fullIterate i initial := by
  simp only [updateRows, List.mem_append, List.mem_map, List.mem_singleton] at hrow
  rcases hrow with ⟨i, hi, rfl⟩ | rfl
  · exact ⟨i, (List.mem_range.mp hi).le, rfl⟩
  · exact ⟨moves, le_rfl, rfl⟩

/-- Every actual emitted source row has the cut and role state of a
specific target-word prefix. Its mobile gap is unrestricted, as required
by the envelope construction. -/
theorem row_prefix_state (hM : 0 < M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace hM background word labels cuts gap sweeps finalGap)
    (satellite : α) (row : Row α)
    (hrow : row ∈ scheduleRows satellite sweeps (renderedBase background labels cuts gap)) :
    ∃ initialWord : List (Fin k), ∃ target tail newGap,
      word = initialWord ++ target :: tail ∧
      row.base = renderedBase background (executeLabels initialWord labels)
        (executeCuts hM initialWord cuts) newGap := by
  induction word generalizing labels cuts gap sweeps with
  | nil =>
    obtain ⟨rfl, _⟩ := htrace
    simp [scheduleRows] at hrow
  | cons target word ih =>
    obtain ⟨moves, rest, nextGap, pre, rfl, _, _, hnext, hrest⟩ := htrace
    change row ∈ updateRows satellite moves (renderedBase background labels cuts gap) ++
      scheduleRows satellite rest (updateEnd moves (renderedBase background labels cuts gap)) at hrow
    rcases List.mem_append.mp hrow with hfirst | hlater
    · obtain ⟨i, _, hi⟩ := updateRows_base satellite moves _ row hfirst
      refine ⟨[], target, word, gap + i, rfl, ?_⟩
      rw [hi]
      simp only [renderedBase, executeLabels, executeCuts, fullIterate_formula, rotateLeft_add]
    · rw [hnext] at hlater
      obtain ⟨initialWord, target', tail, newGap, hword, hbase⟩ :=
        ih (updateLabels target.val labels) (advanceCuts hM target cuts) nextGap rest hrest hlater
      refine ⟨target :: initialWord, target', tail, newGap, ?_, hbase⟩
      simp only [List.cons_append, hword]

end CoefficientTwoPrecision.TargetTrace

#print axioms CoefficientTwoPrecision.TargetTrace.exists_trace
#print axioms CoefficientTwoPrecision.TargetTrace.trace_endpoint
#print axioms CoefficientTwoPrecision.TargetTrace.row_prefix_state
