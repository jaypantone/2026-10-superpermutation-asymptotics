import Quantitative.NormalSegments
import Quantitative.FiniteProgram

/-!
# Row counts and exact splits of actual bounded traces

A trace bounds every sweep by the length of its stationary circle. Hence a
batch with k target updates has at most k(M+k) actual rows. The append lemma
retains the same middle state and the exact two pieces of the sweep list.
-/

namespace CoefficientTwoPrecision.TraceRowBounds

open SuperpermutationUpperBound PositiveParking LiteralState StationaryCircle
open LiteralSchedule PositiveSchedule TargetTrace TraceComposition TraceSteps
open TraceLocalSimplicity BatchSafety ActualCyclicMatching NormalSegments
open MacroCatalogue FiniteProgram

variable {M k : ℕ} {α : Type}

private theorem bounded_sum (sweeps : List ℕ) (B : ℕ)
    (hbound : ∀ i < sweeps.length, movesAt sweeps i + 1 ≤ B) :
    sweeps.sum + sweeps.length ≤ sweeps.length * B := by
  induction sweeps with
  | nil => simp
  | cons moves rest ih =>
    have hfirst : moves + 1 ≤ B := by simpa [movesAt] using hbound 0 (by simp)
    have htail : ∀ i < rest.length, movesAt rest i + 1 ≤ B := by
      intro i hi
      simpa [movesAt] using hbound (i + 1) (by simp only [List.length_cons]; omega)
    have hh := ih htail
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- This bound concerns the original emitted row list of the supplied trace. -/
theorem trace_rows_le (hM : 2 ≤ M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option ℕ → α) (cuts : Fin k → Fin M)
    (gap : ℕ) (sweeps : List ℕ) (finalGap : ℕ)
    (htrace : Trace (by omega) background word labels cuts gap sweeps finalGap)
    (hlen : (renderedBase background labels cuts gap).length = M + k + 1)
    (satellite : α) :
    (scheduleRows satellite sweeps (renderedBase background labels cuts gap)).length ≤
      word.length * (M + k) := by
  have hsweeps := trace_length (show 0 < M by omega) background word labels cuts gap sweeps finalGap htrace
  have hbound : ∀ i < sweeps.length, movesAt sweeps i + 1 ≤ M + k := by
    intro i hi
    obtain ⟨middleGap, pre, hbase, hmoves, _⟩ := trace_step (show 0 < M by omega)
      background word labels cuts gap sweeps finalGap i htrace (by omega)
    have hcurrent := (baseAt_perm hM background word labels cuts gap sweeps finalGap i htrace).length_eq.trans hlen
    rw [hbase] at hcurrent
    simp only [renderedBase, List.length_append, List.length_singleton,
      LiteralState.rotateLeft_eq_rotate, List.length_rotate] at hcurrent
    omega
  rw [scheduleRows_length]
  simpa only [hsweeps] using bounded_sum sweeps (M + k) hbound

/-- The final rendered base of the same trace retains the actual alphabet. -/
theorem endpoint_properties (hM : 2 ≤ M) (background : Fin M → α)
    (word : List (Fin k)) (labels : Option ℕ → α) (cuts : Fin k → Fin M)
    (gap : ℕ) (sweeps : List ℕ) (finalGap : ℕ)
    (htrace : Trace (by omega) background word labels cuts gap sweeps finalGap)
    (hnd : (renderedBase background labels cuts gap).Nodup)
    (hlen : (renderedBase background labels cuts gap).length = M + k + 1) :
    (renderedBase background (executeLabels word labels) (executeCuts (by omega) word cuts) finalGap).Nodup ∧
      (renderedBase background (executeLabels word labels) (executeCuts (by omega) word cuts) finalGap).length =
        M + k + 1 := by
  have hp := RowValidity.scheduleEnd_perm sweeps _
    (trace_suffixSchedule hM background word labels cuts gap sweeps finalGap htrace)
  rw [trace_endpoint (show 0 < M by omega) background word labels cuts gap sweeps finalGap htrace] at hp
  exact ⟨hp.nodup_iff.mpr hnd, hp.length_eq.trans hlen⟩

/-- Split at a literal target-word append, including the exact sweep lists. -/
theorem split_append (hM : 0 < M) (background : Fin M → α)
    (first last : List (Fin k)) (labels : Option ℕ → α) (cuts : Fin k → Fin M)
    (gap : ℕ) (sweeps : List ℕ) (finalGap : ℕ)
    (htrace : Trace hM background (first ++ last) labels cuts gap sweeps finalGap) :
    ∃ firstSweeps lastSweeps middleGap,
      sweeps = firstSweeps ++ lastSweeps ∧
      Trace hM background first labels cuts gap firstSweeps middleGap ∧
      Trace hM background last (executeLabels first labels) (executeCuts hM first cuts)
        middleGap lastSweeps finalGap := by
  obtain ⟨middleGap, hfirst, hlast⟩ := trace_split hM background (first ++ last)
    labels cuts gap sweeps finalGap first.length htrace
  refine ⟨sweeps.take first.length, sweeps.drop first.length, middleGap,
    (List.take_append_drop _ _).symm, ?_, ?_⟩
  · simpa only [List.take_left] using hfirst
  · simpa only [List.take_left, List.drop_left] using hlast

/-- The two row counts add at the actual middle rendered base. -/
theorem rows_append_length (hM : 0 < M) (background : Fin M → α)
    (first : List (Fin k)) (labels : Option ℕ → α) (cuts : Fin k → Fin M)
    (gap : ℕ) (firstSweeps lastSweeps : List ℕ) (middleGap : ℕ)
    (hfirst : Trace hM background first labels cuts gap firstSweeps middleGap) (satellite : α) :
    (scheduleRows satellite (firstSweeps ++ lastSweeps) (renderedBase background labels cuts gap)).length =
      (scheduleRows satellite firstSweeps (renderedBase background labels cuts gap)).length +
      (scheduleRows satellite lastSweeps (renderedBase background (executeLabels first labels)
        (executeCuts hM first cuts) middleGap)).length := by
  rw [scheduleRows_append, List.length_append,
    trace_endpoint hM background first labels cuts gap firstSweeps middleGap hfirst]

theorem program_word_length (k : ℕ) (program : List Macro) :
    (FiniteProgram.word k program).length = batchCount program * k := by
  induction program with
  | nil => simp [FiniteProgram.word, FiniteProgram.batches, MacroCatalogue.batchCount]
  | cons instruction rest ih =>
    cases instruction with
    | normal =>
      change (List.finRange k ++ FiniteProgram.word k rest).length = (1 + batchCount rest) * k
      rw [List.length_append, List.length_finRange, ih]
      ring
    | parking choice =>
      have hmenu : (finiteMenu k choice).length = k := by
        simpa only [List.length_finRange] using (finiteMenu_perm k choice).length_eq
      change (finiteMenu k choice ++ ((finiteMenu k choice).reverse ++ FiniteProgram.word k rest)).length =
        (2 + batchCount rest) * k
      rw [List.length_append, List.length_append, List.length_reverse, hmenu, ih]
      ring

theorem word_replicate_normal (k total : ℕ) :
    FiniteProgram.word k (List.replicate total Macro.normal) = repeatWord total (List.finRange k) := by
  induction total with
  | zero => rfl
  | succ total ih =>
    change List.finRange k ++ FiniteProgram.word k (List.replicate total Macro.normal) = _
    rw [ih]
    rfl

/-- Every complete actual macro program advances all cuts equally. -/
theorem program_cuts [NeZero M] (hM : 0 < M) (program : List Macro)
    (cuts : Fin k → Fin M) (translation : Fin M) :
    executeCuts hM (FiniteProgram.word k program) (fun i => cuts i + translation) =
      fun i => cuts i + (translationCut (batchCount program : ZMod M) + translation) := by
  funext i
  apply cutValue_injective
  rw [executeCuts_value, FiniteProgram.word_count, cutValue_add, cutValue_add,
    cutValue_add, translationCut_value]
  ring

/-- The ordinary row count of a clean batch is below the same bound as
an arbitrary changed batch, without adding their two bounds together. -/
theorem normal_batch_le (M k : ℕ) (hk : 0 < k) (hM : k + 1 ≤ M) :
    (k - 1) * M + k * (k + 1) + 1 ≤ k * (M + k) := by
  have hsplit : (k - 1) * M + M = k * M := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel (show 1 ≤ k by omega)]
  nlinarith only [hsplit, hM]

end CoefficientTwoPrecision.TraceRowBounds

#print axioms CoefficientTwoPrecision.TraceRowBounds.trace_rows_le
#print axioms CoefficientTwoPrecision.TraceRowBounds.endpoint_properties
#print axioms CoefficientTwoPrecision.TraceRowBounds.split_append
#print axioms CoefficientTwoPrecision.TraceRowBounds.program_cuts
