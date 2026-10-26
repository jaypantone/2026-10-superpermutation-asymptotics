import Quantitative.MacroCatalogue
import Mathlib.Data.List.Count

/-!
# Actual literal rows belong to the finite joint envelope

The envelope reconstructs a base from a joint catalogue state, one common
cut translation, and one mobile gap. The containment theorem starts with
the actual recursive target trace and its actual emitted Row list. Its
only program premise is the syntactic target word assembled from normal
and parking macros. Literal containment is the conclusion.
-/

namespace CoefficientTwoPrecision.LiteralEnvelope

open PositiveParking JointStates LiteralSchedule PositiveSchedule TargetTrace MacroCatalogue
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type}

/-- Executing symbolic roles commutes with assigning actual symbol names. -/
theorem execute_pullback (word : List Nat) (initial : Option Nat → α) (roles : Assignment) :
    execute updateLabels word (fun p => initial (roles p)) =
      fun p => initial (execute updateLabels word roles p) := by
  induction word generalizing roles with
  | nil => rfl
  | cons target rest ih => exact ih (updateLabels target roles)

def Envelope (background : Fin M → α) (initial : Option Nat → α)
    (initialCuts : Fin k → Fin M) (source : List α) : Prop :=
  ∃ state ∈ catalogue k (List.range k), ∃ translation : Nat,
    ∃ cuts : Fin k → Fin M, ∃ gap : Nat,
      source = renderedBase background (fun p => initial (state.labels p)) cuts gap ∧
      ∀ j, (cuts j).val = ((initialCuts j).val + translation + state.phases j.val) % M

/-- A constructed source row has a catalogue state, including the exact
correlation between the role prefix and the cut-phase prefix. -/
theorem actual_row_mem (hM : 0 < M) (background : Fin M → α)
    (program : List Macro) (word : List (Fin k))
    (hprogram : word.map Fin.val = programWord k program)
    (initial : Option Nat → α) (initialCuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace hM background word initial initialCuts gap sweeps finalGap)
    (satellite : α) (row : Row α)
    (hrow : row ∈ scheduleRows satellite sweeps (renderedBase background initial initialCuts gap)) :
    Envelope background initial initialCuts row.base := by
  obtain ⟨pre, target, tail, rowGap, hword, hbase⟩ :=
    row_prefix_state hM background word initial initialCuts gap sweeps finalGap htrace satellite row hrow
  have hn : pre.length < (programWord k program).length := by
    rw [← hprogram, List.length_map, hword, List.length_append, List.length_cons]
    omega
  have htake : (programWord k program).take pre.length = pre.map Fin.val := by
    rw [← hprogram, hword, List.map_append, List.map_cons]
    apply List.take_left'
    simp only [List.length_map]
  obtain ⟨state, hstate, translation, hroles, hcounts⟩ := proper_prefix_state k program pre.length hn
  rw [htake] at hroles hcounts
  have hlabels : executeLabels pre initial = fun p => initial (state.labels p) := by
    rw [executeLabels_eq_execute]
    have h := execute_pullback (pre.map Fin.val) initial (id : Assignment)
    rw [hroles] at h
    exact h
  refine ⟨state, hstate, translation, executeCuts hM pre initialCuts, rowGap, ?_, ?_⟩
  · rw [hbase, hlabels]
  · intro j
    rw [executeCuts_count]
    have hc := hcounts j.val j.isLt
    rw [List.count_map_of_injective pre Fin.val Fin.val_injective j] at hc
    rw [hc, Nat.add_assoc]

end CoefficientTwoPrecision.LiteralEnvelope

#print axioms CoefficientTwoPrecision.LiteralEnvelope.actual_row_mem
