import Quantitative.TranslatedRenderer
import Quantitative.LiteralEnvelope
import Quantitative.BatchPrefixes
import Quantitative.ActualCyclicMatching
import Quantitative.SourceProjection

/-!
# Keeping the safe cyclic cut in canonical event coordinates

The local construction may index its background from a safe cut. The
offset is retained explicitly. Every actual local row is the identical
literal row in the canonical background with all stationary cuts shifted
by that offset. At batch time t its canonical time is origin+t.
-/

namespace CoefficientTwoPrecision.OriginTransport

open LiteralState StationaryCircle LiteralSchedule PositiveSchedule TargetTrace
open BatchSafety BatchPrefixes RobustSafety LiteralEnvelope ActualCyclicMatching
open SuperpermutationUpperBound

variable {M k : Nat} {α : Type} [NeZero M]

def shiftedBackground (background : Fin M → α) (origin : Fin M) : Fin M → α :=
  fun i => background (i + origin)

theorem shifted_injective (background : Fin M → α) (hbackground : Function.Injective background)
    (origin : Fin M) : Function.Injective (shiftedBackground background origin) := by
  intro i j heq
  exact add_right_cancel (hbackground heq)

theorem shifted_range (background : Fin M → α) (origin : Fin M) (symbol : α) :
    (∃ i, shiftedBackground background origin i = symbol) ↔ ∃ i, background i = symbol := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i + origin, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨i - origin, ?_⟩
    simpa only [shiftedBackground, sub_add_cancel] using hi

theorem shifted_list (background : Fin M → α) (origin : Fin M) :
    (List.finRange M).map (shiftedBackground background origin) =
      rot ((List.finRange M).map background) origin.val := by
  change (List.finRange M).map (background ∘ (fun i => i + origin)) = _
  rw [← List.map_map, TranslatedControlOrder.finRange_translate, List.map_rotate]
  change _ = ((List.finRange M).map background).rotateLeft origin.val
  rw [LiteralState.rotateLeft_eq_rotate]

theorem rendered_base_canonical (background : Fin M → α) (origin : Fin M)
    (labels : Option Nat → α) (cuts : Fin k → Fin M) (gap : Nat) :
    ∃ canonicalGap,
      renderedBase (shiftedBackground background origin) labels cuts gap =
        renderedBase background labels (fun i => cuts i + origin) canonicalGap := by
  obtain ⟨offset, hrotation⟩ := TranslatedRenderer.render_translate background (residents labels) cuts origin
  have hlocal : render (shiftedBackground background origin) (residents labels) cuts =
      (render background (residents labels) (fun i => cuts i + origin)).rotateLeft offset := by
    rw [LiteralState.rotateLeft_eq_rotate]
    exact hrotation.symm
  refine ⟨offset + gap, ?_⟩
  simp only [renderedBase, hlocal, rotateLeft_add]

theorem envelope_canonical (background : Fin M → α) (origin : Fin M)
    (initial : Option Nat → α) (initialCuts : Fin k → Fin M) (source : List α)
    (hsource : Envelope (shiftedBackground background origin) initial initialCuts source) :
    Envelope background initial initialCuts source := by
  obtain ⟨state, hstate, translation, cuts, gap, hbase, hcuts⟩ := hsource
  obtain ⟨canonicalGap, hcanonical⟩ := rendered_base_canonical background origin
    (fun p => initial (state.labels p)) cuts gap
  refine ⟨state, hstate, translation + origin.val, (fun i => cuts i + origin), canonicalGap,
    hbase.trans hcanonical, ?_⟩
  intro j
  rw [Fin.val_add, hcuts, Nat.mod_add_mod]
  congr 1
  omega

theorem canonical_row_prefix (hM : 0 < M) (background : Fin M → α) (origin : Fin M)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace hM (shiftedBackground background origin) word labels cuts gap sweeps finalGap)
    (satellite : α) (row : Row α)
    (hrow : row ∈ scheduleRows satellite sweeps
      (renderedBase (shiftedBackground background origin) labels cuts gap)) :
    ∃ pre : List (Fin k), ∃ target tail canonicalGap,
      word = pre ++ target :: tail ∧
      row.base = renderedBase background (executeLabels pre labels)
        (fun i => executeCuts hM pre cuts i + origin) canonicalGap := by
  obtain ⟨pre, target, tail, rowGap, hword, hbase⟩ :=
    row_prefix_state hM (shiftedBackground background origin) word labels cuts gap sweeps finalGap
      htrace satellite row hrow
  obtain ⟨canonicalGap, hcanonical⟩ := rendered_base_canonical background origin
    (executeLabels pre labels) (executeCuts hM pre cuts) rowGap
  exact ⟨pre, target, tail, canonicalGap, hword, hbase.trans hcanonical⟩

/-- The canonical event coordinate is origin plus the actual batch
index. The offset is not absorbed into the fixed frame q. -/
theorem canonical_prefix_time (hM : 0 < M) (hk : 0 < k) (origin : Fin M)
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (n : Nat) (hn : n ≤ batches.flatten.length) (cuts : Fin k → Fin M) :
    Represents (fun j => cutValue (cuts j)) (cutValue origin + (n / k : Nat))
      (prefixPhases batches n)
      (fun j => executeCuts hM (batches.flatten.take n) cuts j + origin) := by
  have hprefix := represents_prefix hM hk batches horders n hn cuts
  intro j
  rw [cutValue_add, hprefix j]
  unfold perturbed
  ring

end CoefficientTwoPrecision.OriginTransport

#print axioms CoefficientTwoPrecision.OriginTransport.envelope_canonical
#print axioms CoefficientTwoPrecision.OriginTransport.canonical_row_prefix
#print axioms CoefficientTwoPrecision.OriginTransport.canonical_prefix_time
