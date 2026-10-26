import Quantitative.AdjacentBlocks
import Quantitative.ActualInterval

/-!
# Distinct update blocks in the same or consecutive batches

Each actual indexed block is converted to its specified finite-prefix
state. If two rows agree cyclically, the actual intervening target list
has length zero or one. For distinct indices only length one remains,
and the already proved adjacent-block exclusion applies.
-/

namespace CoefficientTwoPrecision.NearbyBlocks

open LiteralState LiteralSchedule PositiveSchedule TargetTrace TraceSteps
open ActualPrefix ActualInterval RobustMatching BatchSafety
open SuperpermutationUpperBound

variable {M k : Nat} {Control α : Type}

theorem initial_nodup [DecidableEq α] (backgroundTest : α → Bool)
    (background : Fin M → α) (embed : Control → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htestBackground : ∀ i, backgroundTest (background i) = true)
    (htestControl : ∀ c, backgroundTest (embed c) = false)
    (assignment : FiniteRoles.Role k ≃ Control) (cuts : Fin k → Fin M) (gap : Nat) :
    (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap).Nodup := by
  have heq := rendered_execute_eq background embed assignment [] cuts gap
  simp only [executeLabels, FiniteRoles.execute] at heq
  rw [heq]
  exact ActualMatching.base_nodup backgroundTest background embed hbackground hembed
    htestBackground htestControl assignment cuts gap

/-- The index here is the specified update-block index, not an index
chosen merely from existential membership in the full row list. -/
theorem block_prefixBase (hM : 0 < M) (background : Fin M → α) (embed : Control → α)
    (assignment : FiniteRoles.Role k ≃ Control) (word : List (Fin k))
    (cuts : Fin k → Fin M) (gap : Nat) (sweeps : List Nat) (finalGap n : Nat)
    (htrace : Trace hM background word (fun p => embed (FiniteRoles.lift assignment p))
      cuts gap sweeps finalGap) (hn : n < word.length) (satellite : α) (row : Row α)
    (hrow : row ∈ blockAt satellite sweeps
      (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap) n) :
    ∃ rowGap, row.base = prefixBase hM background embed assignment word cuts n rowGap := by
  obtain ⟨middleGap, pre, hbase, _, _⟩ :=
    trace_step hM background word _ cuts gap sweeps finalGap n htrace hn
  obtain ⟨i, _, hrowBase⟩ := updateRows_base satellite (movesAt sweeps n) _ row hrow
  refine ⟨middleGap + i, ?_⟩
  rw [hrowBase, hbase]
  change fullIterate i
    ((StationaryCircle.render background
      (residents (executeLabels (word.take n) (fun p => embed (FiniteRoles.lift assignment p))))
      (executeCuts hM (word.take n) cuts)).rotateLeft middleGap ++
        [executeLabels (word.take n) (fun p => embed (FiniteRoles.lift assignment p)) none]) = _
  rw [fullIterate_formula, rotateLeft_add]
  exact rendered_execute_eq background embed assignment (word.take n)
    (executeCuts hM (word.take n) cuts) (middleGap + i)

theorem nearby_blocks_disjoint [DecidableEq α] (hM : 3 ≤ M) (hk : 3 ≤ k)
    (backgroundTest : α → Bool) (background : Fin M → α) (embed : Control → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htestBackground : ∀ i, backgroundTest (background i) = true)
    (htestControl : ∀ c, backgroundTest (embed c) = false)
    (assignment : FiniteRoles.Role k ≃ Control) (cuts : Fin k → Fin M)
    (hrobust : Robust (fun j => cutValue (cuts j)))
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (gap : Nat) (sweeps : List Nat) (finalGap first last : Nat)
    (htrace : Trace (by omega) background batches.flatten
      (fun p => embed (FiniteRoles.lift assignment p)) cuts gap sweeps finalGap)
    (horder : first < last) (hlast : last < batches.flatten.length)
    (hconsecutive : last / k ≤ first / k + 1)
    (satellite : α) (firstRow lastRow : Row α)
    (hfirstRow : firstRow ∈ blockAt satellite sweeps
      (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap) first)
    (hlastRow : lastRow ∈ blockAt satellite sweeps
      (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap) last) :
    ¬ firstRow.base.IsRotated lastRow.base := by
  intro hcyclic
  obtain ⟨firstGap, hfirstBase⟩ := block_prefixBase (show 0 < M by omega) background embed assignment
    batches.flatten cuts gap sweeps finalGap first htrace (by omega) satellite firstRow hfirstRow
  obtain ⟨lastGap, hlastBase⟩ := block_prefixBase (show 0 < M by omega) background embed assignment
    batches.flatten cuts gap sweeps finalGap last htrace hlast satellite lastRow hlastRow
  have hcyclicPrefix := hcyclic
  rw [hfirstBase, hlastBase] at hcyclicPrefix
  have hinterval := repeated_interval_empty_or_single hM hk backgroundTest background embed
    hbackground hembed htestBackground htestControl assignment cuts hrobust batches horders
    first last firstGap lastGap horder.le hlast.le hconsecutive hcyclicPrefix
  have hlength : ((batches.flatten.drop first).take (last - first)).length = last - first := by
    apply List.length_take_of_le
    rw [List.length_drop]
    omega
  have hnext : last = first + 1 := by
    rcases hinterval with hnil | ⟨target, hsingle⟩
    · rw [hnil, List.length_nil] at hlength
      omega
    · rw [hsingle, List.length_singleton] at hlength
      omega
  have hnd := initial_nodup backgroundTest background embed hbackground hembed
    htestBackground htestControl assignment cuts gap
  apply AdjacentBlocks.adjacent_blocks_disjoint hM (by omega) background hbackground
    (fun p => embed (FiniteRoles.lift assignment p)) cuts hrobust batches horders
    gap sweeps finalGap first htrace (by omega) hnd satellite firstRow lastRow hfirstRow
      (by simpa only [hnext] using hlastRow)
  exact hcyclic

end CoefficientTwoPrecision.NearbyBlocks

#print axioms CoefficientTwoPrecision.NearbyBlocks.block_prefixBase
#print axioms CoefficientTwoPrecision.NearbyBlocks.nearby_blocks_disjoint
