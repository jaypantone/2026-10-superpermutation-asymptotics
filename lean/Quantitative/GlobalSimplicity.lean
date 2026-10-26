import Quantitative.NearbyBlocks
import Quantitative.DoubleTrace
import Quantitative.BatchTime

/-!
# Pairwise cyclic distinctness of the complete actual source contour

There are exactly M complete batches. Robust matching forces equal cyclic
source bases into equal or neighbouring batch times. Ordinary neighbours
are excluded by the actual interval and adjacent-block theorems. The
last/first batch comparison is moved into the two consecutive middle
batches of the doubled literal trace. Finally the indexed block lists are
flattened, preserving every source occurrence.
-/

namespace CoefficientTwoPrecision.GlobalSimplicity

open LiteralSchedule PositiveSchedule TargetTrace TraceSteps TraceLocalSimplicity
open ActualPrefix NearbyBlocks DoubleTrace BatchTime RobustMatching BatchSafety
open SuperpermutationUpperBound

variable {M k : Nat} {Control α : Type} [DecidableEq α]

theorem complete_batches_count (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k)) (target : Fin k) :
    batches.flatten.count target = batches.length := by
  induction batches with
  | nil => rfl
  | cons order batches ih =>
    have horder := horders order (by simp)
    have hcount : order.count target = 1 := by
      rw [horder.count_eq]
      exact List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange target)
    have htail := ih (fun next hnext => horders next (by simp [hnext]))
    simp only [List.flatten_cons, List.count_append, hcount, htail, List.length_cons]
    omega

theorem distinct_blocks_disjoint (hM : 3 ≤ M) (hk : 3 ≤ k)
    (backgroundTest : α → Bool) (background : Fin M → α) (embed : Control → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htestBackground : ∀ i, backgroundTest (background i) = true)
    (htestControl : ∀ c, backgroundTest (embed c) = false)
    (assignment : FiniteRoles.Role k ≃ Control) (cuts : Fin k → Fin M)
    (hrobust : Robust (fun j => cutValue (cuts j)))
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k)) (hnumber : batches.length = M)
    (gap : Nat) (sweeps : List Nat) (finalGap first last : Nat)
    (htrace : Trace (by omega) background batches.flatten
      (fun p => embed (FiniteRoles.lift assignment p)) cuts gap sweeps finalGap)
    (hlabels : executeLabels batches.flatten (fun p => embed (FiniteRoles.lift assignment p)) =
      (fun p => embed (FiniteRoles.lift assignment p)))
    (hclosed : scheduleEnd sweeps
      (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap) =
      renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap)
    (horder : first < last) (hlast : last < batches.flatten.length)
    (satellite : α) (firstRow lastRow : Row α)
    (hfirstRow : firstRow ∈ blockAt satellite sweeps
      (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap) first)
    (hlastRow : lastRow ∈ blockAt satellite sweeps
      (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap) last) :
    ¬ firstRow.base.IsRotated lastRow.base := by
  intro hcyclic
  have hfirst : first < batches.flatten.length := by omega
  obtain ⟨firstGap, hfirstBase⟩ := block_prefixBase (show 0 < M by omega) background embed assignment
    batches.flatten cuts gap sweeps finalGap first htrace hfirst satellite firstRow hfirstRow
  obtain ⟨lastGap, hlastBase⟩ := block_prefixBase (show 0 < M by omega) background embed assignment
    batches.flatten cuts gap sweeps finalGap last htrace hlast satellite lastRow hlastRow
  have hcyclicPrefix := hcyclic
  rw [hfirstBase, hlastBase] at hcyclicPrefix
  have hnear := equal_prefix_times (show 0 < M by omega) hk backgroundTest background embed
    hbackground hembed htestBackground htestControl assignment cuts hrobust batches horders
    first last firstGap lastGap hfirst.le hlast.le hcyclicPrefix
  have htimeFirst := batch_time_lt (by omega : 0 < k) batches horders hnumber first hfirst
  have htimeLast := batch_time_lt (by omega : 0 < k) batches horders hnumber last hlast
  have htimeOrder : first / k ≤ last / k := Nat.div_le_div_right horder.le
  rcases ordered_neighbor_times hM (first / k) (last / k) htimeFirst htimeLast htimeOrder hnear with
    hconsecutive | hwrap
  · exact nearby_blocks_disjoint hM hk backgroundTest background embed hbackground hembed
      htestBackground htestControl assignment cuts hrobust batches horders gap sweeps finalGap
      first last htrace horder hlast hconsecutive satellite firstRow lastRow hfirstRow hlastRow hcyclic
  · have hlength := trace_length (show 0 < M by omega) background batches.flatten
      (fun p => embed (FiniteRoles.lift assignment p)) cuts gap sweeps finalGap htrace
    have hwordLength : batches.flatten.length = M * k := by
      rw [batches_length batches horders, hnumber]
    have hsweepsLength : sweeps.length = M * k := hlength.trans hwordLength
    have hwordNe : batches.flatten ≠ [] := by
      intro hnil
      simp only [hnil, List.length_nil] at hlast
      omega
    have hcounts : ∀ target, batches.flatten.count target = M := by
      intro target
      rw [complete_batches_count batches horders target, hnumber]
    have hcutReturn := executeCuts_closed (show 0 < M by omega) batches.flatten cuts hcounts
    have hdoubleTrace := double_closed_trace (show 0 < M by omega) background batches.flatten hwordNe
      (fun p => embed (FiniteRoles.lift assignment p)) cuts gap sweeps finalGap htrace hlabels hcutReturn hclosed
    have hdoubleOrders : ∀ order ∈ batches ++ batches, order.Perm (List.finRange k) := by
      intro order hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact horders order hmem
      · exact horders order hmem
    have hdouble : Trace (show 0 < M by omega) background (batches ++ batches).flatten
        (fun p => embed (FiniteRoles.lift assignment p)) cuts gap (sweeps ++ sweeps) finalGap := by
      simpa only [List.flatten_append] using hdoubleTrace
    have hindexOrder : last < sweeps.length + first := by omega
    have hindexLast : sweeps.length + first < (batches ++ batches).flatten.length := by
      rw [List.flatten_append, List.length_append]
      omega
    have hconsecutive : (sweeps.length + first) / k ≤ last / k + 1 := by
      rw [hsweepsLength, shifted_batch_div (by omega), hwrap.1, hwrap.2]
      omega
    have hlastCopied : lastRow ∈ blockAt satellite (sweeps ++ sweeps)
        (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap) last := by
      rw [blockAt_double_left satellite sweeps _ last (by omega)]
      exact hlastRow
    have hfirstCopied : firstRow ∈ blockAt satellite (sweeps ++ sweeps)
        (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap)
          (sweeps.length + first) := by
      rw [blockAt_double_right satellite sweeps _ first hclosed]
      exact hfirstRow
    exact nearby_blocks_disjoint hM hk backgroundTest background embed hbackground hembed
      htestBackground htestControl assignment cuts hrobust (batches ++ batches) hdoubleOrders
      gap (sweeps ++ sweeps) finalGap last (sweeps.length + first) hdouble hindexOrder hindexLast
      hconsecutive satellite lastRow firstRow hlastCopied hfirstCopied hcyclic.symm

/-- Every source occurrence in the actual complete closed contour has a
different cyclic base. All local and cross-boundary cases are discharged. -/
theorem scheduleRows_pairwise (hM : 3 ≤ M) (hk : 3 ≤ k)
    (backgroundTest : α → Bool) (background : Fin M → α) (embed : Control → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htestBackground : ∀ i, backgroundTest (background i) = true)
    (htestControl : ∀ c, backgroundTest (embed c) = false)
    (assignment : FiniteRoles.Role k ≃ Control) (cuts : Fin k → Fin M)
    (hrobust : Robust (fun j => cutValue (cuts j)))
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k)) (hnumber : batches.length = M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background batches.flatten
      (fun p => embed (FiniteRoles.lift assignment p)) cuts gap sweeps finalGap)
    (hlabels : executeLabels batches.flatten (fun p => embed (FiniteRoles.lift assignment p)) =
      (fun p => embed (FiniteRoles.lift assignment p)))
    (hclosed : scheduleEnd sweeps
      (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap) =
      renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap)
    (satellite : α) :
    (scheduleRows satellite sweeps
      (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap)).Pairwise
        (fun first last => ¬ first.base.IsRotated last.base) := by
  have hlength := trace_length (show 0 < M by omega) background batches.flatten
    (fun p => embed (FiniteRoles.lift assignment p)) cuts gap sweeps finalGap htrace
  have hnd := initial_nodup backgroundTest background embed hbackground hembed htestBackground
    htestControl assignment cuts gap
  rw [rows_eq_blocks]
  apply List.pairwise_flatMap.mpr
  constructor
  · intro n hn
    have hn' : n < sweeps.length := List.mem_range.mp hn
    exact block_cyclicDistinct (by omega) background batches.flatten
      (fun p => embed (FiniteRoles.lift assignment p)) cuts gap sweeps finalGap n htrace (by omega) hnd satellite
  · have hindices : (List.range sweeps.length).Pairwise (fun i j => i < j) := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      simpa only [List.getElem_range] using hij
    apply List.Pairwise.imp_of_mem _ hindices
    intro first last hfirst hlast horder firstRow hfirstRow lastRow hlastRow
    have hlast' : last < sweeps.length := List.mem_range.mp hlast
    exact distinct_blocks_disjoint hM hk backgroundTest background embed hbackground hembed
      htestBackground htestControl assignment cuts hrobust batches horders hnumber gap sweeps finalGap
      first last htrace hlabels hclosed horder (by omega) satellite firstRow lastRow hfirstRow hlastRow

end CoefficientTwoPrecision.GlobalSimplicity

#print axioms CoefficientTwoPrecision.GlobalSimplicity.distinct_blocks_disjoint
#print axioms CoefficientTwoPrecision.GlobalSimplicity.scheduleRows_pairwise
