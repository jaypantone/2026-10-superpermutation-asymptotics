import Quantitative.ActualMatching
import Quantitative.BatchPrefixes
import Quantitative.TargetTrace
import Quantitative.FiniteRoleExecution

/-!
# Actual source rows have chronological finite role assignments

This module connects the concrete row trace to finite bijective role
assignments at target-word indices. Equal cyclic source bases then have
the same or neighbouring batch times modulo the background length.
-/

namespace CoefficientTwoPrecision.ActualPrefix

open LiteralSchedule PositiveSchedule TargetTrace BatchSafety BatchPrefixes RobustMatching
open SuperpermutationUpperBound

variable {M k : Nat} {Control α : Type}

theorem executeLabels_map (word : List (Fin k)) (labels : Option Nat → Control) (embed : Control → α) :
    executeLabels word (fun p => embed (labels p)) = fun p => embed (executeLabels word labels p) := by
  induction word generalizing labels with
  | nil => rfl
  | cons target rest ih => exact ih (PositiveParking.updateLabels target.val labels)

theorem rendered_execute_eq (background : Fin M → α) (embed : Control → α)
    (assignment : FiniteRoles.Role k ≃ Control) (word : List (Fin k))
    (cuts : Fin k → Fin M) (gap : Nat) :
    renderedBase background (executeLabels word (fun p => embed (FiniteRoles.lift assignment p))) cuts gap =
      ActualMatching.base background embed (FiniteRoles.execute word assignment) cuts gap := by
  have hagree := FiniteRoles.execute_lift_agrees word assignment
  have hresident : residents (k := k)
      (executeLabels word (fun p => embed (FiniteRoles.lift assignment p))) =
      ActualMatching.resident embed (FiniteRoles.execute word assignment) := by
    funext i
    rw [executeLabels_map]
    exact congrArg embed (hagree.2 i)
  have hmobile : executeLabels word (fun p => embed (FiniteRoles.lift assignment p)) none =
      embed (FiniteRoles.execute word assignment none) := by
    rw [executeLabels_map]
    exact congrArg embed hagree.1
  simp only [renderedBase, ActualMatching.base, hresident, hmobile]

def prefixBase (hM : 0 < M) (background : Fin M → α) (embed : Control → α)
    (assignment : FiniteRoles.Role k ≃ Control) (word : List (Fin k))
    (cuts : Fin k → Fin M) (n gap : Nat) : List α :=
  ActualMatching.base background embed (FiniteRoles.execute (word.take n) assignment)
    (executeCuts hM (word.take n) cuts) gap

/-- Every actual source occurrence has a genuine proper target prefix
and the finite bijection obtained by executing that prefix. -/
theorem row_prefixBase (hM : 0 < M) (background : Fin M → α) (embed : Control → α)
    (assignment : FiniteRoles.Role k ≃ Control) (word : List (Fin k))
    (cuts : Fin k → Fin M) (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace hM background word (fun p => embed (FiniteRoles.lift assignment p))
      cuts gap sweeps finalGap) (satellite : α) (row : Row α)
    (hrow : row ∈ scheduleRows satellite sweeps
      (renderedBase background (fun p => embed (FiniteRoles.lift assignment p)) cuts gap)) :
    ∃ n < word.length, ∃ rowGap,
      row.base = prefixBase hM background embed assignment word cuts n rowGap := by
  obtain ⟨pre, target, tail, rowGap, hword, hbase⟩ :=
    row_prefix_state hM background word _ cuts gap sweeps finalGap htrace satellite row hrow
  have hn : pre.length < word.length := by
    rw [hword, List.length_append, List.length_cons]
    omega
  have htake : word.take pre.length = pre := by
    rw [hword]
    exact List.take_left
  refine ⟨pre.length, hn, rowGap, ?_⟩
  rw [hbase, rendered_execute_eq]
  simp only [prefixBase, htake]

/-- Equality of actual cyclic prefix bases forces neighbouring batch
times. The binary cut phases are derived from the concrete complete
batches by `represents_prefix`. -/
theorem equal_prefix_times [DecidableEq α] (hM : 0 < M) (hk : 3 ≤ k)
    (backgroundTest : α → Bool) (background : Fin M → α) (embed : Control → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htestBackground : ∀ i, backgroundTest (background i) = true)
    (htestControl : ∀ c, backgroundTest (embed c) = false)
    (assignment : FiniteRoles.Role k ≃ Control) (cuts : Fin k → Fin M)
    (hrobust : Robust (fun j => cutValue (cuts j)))
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (first last firstGap lastGap : Nat)
    (hfirst : first ≤ batches.flatten.length) (hlast : last ≤ batches.flatten.length)
    (hcyclic : (prefixBase hM background embed assignment batches.flatten cuts first firstGap).IsRotated
      (prefixBase hM background embed assignment batches.flatten cuts last lastGap)) :
    ((last / k : Nat) : ZMod M) - (first / k : Nat) = 0 ∨
      ((last / k : Nat) : ZMod M) - (first / k : Nat) = 1 ∨
      ((last / k : Nat) : ZMod M) - (first / k : Nat) = -1 := by
  let firstRoles := FiniteRoles.execute (batches.flatten.take first) assignment
  let lastRoles := FiniteRoles.execute (batches.flatten.take last) assignment
  let firstCuts := executeCuts hM (batches.flatten.take first) cuts
  let lastCuts := executeCuts hM (batches.flatten.take last) cuts
  have hfirstRep := represents_prefix hM (by omega : 0 < k) batches horders first hfirst cuts
  have hlastRep := represents_prefix hM (by omega : 0 < k) batches horders last hlast cuts
  have hdiag := ActualMatching.all_matches_diagonal hk backgroundTest background embed
    hbackground hembed htestBackground htestControl _ hrobust
    firstRoles lastRoles firstCuts lastCuts firstGap lastGap
    (first / k : Nat) (last / k : Nat) (prefixPhases batches first) (prefixPhases batches last)
    hfirstRep hlastRep hcyclic
  obtain ⟨i, j, _, _, _, hmatch, _⟩ := FiniteRoles.two_matches hk firstRoles lastRoles
  have hij := hdiag i j hmatch
  subst j
  have hcut := ActualMatching.matched_cuts_eq backgroundTest background embed
    hbackground hembed htestBackground htestControl firstRoles lastRoles firstCuts lastCuts
    firstGap lastGap hcyclic i i hmatch
  have hc := congrArg cutValue hcut
  rw [hfirstRep i, hlastRep i] at hc
  dsimp only [RobustSafety.perturbed] at hc
  exact diagonal_time_difference (fun j => cutValue (cuts j))
    ((first / k : Nat) : ZMod M) ((last / k : Nat) : ZMod M) i
    (prefixPhases batches first i) (prefixPhases batches last i) hc

end CoefficientTwoPrecision.ActualPrefix

#print axioms CoefficientTwoPrecision.ActualPrefix.row_prefixBase
#print axioms CoefficientTwoPrecision.ActualPrefix.equal_prefix_times
