import Quantitative.ActualPrefix

/-!
# A genuine repeated-source interval has zero or one target updates

Both endpoint states below are extracted from one actual flattened batch
word. The intervening target word is its concrete drop/take interval.
Robust matching, finite role comparison, and the proved count bounds
leave only an empty interval or a single short update.
-/

namespace CoefficientTwoPrecision.ActualInterval

open LiteralSchedule PositiveSchedule BatchSafety BatchPrefixes RobustMatching
open ActualPrefix CutPersistence

variable {M k : Nat} {Control α : Type} [DecidableEq α]

theorem finite_execute_append (first last : List (Fin k))
    (assignment : FiniteRoles.Role k ≃ Control) :
    FiniteRoles.execute (first ++ last) assignment =
      FiniteRoles.execute last (FiniteRoles.execute first assignment) := by
  induction first generalizing assignment with
  | nil => rfl
  | cons target rest ih => exact ih (FiniteRoles.update target assignment)

theorem repeated_interval_empty_or_single (hM : 3 ≤ M) (hk : 3 ≤ k)
    (backgroundTest : α → Bool) (background : Fin M → α) (embed : Control → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htestBackground : ∀ i, backgroundTest (background i) = true)
    (htestControl : ∀ c, backgroundTest (embed c) = false)
    (assignment : FiniteRoles.Role k ≃ Control) (cuts : Fin k → Fin M)
    (hrobust : Robust (fun j => cutValue (cuts j)))
    (batches : List (List (Fin k)))
    (horders : ∀ order ∈ batches, order.Perm (List.finRange k))
    (first last firstGap lastGap : Nat) (horder : first ≤ last)
    (hlast : last ≤ batches.flatten.length) (hconsecutive : last / k ≤ first / k + 1)
    (hcyclic : (prefixBase (by omega) background embed assignment batches.flatten cuts first firstGap).IsRotated
      (prefixBase (by omega) background embed assignment batches.flatten cuts last lastGap)) :
    (batches.flatten.drop first).take (last - first) = [] ∨
      ∃ target, (batches.flatten.drop first).take (last - first) = [target] := by
  let interval := (batches.flatten.drop first).take (last - first)
  let firstRoles := FiniteRoles.execute (batches.flatten.take first) assignment
  let lastRoles := FiniteRoles.execute (batches.flatten.take last) assignment
  let firstCuts := executeCuts (show 0 < M by omega) (batches.flatten.take first) cuts
  let lastCuts := executeCuts (show 0 < M by omega) (batches.flatten.take last) cuts
  have hsplit : batches.flatten.take last = batches.flatten.take first ++ interval := by
    have heq : last = first + (last - first) := by omega
    conv_lhs => rw [heq, List.take_add]
  have hfirstRep := represents_prefix (show 0 < M by omega) (by omega : 0 < k)
    batches horders first (by omega) cuts
  have hlastRep := represents_prefix (show 0 < M by omega) (by omega : 0 < k)
    batches horders last hlast cuts
  have hdiag := ActualMatching.all_matches_diagonal hk backgroundTest background embed
    hbackground hembed htestBackground htestControl _ hrobust
    firstRoles lastRoles firstCuts lastCuts firstGap lastGap
    (first / k : Nat) (last / k : Nat) (prefixPhases batches first) (prefixPhases batches last)
    hfirstRep hlastRep hcyclic
  have hroles : lastRoles = FiniteRoles.execute interval firstRoles := by
    dsimp only [lastRoles, firstRoles]
    rw [hsplit, finite_execute_append]
  have hcuts : lastCuts = executeCuts (show 0 < M by omega) interval firstCuts := by
    dsimp only [lastCuts, firstCuts]
    rw [hsplit, executeCuts_append]
  apply interval_empty_or_single hM interval firstRoles lastRoles firstCuts hroles hdiag
  · intro i hmatch
    have hc := ActualMatching.matched_cuts_eq backgroundTest background embed
      hbackground hembed htestBackground htestControl firstRoles lastRoles firstCuts lastCuts
      firstGap lastGap hcyclic i i hmatch
    rw [hcuts] at hc
    exact hc.symm
  · intro i
    exact consecutive_interval_count (by omega) batches horders first last horder hlast hconsecutive i

end CoefficientTwoPrecision.ActualInterval

#print axioms CoefficientTwoPrecision.ActualInterval.repeated_interval_empty_or_single
