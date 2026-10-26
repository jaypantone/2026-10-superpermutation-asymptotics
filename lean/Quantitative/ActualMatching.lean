import Quantitative.CutExtraction
import Quantitative.FiniteRoles
import Quantitative.RobustMatching
import Quantitative.BatchSafety

/-!
# Equal actual source bases force diagonal stationary matches

Finite bijective role assignments supply shared named controls. The
concrete renderer and cyclic projection recover their background cuts.
Robust separation then forces every shared stationary label to retain
its physical slot, and the two batch translations differ by at most one.
-/

namespace CoefficientTwoPrecision.ActualMatching

open LiteralState StationaryCircle StationaryUpdate CutExtraction
open FiniteRoles RobustMatching BatchSafety

variable {M k : Nat} {Control α : Type} [DecidableEq α]

def resident (embed : Control → α) (assignment : FiniteRoles.Role k ≃ Control) : Fin k → α :=
  fun i => embed (assignment (some i))

def base (background : Fin M → α) (embed : Control → α)
    (assignment : FiniteRoles.Role k ≃ Control) (cuts : Fin k → Fin M) (gap : Nat) : List α :=
  (render background (resident embed assignment) cuts).rotateLeft gap ++ [embed (assignment none)]

theorem resident_injective (embed : Control → α) (hembed : Function.Injective embed)
    (assignment : FiniteRoles.Role k ≃ Control) : Function.Injective (resident embed assignment) := by
  intro i j h
  exact Option.some.inj (assignment.injective (hembed h))

theorem base_nodup (backgroundTest : α → Bool) (background : Fin M → α)
    (embed : Control → α) (hbackground : Function.Injective background)
    (hembed : Function.Injective embed)
    (htestBackground : ∀ i, backgroundTest (background i) = true)
    (htestControl : ∀ c, backgroundTest (embed c) = false)
    (assignment : FiniteRoles.Role k ≃ Control) (cuts : Fin k → Fin M) (gap : Nat) :
    (base background embed assignment cuts gap).Nodup := by
  have hcross : ∀ j i, resident embed assignment j ≠ background i := by
    intro j i h
    have ht := congrArg backgroundTest h
    simp only [resident, htestControl, htestBackground] at ht
    cases ht
  have hmb : ∀ i, background i ≠ embed (assignment none) := by
    intro i h
    have ht := congrArg backgroundTest h
    simp only [htestControl, htestBackground] at ht
    cases ht
  have hmr : ∀ j, resident embed assignment j ≠ embed (assignment none) := by
    intro j h
    have heq := assignment.injective (hembed h)
    cases heq
  have hnd := StationaryUpdate.base_nodup background (resident embed assignment) cuts
    hbackground (resident_injective embed hembed assignment) hcross
    (embed (assignment none)) hmb hmr
  unfold base
  rw [LiteralState.rotateLeft_eq_rotate]
  exact ((List.rotate_perm (render background (resident embed assignment) cuts) gap).append_right
    [embed (assignment none)]).nodup_iff.mpr hnd

theorem stationary_atCut (backgroundTest : α → Bool) (background : Fin M → α)
    (embed : Control → α) (hembed : Function.Injective embed)
    (htestBackground : ∀ i, backgroundTest (background i) = true)
    (htestControl : ∀ c, backgroundTest (embed c) = false)
    (assignment : FiniteRoles.Role k ≃ Control) (cuts : Fin k → Fin M) (gap : Nat)
    (target : Fin k) :
    AtCut backgroundTest (base background embed assignment cuts gap)
      (embed (assignment (some target))) (background (cuts target)) := by
  apply mobile_base_atCut
  · exact htestControl _
  · intro h
    have heq := assignment.injective (hembed h)
    cases heq
  · exact render_atCut backgroundTest background (resident embed assignment)
      (resident_injective embed hembed assignment) htestBackground
      (fun i => htestControl _) cuts target

/-- A matched named stationary control has the same actual background cut
in two cyclically equal rendered bases. -/
theorem matched_cuts_eq (backgroundTest : α → Bool) (background : Fin M → α)
    (embed : Control → α) (hbackground : Function.Injective background)
    (hembed : Function.Injective embed)
    (htestBackground : ∀ i, backgroundTest (background i) = true)
    (htestControl : ∀ c, backgroundTest (embed c) = false)
    (first second : FiniteRoles.Role k ≃ Control)
    (firstCuts secondCuts : Fin k → Fin M) (firstGap secondGap : Nat)
    (hcyclic : (base background embed first firstCuts firstGap).IsRotated
      (base background embed second secondCuts secondGap)) (i j : Fin k)
    (hmatch : Matches first second i j) : firstCuts i = secondCuts j := by
  have hfirst := stationary_atCut backgroundTest background embed hembed htestBackground htestControl
    first firstCuts firstGap i
  have hsecond := stationary_atCut backgroundTest background embed hembed htestBackground htestControl
    second secondCuts secondGap j
  have hlabel : embed (first (some i)) = embed (second (some j)) := congrArg embed hmatch
  rw [← hlabel] at hsecond
  apply hbackground
  exact common_stationary_cut backgroundTest _ _
    (base_nodup backgroundTest background embed hbackground hembed htestBackground htestControl
      first firstCuts firstGap) hcyclic _ _ _ hfirst hsecond

/-- Every common stationary label is in the same physical position when
two actual rendered rows on one robust frame have the same cyclic base. -/
theorem all_matches_diagonal (hk : 3 ≤ k) (backgroundTest : α → Bool)
    (background : Fin M → α) (embed : Control → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htestBackground : ∀ i, backgroundTest (background i) = true)
    (htestControl : ∀ c, backgroundTest (embed c) = false)
    (q : Fin k → ZMod M) (hrobust : Robust q)
    (first second : FiniteRoles.Role k ≃ Control)
    (firstCuts secondCuts : Fin k → Fin M) (firstGap secondGap : Nat)
    (t t' : ZMod M) (phases phases' : Fin k → Bool)
    (hfirst : Represents q t phases firstCuts) (hsecond : Represents q t' phases' secondCuts)
    (hcyclic : (base background embed first firstCuts firstGap).IsRotated
      (base background embed second secondCuts secondGap)) :
    ∀ i j, Matches first second i j → i = j := by
  have hequal (i j : Fin k) (hmatch : Matches first second i j) :
      q i + t + (bit (phases i) : ZMod M) = q j + t' + (bit (phases' j) : ZMod M) := by
    have hc := congrArg cutValue (matched_cuts_eq backgroundTest background embed hbackground hembed
      htestBackground htestControl first second firstCuts secondCuts firstGap secondGap hcyclic i j hmatch)
    rw [hfirst i, hsecond j] at hc
    exact hc
  obtain ⟨i₀, j₀, i₁, j₁, hne, hm₀, hm₁⟩ := two_matches hk first second
  intro i j hmatch
  by_cases hi : i = i₀
  · subst i
    exact (two_matches_diagonal q hrobust t t' i₀ j i₁ j₁ hne
      (phases i₀) (phases' j) (phases i₁) (phases' j₁)
      (hequal i₀ j hmatch) (hequal i₁ j₁ hm₁)).1
  · exact (two_matches_diagonal q hrobust t t' i j i₀ j₀ hi
      (phases i) (phases' j) (phases i₀) (phases' j₀)
      (hequal i j hmatch) (hequal i₀ j₀ hm₀)).1

end CoefficientTwoPrecision.ActualMatching

#print axioms CoefficientTwoPrecision.ActualMatching.matched_cuts_eq
#print axioms CoefficientTwoPrecision.ActualMatching.all_matches_diagonal
