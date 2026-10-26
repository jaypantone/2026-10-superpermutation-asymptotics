import Quantitative.GuardBackgrounds
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Exact count of actual distinct-cut guard backgrounds

The finite list is the image of all injective labelled guard-cut maps under
the concrete word renderer. The reconstruction theorem proves cyclic
distinctness of that list, so its falling-factorial length counts actual
background classes without an ordering multiplicity.
-/

namespace CoefficientTwoPrecision.GuardCount

open SuperpermutationUpperBound CoefficientTwoPrecision.StationaryCircle
open CoefficientTwoPrecision.GuardBackgrounds

variable {m G : Nat} {α : Type} [DecidableEq α]

noncomputable def guardBackgrounds (old : Fin m → α) (guard : Fin G → α) : List (List α) :=
  (Finset.univ : Finset (Fin G ↪ Fin m)).toList.map
    (fun cuts : Fin G ↪ Fin m => render old guard cuts)

theorem guardBackgrounds_length (old : Fin m → α) (guard : Fin G → α) :
    (guardBackgrounds old guard).length = m.descFactorial G := by
  simp [guardBackgrounds, Fintype.card_embedding_eq]

theorem guardBackgrounds_cyclicDistinct (old : Fin m → α) (guard : Fin G → α)
    (ho : Function.Injective old) (hg : Function.Injective guard)
    (hcross : ∀ j i, guard j ≠ old i) :
    (guardBackgrounds old guard).Pairwise (fun a b => ¬ CyclicEq a b) := by
  classical
  simp only [guardBackgrounds, List.pairwise_map]
  apply (Finset.nodup_toList (Finset.univ : Finset (Fin G ↪ Fin m))).imp
  intro first second hne hc
  have he := cuts_eq_of_cyclicEq old guard ho hg hcross first second hc
  apply hne
  exact DFunLike.coe_injective he

end CoefficientTwoPrecision.GuardCount

#print axioms CoefficientTwoPrecision.GuardCount.guardBackgrounds_length
#print axioms CoefficientTwoPrecision.GuardCount.guardBackgrounds_cyclicDistinct
