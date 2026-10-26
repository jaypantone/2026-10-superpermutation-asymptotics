import Quantitative.LiteralSchedule
import Quantitative.SourceUniverse

/-!
# No repeated source cyclic class inside one proper full run

The statement includes the final short source row: if there are `moves`
full moves, the source gap indices are exactly 0 through `moves`. Requiring
`moves < stationary.length` therefore suffices. Robust geometry must still
show that rows compared across different positive updates reduce to this
case or to the one-short-update exclusion.
-/

namespace CoefficientTwoPrecision.FullRunSimplicity

open LiteralState LiteralSchedule
open SuperpermutationUpperBound

variable {α : Type}

theorem fullIterate_cyclic_injective (stationary : List α) (mobile : α)
    (hnodup : stationary.Nodup) (hfresh : mobile ∉ stationary) (i j : Nat)
    (hi : i < stationary.length) (hj : j < stationary.length)
    (h : (fullIterate i (stationary ++ [mobile])).IsRotated
      (fullIterate j (stationary ++ [mobile]))) : i = j := by
  rw [fullIterate_formula, fullIterate_formula,
    LiteralState.rotateLeft_eq_rotate, LiteralState.rotateLeft_eq_rotate] at h
  exact SourceUniverse.insertion_class_injective hnodup hfresh hi hj h

/-- The actual full/short row list has exactly the expected sequence of bases. -/
theorem updateRows_bases (satellite : α) (moves : Nat) (base : List α) :
    (updateRows satellite moves base).map Row.base =
      (List.range (moves + 1)).map (fun i => fullIterate i base) := by
  simp only [updateRows, List.map_append, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, fullRow, shortRow]
  rw [List.range_succ, List.map_append]
  rfl

theorem updateRows_cyclicDistinct (stationary : List α) (mobile satellite : α)
    (hnodup : stationary.Nodup) (hfresh : mobile ∉ stationary) (moves : Nat)
    (hmoves : moves < stationary.length) :
    SourceUniverse.CyclicDistinct
      ((updateRows satellite moves (stationary ++ [mobile])).map Row.base) := by
  rw [updateRows_bases]
  unfold SourceUniverse.CyclicDistinct
  apply List.pairwise_map.mpr
  have hnodupRange : (List.range (moves + 1)).Nodup := List.nodup_range
  apply List.Pairwise.imp_of_mem _ hnodupRange
  intro i j hi hj hne hcyclic
  have hib : i < moves + 1 := List.mem_range.mp hi
  have hjb : j < moves + 1 := List.mem_range.mp hj
  exact hne (fullIterate_cyclic_injective stationary mobile hnodup hfresh i j
    (by omega) (by omega) hcyclic)

end CoefficientTwoPrecision.FullRunSimplicity

#print axioms CoefficientTwoPrecision.FullRunSimplicity.fullIterate_cyclic_injective
#print axioms CoefficientTwoPrecision.FullRunSimplicity.updateRows_cyclicDistinct
