import Quantitative.FiniteRoles
import Mathlib.Data.List.Rotate
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Extracting the cyclic matching from two retained label lists

There are exactly k-1 possible offsets after omitting one of k stationary
positions. This lemma extracts an actual offset from cyclic equality of
the retained label lists. The geometric projection to these lists is a
separate obligation; no arbitrary permutation is counted as a cyclic match.
-/

namespace CoefficientTwoPrecision.CyclicMatching

theorem rotation_offset {n : Nat} {α : Type} (hn : 0 < n)
    (left right : Fin n → α)
    (h : (List.ofFn left).IsRotated (List.ofFn right)) :
    ∃ offset : Fin n, ∀ i, left (i + offset) = right i := by
  obtain ⟨shift, hshift⟩ := h
  let offset : Fin n := ⟨shift % n, Nat.mod_lt _ hn⟩
  refine ⟨offset, ?_⟩
  intro i
  have hget := congrArg (fun word : List α => word[i.val]?) hshift
  rw [List.getElem?_rotate (by simpa using i.isLt), List.length_ofFn] at hget
  have hmod : (i.val + shift) % n < n := Nat.mod_lt _ hn
  have hval : (⟨(i.val + shift) % n, hmod⟩ : Fin n) = i + offset := by
    apply Fin.ext
    simp only [Fin.val_add, offset, Nat.add_mod_mod]
  simpa only [List.getElem?_ofFn, dif_pos hmod, dif_pos i.isLt,
    Option.some.injEq, Fin.eta, hval] using hget

def retainedLabels {n : Nat} {α : Type}
    (assignment : FiniteRoles.Role (n + 1) ≃ α) (omitted : Fin (n + 1)) : List α :=
  List.ofFn (fun i : Fin n => assignment (some (omitted.succAbove i)))

theorem retained_matching {n : Nat} {α : Type} (hn : 0 < n)
    (left right : FiniteRoles.Role (n + 1) ≃ α)
    (leftOmitted rightOmitted : Fin (n + 1))
    (h : (retainedLabels left leftOmitted).IsRotated (retainedLabels right rightOmitted)) :
    ∃ offset : Fin n, ∀ i : Fin n,
      FiniteRoles.Matches left right (leftOmitted.succAbove (i + offset))
        (rightOmitted.succAbove i) :=
  rotation_offset hn _ _ h

end CoefficientTwoPrecision.CyclicMatching

#print axioms CoefficientTwoPrecision.CyclicMatching.retained_matching
