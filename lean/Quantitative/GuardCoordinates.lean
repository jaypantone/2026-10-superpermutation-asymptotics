import Quantitative.GuardBackgrounds

/-!
# Exact original-cut offsets in the concrete guard renderer

The renderer starts before the guards at old cut zero. Every entry in the
block at old cut x has literal index x+e, where e counts preceding guards
and lies between zero and G. The statement includes old symbols and guard
symbols. A later cyclic re-anchoring adds a common shift; zero-sum linear
relations are unchanged by that common shift.
-/

namespace CoefficientTwoPrecision.GuardCoordinates

open CoefficientTwoPrecision.StationaryCircle CoefficientTwoPrecision.StationaryUpdate

variable {m G : Nat} {α : Type}

private theorem flatMap_length_ge {β : Type} (xs : List β) (f : β → List α)
    (hf : ∀ x ∈ xs, 1 ≤ (f x).length) : xs.length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

def blockStart (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (cut : Fin m) : Nat :=
  (((List.finRange m).take cut.val).flatMap (block old guard cuts)).length

theorem finRange_split (cut : Fin m) :
    List.finRange m = (List.finRange m).take cut.val ++
      cut :: (List.finRange m).drop (cut.val + 1) := by
  have hi : cut.val < (List.finRange m).length := by simp
  have he := List.take_append_drop cut.val (List.finRange m)
  rw [List.drop_eq_getElem_cons (l := List.finRange m) hi] at he
  have hv : (List.finRange m)[cut.val]'hi = cut := by apply Fin.ext; simp
  rw [hv] at he
  exact he.symm

/-- This equality identifies the actual literal prefix and suffix of every
old-cut block, rather than only counting an abstract arrangement. -/
theorem render_split (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (cut : Fin m) :
    render old guard cuts =
      (((List.finRange m).take cut.val).flatMap (block old guard cuts)) ++
      block old guard cuts cut ++
      (((List.finRange m).drop (cut.val + 1)).flatMap (block old guard cuts)) := by
  have he := congrArg (List.flatMap (block old guard cuts)) (finRange_split cut)
  simpa only [render, List.flatMap_append, List.flatMap_cons, List.append_assoc] using he

/-- The actual renderer index of any old or guard symbol at old cut x is
between x and x+G. All guard cuts may be handled at once. -/
theorem coordinate_bounds (old : Fin m → α) (guard : Fin G → α)
    (cuts : Fin G → Fin m) (ho : Function.Injective old)
    (hg : Function.Injective guard) (hcross : ∀ j i, guard j ≠ old i)
    (cut : Fin m) (offset : Nat) (hoff : offset < (block old guard cuts cut).length) :
    cut.val ≤ blockStart old guard cuts cut + offset ∧
      blockStart old guard cuts cut + offset ≤ cut.val + G ∧
      blockStart old guard cuts cut + offset < (render old guard cuts).length := by
  have hblock : ∀ x, 1 ≤ (block old guard cuts x).length := by
    intro x
    simp [block]
  have hbefore := flatMap_length_ge ((List.finRange m).take cut.val)
    (block old guard cuts) (fun x _ => hblock x)
  have hafter := flatMap_length_ge ((List.finRange m).drop (cut.val + 1))
    (block old guard cuts) (fun x _ => hblock x)
  have hcut : cut.val < m := cut.isLt
  have hpre : ((List.finRange m).take cut.val).length = cut.val := by
    simp [List.length_take, Nat.min_eq_left hcut.le]
  have hpost : ((List.finRange m).drop (cut.val + 1)).length = m - (cut.val + 1) := by simp
  rw [hpre] at hbefore
  rw [hpost] at hafter
  have htotal := render_length old guard cuts ho hg hcross
  have hsplit := congrArg List.length (render_split old guard cuts cut)
  simp only [List.length_append] at hsplit
  change cut.val ≤ blockStart old guard cuts cut at hbefore
  have hsplit' : (render old guard cuts).length = blockStart old guard cuts cut +
      (block old guard cuts cut).length +
        (((List.finRange m).drop (cut.val + 1)).flatMap (block old guard cuts)).length := hsplit
  omega

/-- The bounded offset is obtained from the actual literal position. -/
theorem coordinate_offset (old : Fin m → α) (guard : Fin G → α)
    (cuts : Fin G → Fin m) (ho : Function.Injective old)
    (hg : Function.Injective guard) (hcross : ∀ j i, guard j ≠ old i)
    (cut : Fin m) (offset : Nat) (hoff : offset < (block old guard cuts cut).length) :
    ∃ e ≤ G, blockStart old guard cuts cut + offset = cut.val + e := by
  have hb := coordinate_bounds old guard cuts ho hg hcross cut offset hoff
  exact ⟨blockStart old guard cuts cut + offset - cut.val, by omega, by omega⟩

end CoefficientTwoPrecision.GuardCoordinates

#print axioms CoefficientTwoPrecision.GuardCoordinates.render_split
#print axioms CoefficientTwoPrecision.GuardCoordinates.coordinate_offset
