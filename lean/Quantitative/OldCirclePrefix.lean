import Quantitative.GuardPositions

/-!
# Filtering a local background prefix to the original old circle

A position inside the block at old cut x occurs before that block's old
symbol. Deleting every guard therefore leaves exactly the first x old
symbols before that position. This identifies insertion cuts themselves,
not just a bounded numerical difference between two coordinate systems.
-/

namespace CoefficientTwoPrecision.OldCirclePrefix

open SuperpermutationUpperBound.Transport
open StationaryCircle StationaryUpdate GuardCoordinates

private theorem take_middle {α : Type} (before middle after : List α)
    (offset : Nat) (hoff : offset ≤ middle.length) :
    (before ++ middle ++ after).take (before.length + offset) =
      before ++ middle.take offset := by
  rw [List.append_assoc, List.take_add, List.take_append_length, List.drop_append_length,
    List.take_append_of_le_length hoff]

private theorem filter_blocks {m G : Nat} {α : Type}
    (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m) (keep : α → Bool)
    (hold : ∀ i, keep (old i) = true) (hguard : ∀ j, keep (guard j) = false)
    (xs : List (Fin m)) :
    (xs.flatMap (block old guard cuts)).filter keep = xs.map old := by
  have hblock (cut : Fin m) : (block old guard cuts cut).filter keep = [old cut] := by
    have hg : ((controlsAt cuts cut).map guard).filter keep = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      simp [hguard j]
    simp [block, List.filter_append, hg, hold]
  induction xs with
  | nil => rfl
  | cons cut xs ih =>
    simp only [List.flatMap_cons, List.filter_append, hblock, ih, List.map_cons,
      List.singleton_append]

theorem prefix_filter {m G : Nat} {α : Type}
    (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m) (keep : α → Bool)
    (hold : ∀ i, keep (old i) = true) (hguard : ∀ j, keep (guard j) = false)
    (cut : Fin m) (offset : Nat) (hoff : offset < (block old guard cuts cut).length) :
    ((render old guard cuts).take (blockStart old guard cuts cut + offset)).filter keep =
      ((List.finRange m).map old).take cut.val := by
  have hguardsLen : offset ≤ ((controlsAt cuts cut).map guard).length := by
    simp only [block, List.length_append, List.length_singleton] at hoff
    omega
  have hpartial : ((block old guard cuts cut).take offset).filter keep = [] := by
    rw [block, List.take_append_of_le_length hguardsLen]
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take ha)
    simp [hguard j]
  have htake : (render old guard cuts).take (blockStart old guard cuts cut + offset) =
      (((List.finRange m).take cut.val).flatMap (block old guard cuts)) ++
        (block old guard cuts cut).take offset := by
    rw [render_split old guard cuts cut]
    exact take_middle _ _ _ offset hoff.le
  rw [htake, List.filter_append, hpartial, List.append_nil]
  rw [filter_blocks old guard cuts keep hold hguard]
  simp only [List.map_take]

theorem suffix_filter {m G : Nat} {α : Type}
    (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m) (keep : α → Bool)
    (hold : ∀ i, keep (old i) = true) (hguard : ∀ j, keep (guard j) = false)
    (cut : Fin m) (offset : Nat) (hoff : offset < (block old guard cuts cut).length) :
    ((render old guard cuts).drop (blockStart old guard cuts cut + offset)).filter keep =
      ((List.finRange m).map old).drop cut.val := by
  have hsplit := congrArg (List.filter keep)
    (List.take_append_drop (blockStart old guard cuts cut + offset) (render old guard cuts))
  rw [List.filter_append, prefix_filter old guard cuts keep hold hguard cut offset hoff,
    delete_residents old guard cuts keep hold hguard] at hsplit
  exact List.append_cancel_left (hsplit.trans
    (List.take_append_drop cut.val ((List.finRange m).map old)).symm)

/-- Inserting a retained control at the local position projects to literal
insertion at the containing original old cut. -/
theorem insertion_filter {m G : Nat} {α : Type}
    (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m) (keep : α → Bool)
    (hold : ∀ i, keep (old i) = true) (hguard : ∀ j, keep (guard j) = false)
    (tracked : α) (htracked : keep tracked = true)
    (cut : Fin m) (offset : Nat) (hoff : offset < (block old guard cuts cut).length) :
    (insertLetter (render old guard cuts) tracked
      (blockStart old guard cuts cut + offset)).filter keep =
        insertLetter ((List.finRange m).map old) tracked cut.val := by
  simp only [insertLetter, List.filter_append, List.filter_cons, htracked,
    Bool.true_eq, ↓reduceIte, List.filter_nil]
  rw [prefix_filter old guard cuts keep hold hguard cut offset hoff,
    suffix_filter old guard cuts keep hold hguard cut offset hoff]

end CoefficientTwoPrecision.OldCirclePrefix

#print axioms CoefficientTwoPrecision.OldCirclePrefix.prefix_filter
#print axioms CoefficientTwoPrecision.OldCirclePrefix.insertion_filter
