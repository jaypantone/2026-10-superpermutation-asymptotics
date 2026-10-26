import Quantitative.GuardCoordinates

/-!
# Every literal background position has an original cut

The coordinate bound is useful only if it applies to every position in
the rendered background. The partition argument below supplies the actual
block and the offset inside that block. No coordinate map is assumed.
-/

namespace CoefficientTwoPrecision.GuardPositions

open CoefficientTwoPrecision.StationaryCircle CoefficientTwoPrecision.GuardCoordinates
open CoefficientTwoPrecision.StationaryUpdate

private theorem flatMap_position {α β : Type} (f : α → List β)
    (xs : List α) (p : Nat) (hp : p < (xs.flatMap f).length) :
    ∃ before a after offset,
      xs = before ++ a :: after ∧ offset < (f a).length ∧
        p = (before.flatMap f).length + offset := by
  induction xs generalizing p with
  | nil => simp at hp
  | cons a xs ih =>
    by_cases hfirst : p < (f a).length
    · exact ⟨[], a, xs, p, rfl, hfirst, by simp⟩
    · have hrest : p - (f a).length < (xs.flatMap f).length := by
        simp only [List.flatMap_cons, List.length_append] at hp
        omega
      obtain ⟨before, b, after, offset, hs, ho, he⟩ := ih (p - (f a).length) hrest
      refine ⟨a :: before, b, after, offset, ?_, ho, ?_⟩
      · simp only [List.cons_append, hs]
      · simp only [List.flatMap_cons, List.length_append]
        omega

/-- Every actual local position lies in exactly one of the listed old-cut
blocks; only existence is needed for the following estimates. -/
theorem position_has_cut {m G : Nat} {α : Type}
    (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (p : Nat) (hp : p < (render old guard cuts).length) :
    ∃ cut : Fin m, ∃ offset : Nat,
      offset < (block old guard cuts cut).length ∧
        p = blockStart old guard cuts cut + offset := by
  obtain ⟨before, cut, after, offset, hs, ho, he⟩ :=
    flatMap_position (block old guard cuts) (List.finRange m) p hp
  have hn : (before ++ cut :: after).Nodup := hs ▸ List.nodup_finRange m
  have hnot : cut ∉ before := by
    intro hc
    exact (List.nodup_append.mp hn).2.2 cut hc cut (by simp) rfl
  have hlen : cut.val = before.length := by
    have hi := congrArg (fun xs : List (Fin m) => xs.idxOf cut) hs
    simpa only [List.idxOf_finRange, List.idxOf_append, if_neg hnot,
      List.idxOf_cons_self, Nat.zero_add] using hi
  have htake : (List.finRange m).take cut.val = before := by
    rw [hlen, hs]
    simp
  exact ⟨cut, offset, ho, by simpa only [blockStart, htake] using he⟩

/-- A coordinate and its bounded offset are obtained from each actual
position of the rendered list. -/
theorem position_offset {m G : Nat} {α : Type}
    (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (ho : Function.Injective old) (hg : Function.Injective guard)
    (hcross : ∀ j i, guard j ≠ old i)
    (p : Nat) (hp : p < (render old guard cuts).length) :
    ∃ cut : Fin m, ∃ e ≤ G, p = cut.val + e := by
  obtain ⟨cut, offset, hoff, heq⟩ := position_has_cut old guard cuts p hp
  obtain ⟨e, he, hp'⟩ := coordinate_offset old guard cuts ho hg hcross cut offset hoff
  exact ⟨cut, e, he, heq.trans hp'⟩

/-- The block coordinate also identifies the actual symbol at that
position. Optional indexing avoids transporting a dependent length proof
through the literal prefix decomposition. -/
theorem render_getElem_block {m G : Nat} {α : Type}
    (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (cut : Fin m) (offset : Nat) (hoff : offset < (block old guard cuts cut).length) :
    (render old guard cuts)[blockStart old guard cuts cut + offset]? =
      some ((block old guard cuts cut)[offset]'hoff) := by
  rw [render_split old guard cuts cut, List.append_assoc]
  rw [List.getElem?_append_right (by unfold blockStart; omega)]
  simp only [blockStart, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hoff]
  exact List.getElem?_eq_getElem hoff

theorem guard_cut_of_mem_block {m G : Nat} {α : Type}
    (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (hg : Function.Injective guard) (hcross : ∀ j i, guard j ≠ old i)
    (j : Fin G) (cut : Fin m) (hmem : guard j ∈ block old guard cuts cut) :
    cuts j = cut := by
  unfold block at hmem
  rcases List.mem_append.mp hmem with hresident | hold
  · obtain ⟨j', hj', he⟩ := List.mem_map.mp hresident
    have hjj : j' = j := hg he
    subst j'
    exact (mem_controlsAt cuts cut j).mp hj'
  · have he : guard j = old cut := List.mem_singleton.mp hold
    exact False.elim (hcross j cut he)

/-- For a named guard, the recovered old cut is its prescribed cut. This
is the identity needed to count foreign relations in the guard variables. -/
theorem guard_position_offset {m G : Nat} {α : Type}
    (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (ho : Function.Injective old) (hg : Function.Injective guard)
    (hcross : ∀ j i, guard j ≠ old i)
    (j : Fin G) (p : Nat) (hp : p < (render old guard cuts).length)
    (hguard : (render old guard cuts)[p]? = some (guard j)) :
    ∃ e ≤ G, p = (cuts j).val + e := by
  obtain ⟨cut, offset, hoff, heq⟩ := position_has_cut old guard cuts p hp
  have hentry := render_getElem_block old guard cuts cut offset hoff
  rw [← heq] at hentry
  have hvalue : (block old guard cuts cut)[offset]'hoff = guard j :=
    Option.some.inj (hentry.symm.trans hguard)
  have hmem : guard j ∈ block old guard cuts cut := hvalue ▸ List.getElem_mem hoff
  have hcut := guard_cut_of_mem_block old guard cuts hg hcross j cut hmem
  obtain ⟨e, he, hposition⟩ := coordinate_offset old guard cuts ho hg hcross cut offset hoff
  exact ⟨e, he, by simpa only [← hcut] using heq.trans hposition⟩

end CoefficientTwoPrecision.GuardPositions

#print axioms CoefficientTwoPrecision.GuardPositions.position_has_cut
#print axioms CoefficientTwoPrecision.GuardPositions.position_offset
#print axioms CoefficientTwoPrecision.GuardPositions.guard_position_offset
