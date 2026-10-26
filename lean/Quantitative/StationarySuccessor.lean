import Quantitative.StationaryUpdate

/-!
# Positive short updates preserve the concrete stationary-circle model

The destination is now the cyclic successor of the target's background
cut. Rotating the background-index list handles the last/first cut boundary
uniformly. The resulting literal equality proves an actual F/S update,
not just the corresponding exchange of abstract role labels.
-/

namespace CoefficientTwoPrecision.StationarySuccessor

open JointStates LiteralState StationaryCircle StationaryUpdate

variable {M k : Nat} {α : Type}

def successor (hM : 0 < M) (cut : Fin M) : Fin M :=
  ⟨(cut.val + 1) % M, Nat.mod_lt _ hM⟩

/-- Starting the background cycle at a cut exposes that cut and its actual
cyclic successor, including the wrap from the last cut to zero. -/
theorem rotated_cut_order (hM : 2 ≤ M) (cut : Fin M) :
    ∃ rest : List (Fin M),
      (List.finRange M).rotate cut.val = cut :: successor (by omega) cut :: rest := by
  have hfirst : ((List.finRange M).rotate cut.val).head? = some cut := by
    rw [List.head?_rotate (by simpa using cut.isLt)]
    rw [List.getElem?_eq_getElem (by simpa using cut.isLt)]
    simp
  have hsecond : ((List.finRange M).rotate cut.val)[1]? =
      some (successor (by omega) cut) := by
    rw [List.getElem?_rotate (by simp; omega)]
    simp only [List.length_finRange]
    rw [List.getElem?_eq_getElem (by simp; exact Nat.mod_lt _ (by omega))]
    simp [successor, Nat.add_comm]
  generalize horder : (List.finRange M).rotate cut.val = order at hfirst hsecond ⊢
  cases order with
  | nil => simp at hfirst
  | cons a tail =>
    have ha : a = cut := by simpa using hfirst
    subst a
    cases tail with
    | nil => simp at hsecond
    | cons b rest =>
      have hb : b = successor (by omega) cut := by simpa using hsecond
      subst b
      exact ⟨rest, rfl⟩

/-- Replacing symbols by finite blocks preserves cyclic rotation. -/
theorem flatMap_rotate_isRotated {β : Type} (order : List α) (blocks : α → List β)
    (n : Nat) (hn : n ≤ order.length) :
    List.IsRotated (order.flatMap blocks) ((order.rotate n).flatMap blocks) := by
  have hsource : order.flatMap blocks =
      (order.take n).flatMap blocks ++ (order.drop n).flatMap blocks := by
    rw [← List.flatMap_append, List.take_append_drop]
  have htarget : (order.rotate n).flatMap blocks =
      (order.drop n).flatMap blocks ++ (order.take n).flatMap blocks := by
    rw [List.rotate_eq_drop_append_take hn, List.flatMap_append]
  rw [hsource, htarget]
  exact List.isRotated_append

/-- Before and after a cut advance, the concrete stationary circles have
the local forms A,x,y,rest and x,T,y,rest. Here y is the next background
symbol and T is the old mobile. -/
theorem positive_local_forms (hM : 2 ≤ M) (background : Fin M → α)
    (resident : Fin k → α) (cuts : Fin k → Fin M)
    (hcuts : Function.Injective cuts) (target : Fin k) (mobile : α)
    (hfree : ∀ j, cuts j ≠ successor (by omega) (cuts target)) :
    ∃ rest : List α,
      List.IsRotated (render background resident cuts)
        (resident target :: background (cuts target) ::
          background (successor (by omega) (cuts target)) :: rest) ∧
      List.IsRotated
        (render background (moveResident resident target mobile)
          (moveCut cuts target (successor (by omega) (cuts target))))
        (background (cuts target) :: mobile ::
          background (successor (by omega) (cuts target)) :: rest) := by
  obtain ⟨rest, horder⟩ := rotated_cut_order hM (cuts target)
  have hnodup :
      ((List.finRange M).rotate (cuts target).val).Nodup :=
    List.nodup_rotate.mpr (List.nodup_finRange M)
  rw [horder] at hnodup
  have hnotold : cuts target ∉ rest := by
    intro h
    exact (List.nodup_cons.mp hnodup).1 (List.mem_cons_of_mem _ h)
  have hnotnew : successor (by omega) (cuts target) ∉ rest :=
    (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
  have hrest :
      rest.flatMap (block background (moveResident resident target mobile)
        (moveCut cuts target (successor (by omega) (cuts target)))) =
      rest.flatMap (block background resident cuts) := by
    apply List.flatMap_congr
    intro cut hcut
    apply moved_other_block
    · intro heq
      exact hnotold (heq.symm ▸ hcut)
    · intro heq
      exact hnotnew (heq.symm ▸ hcut)
  have hempty : block background resident cuts (successor (by omega) (cuts target)) =
      [background (successor (by omega) (cuts target))] := by
    simp [block, controlsAt_empty _ _ hfree]
  refine ⟨rest.flatMap (block background resident cuts), ?_, ?_⟩
  · have h := flatMap_rotate_isRotated (List.finRange M) (block background resident cuts)
      (cuts target).val (by simpa using (cuts target).isLt.le)
    change List.IsRotated (render background resident cuts) _ at h
    simpa only [horder, List.flatMap_cons,
      target_block background resident cuts hcuts target, hempty,
      List.cons_append, List.nil_append] using h
  · have h := flatMap_rotate_isRotated (List.finRange M)
      (block background (moveResident resident target mobile)
        (moveCut cuts target (successor (by omega) (cuts target))))
      (cuts target).val (by simpa using (cuts target).isLt.le)
    change List.IsRotated
      (render background (moveResident resident target mobile)
        (moveCut cuts target (successor (by omega) (cuts target)))) _ at h
    simpa only [horder, List.flatMap_cons,
      moved_old_block background resident cuts hcuts target _ mobile hfree,
      moved_destination_block background resident cuts hcuts target _ mobile hfree,
      hrest, List.cons_append, List.nil_append] using h

/-- An actual positive update changes the rendered cut and resident exactly
as specified. The old resident is the new final/mobile symbol. All rotations
and the number of full moves are constructed in the proof. -/
theorem positive_update_realizes (hM : 2 ≤ M) (background : Fin M → α)
    (resident : Fin k → α) (cuts : Fin k → Fin M)
    (hcuts : Function.Injective cuts) (target : Fin k) (mobile : α) (gap : Nat)
    (hfree : ∀ j, cuts j ≠ successor (by omega) (cuts target)) :
    ∃ moves < (render background resident cuts).length, ∃ nextGap : Nat,
      shortStep (fullIterate moves ((render background resident cuts).rotateLeft gap ++ [mobile])) =
        (render background (moveResident resident target mobile)
          (moveCut cuts target (successor (by omega) (cuts target)))).rotateLeft nextGap ++
            [resident target] := by
  obtain ⟨rest, hold, hnew⟩ := positive_local_forms hM background resident cuts hcuts target mobile hfree
  have holdTarget : List.IsRotated (render background resident cuts)
      ((background (successor (by omega) (cuts target)) :: rest) ++
        [resident target, background (cuts target)]) :=
    hold.trans (List.isRotated_append
      (l := [resident target, background (cuts target)])
      (l' := background (successor (by omega) (cuts target)) :: rest))
  have hnewTarget : List.IsRotated
      (render background (moveResident resident target mobile)
        (moveCut cuts target (successor (by omega) (cuts target))))
      ((mobile :: background (successor (by omega) (cuts target)) :: rest) ++
        [background (cuts target)]) :=
    hnew.trans (List.isRotated_append
      (l := [background (cuts target)])
      (l' := mobile :: background (successor (by omega) (cuts target)) :: rest))
  obtain ⟨desired, hdesired⟩ := holdTarget
  obtain ⟨nextGap, hafter⟩ := hnewTarget
  have hlen : 0 < (render background resident cuts).length := by
    obtain ⟨before, after, hsplit⟩ := target_decomposition background resident cuts hcuts target
    rw [hsplit]
    simp
  obtain ⟨moves, hmoves, hreach⟩ :=
    rotation_reachable (render background resident cuts) hlen gap desired
  have hfull : fullIterate moves ((render background resident cuts).rotateLeft gap ++ [mobile]) =
      (background (successor (by omega) (cuts target)) :: rest) ++
        [resident target, background (cuts target), mobile] := by
    rw [fullIterate_formula, hreach, rotateLeft_eq_rotate, hdesired]
    simp [List.append_assoc]
  refine ⟨moves, hmoves, nextGap, ?_⟩
  rw [hfull, shortStep_suffix, rotateLeft_eq_rotate, hafter]
  simp [List.append_assoc]

end CoefficientTwoPrecision.StationarySuccessor

#print axioms CoefficientTwoPrecision.StationarySuccessor.rotated_cut_order
#print axioms CoefficientTwoPrecision.StationarySuccessor.positive_local_forms
#print axioms CoefficientTwoPrecision.StationarySuccessor.positive_update_realizes
