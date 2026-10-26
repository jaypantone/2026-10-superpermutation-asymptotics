import Quantitative.ShortBoundarySimplicity
import Quantitative.CutExtraction

/-!
# No cyclic repetition across one positive short update

The first compared row may occur anywhere before the short move. Delete
its mobile from both equal cyclic bases. The old stationary circle is
unchanged by its full moves. In the new circle, deleting that mobile
reduces the new full-gap index by one. Injectivity of the insertion gaps
for the old resident then forces the last new stationary gap. The proved
stopping bound excludes that gap.
-/

namespace CoefficientTwoPrecision.OneUpdateSimplicity

open LiteralState ShortBoundarySimplicity CutExtraction

variable {α : Type} [DecidableEq α]

theorem filter_rotate_cons (stationary : List α) (mobile : α)
    (hfresh : mobile ∉ stationary) (n : Nat) (hn : n ≤ stationary.length) :
    ((mobile :: stationary).rotate (n + 1)).filter (fun x => decide (x ≠ mobile)) =
      stationary.rotate n := by
  have hkeep (part : List α) (hpart : part.Sublist stationary) :
      part.filter (fun x => decide (x ≠ mobile)) = part := by
    apply List.filter_eq_self.mpr
    intro x hx
    have hne : x ≠ mobile := by
      intro heq
      exact hfresh (heq ▸ hpart.subset hx)
    simpa only [decide_eq_true_eq] using hne
  rw [List.rotate_cons_succ,
    List.rotate_eq_drop_append_take (by simp; omega),
    List.drop_append_of_le_length hn, List.take_append_of_le_length hn,
    List.filter_append, List.filter_append,
    hkeep _ (List.drop_sublist _ _), hkeep _ (List.take_sublist _ _)]
  simp only [List.filter_cons, List.filter_nil, ne_eq, not_true_eq_false,
    decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  exact (List.rotate_eq_drop_append_take hn).symm

theorem old_stationary_is_last_insertion (pre : List α) (resident crossed : α) :
    (pre ++ [resident, crossed]).IsRotated
      ((pre ++ [crossed]).rotate ((pre ++ [crossed]).length - 1) ++ [resident]) := by
  have hrot : (pre ++ [crossed]).rotate ((pre ++ [crossed]).length - 1) = crossed :: pre := by
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    rw [List.rotate_append_length_eq]
    rfl
  rw [hrot]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    (List.isRotated_append (l := pre ++ [resident]) (l' := [crossed]))

/-- A common cyclic base before and after one short move can occur only
at the last post-update full gap, regardless of the earlier full gap. -/
theorem return_across_one_update_last_gap (pre : List α) (resident crossed mobile : α)
    (hpre : 0 < pre.length) (hnodup : (pre ++ [resident, crossed, mobile]).Nodup)
    (i j : Nat) (hj : j < (newStationary pre crossed mobile).length)
    (hreturn : (fullIterate i (pre ++ [resident, crossed, mobile])).IsRotated
      (fullIterate j (shortStep (pre ++ [resident, crossed, mobile])))) :
    j = (newStationary pre crossed mobile).length - 1 := by
  let oldStationary := pre ++ [resident, crossed]
  let reduced := pre ++ [crossed]
  have hsource : pre ++ [resident, crossed, mobile] = oldStationary ++ [mobile] := by
    simp only [oldStationary, List.append_assoc, List.cons_append, List.nil_append]
  have hndSource : (oldStationary ++ [mobile]).Nodup := hsource ▸ hnodup
  have hndOld : oldStationary.Nodup := (List.nodup_append.mp hndSource).1
  have hmOld : mobile ∉ oldStationary := by
    intro hmem
    exact (List.nodup_append.mp hndSource).2.2 _ hmem _ (by simp) rfl
  have hsub : reduced.Sublist oldStationary :=
    (List.sublist_cons_self resident [crossed]).append_left pre
  have hndReduced : reduced.Nodup := List.Nodup.sublist hsub hndOld
  have hmReduced : mobile ∉ reduced := fun hmem => hmOld (hsub.subset hmem)
  have hrReduced : resident ∉ reduced := by
    intro hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact (List.nodup_append.mp hndOld).2.2 _ hmem _ (by simp) rfl
    · have hne : resident ≠ crossed := by
        have htail := (List.nodup_append.mp hndOld).2.1
        simpa using (List.nodup_cons.mp htail).1
      exact hne (by simpa using hmem)
  have hrm : resident ≠ mobile := by
    intro heq
    exact hmOld (heq ▸ (show resident ∈ oldStationary by simp [oldStationary]))
  have hkeepOld (n : Nat) :
      (oldStationary.rotate n).filter (fun x => decide (x ≠ mobile)) = oldStationary.rotate n := by
    apply List.filter_eq_self.mpr
    intro x hx
    have hne : x ≠ mobile := by
      intro heq
      exact hmOld (heq ▸ List.mem_rotate.mp hx)
    simpa only [decide_eq_true_eq] using hne
  have hfiltered := filter_isRotated _ _ (fun x => decide (x ≠ mobile)) hreturn
  have holdFull : fullIterate i (pre ++ [resident, crossed, mobile]) =
      oldStationary.rotate i ++ [mobile] := by
    rw [hsource, fullIterate_formula, LiteralState.rotateLeft_eq_rotate]
  have hnewFull : fullIterate j (shortStep (pre ++ [resident, crossed, mobile])) =
      (mobile :: reduced).rotate j ++ [resident] := by
    rw [shortStep_as_base, fullIterate_formula, LiteralState.rotateLeft_eq_rotate]
    rfl
  rw [holdFull, hnewFull, List.filter_append, List.filter_append, hkeepOld] at hfiltered
  simp only [List.filter_cons, List.filter_nil, hrm, ne_eq, not_true_eq_false,
    decide_false, decide_true, Bool.false_eq_true, ↓reduceIte,
    List.append_nil] at hfiltered
  change (oldStationary.rotate i).IsRotated
    (((mobile :: reduced).rotate j).filter (fun x => decide (x ≠ mobile)) ++ [resident]) at hfiltered
  have hcanonical := old_stationary_is_last_insertion pre resident crossed
  have hrotate : oldStationary.IsRotated (oldStationary.rotate i) := ⟨i, rfl⟩
  have hreducedLength : 1 < reduced.length := by
    simp only [reduced, List.length_append, List.length_singleton]
    omega
  cases j with
  | zero =>
    have hkeepReduced : reduced.filter (fun x => decide (x ≠ mobile)) = reduced := by
      apply List.filter_eq_self.mpr
      intro x hx
      have hne : x ≠ mobile := fun heq => hmReduced (heq ▸ hx)
      simpa only [decide_eq_true_eq] using hne
    simp only [List.rotate_zero, List.filter_cons, ne_eq, not_true_eq_false, decide_false,
      Bool.false_eq_true, ↓reduceIte, hkeepReduced] at hfiltered
    have hcompare := hcanonical.symm.trans (hrotate.trans hfiltered)
    have heq := SourceUniverse.insertion_class_injective hndReduced hrReduced
      (by omega : reduced.length - 1 < reduced.length) (by omega : 0 < reduced.length)
      (by simpa only [List.rotate_zero] using hcompare)
    omega
  | succ n =>
    have hn : n < reduced.length := by
      change n + 1 < reduced.length + 1 at hj
      omega
    rw [filter_rotate_cons reduced mobile hmReduced n hn.le] at hfiltered
    have heq := SourceUniverse.insertion_class_injective hndReduced hrReduced
      (by omega : reduced.length - 1 < reduced.length) hn
      (hcanonical.symm.trans (hrotate.trans hfiltered))
    change n + 1 = reduced.length + 1 - 1
    omega

theorem no_return_across_one_update (pre : List α) (resident crossed mobile : α)
    (hpre : 0 < pre.length) (hnodup : (pre ++ [resident, crossed, mobile]).Nodup)
    (i j : Nat) (hj : j < (newStationary pre crossed mobile).length - 1) :
    ¬ (fullIterate i (pre ++ [resident, crossed, mobile])).IsRotated
      (fullIterate j (shortStep (pre ++ [resident, crossed, mobile]))) := by
  intro hreturn
  have heq := return_across_one_update_last_gap pre resident crossed mobile hpre hnodup i j
    (by omega) hreturn
  omega

end CoefficientTwoPrecision.OneUpdateSimplicity

#print axioms CoefficientTwoPrecision.OneUpdateSimplicity.return_across_one_update_last_gap
#print axioms CoefficientTwoPrecision.OneUpdateSimplicity.no_return_across_one_update
