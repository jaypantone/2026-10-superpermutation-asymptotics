import Quantitative.StationaryUpdate
import Quantitative.SourceErasure

/-!
# Literal labelled guard backgrounds

The concrete renderer inserts each labelled guard before its assigned old
symbol. Filtering out every other guard recovers a single literal insertion
position. The cyclic class of the background therefore determines every
guard cut. This is the geometric injection behind the guard-background
count and the separation of different backgrounds on one active block.
-/

namespace CoefficientTwoPrecision.GuardBackgrounds

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open CoefficientTwoPrecision.StationaryCircle CoefficientTwoPrecision.StationaryUpdate

variable {m G : Nat} {α : Type} [DecidableEq α]

private theorem flatMap_without {β : Type} [DecidableEq β] (xs : List β)
    (target : β) (f : β → α) (guard : α) (hnot : target ∉ xs) :
    (xs.flatMap fun x => (if x = target then [guard] else []) ++ [f x]) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have ha : a ≠ target := by intro he; apply hnot; simp [he]
    have ht : target ∉ rest := fun hm => hnot (List.mem_cons_of_mem _ hm)
    simp only [List.flatMap_cons, if_neg ha, List.nil_append, List.singleton_append,
      List.map_cons, ih ht]

private theorem flatMap_one_insertion {β : Type} [DecidableEq β]
    (xs : List β) (hnd : xs.Nodup) (i : Nat) (hi : i < xs.length) (f : β → α) (guard : α) :
    (xs.flatMap fun x => (if x = xs[i] then [guard] else []) ++ [f x]) =
      insertLetter (xs.map f) guard i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    have hn := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.flatMap_cons, ↓reduceIte,
        flatMap_without rest a f guard hn.1, List.map_cons, insertLetter]
      simp
    | succ i =>
      have hi' : i < rest.length := by simp only [List.length_cons] at hi; omega
      have ha : a ≠ rest[i] := by
        intro he
        exact hn.1 (he ▸ List.getElem_mem hi')
      simp only [List.getElem_cons_succ, List.flatMap_cons, if_neg ha,
        List.nil_append, List.singleton_append, List.map_cons, insertLetter_cons_succ]
      exact congrArg (List.cons (f a)) (ih hn.2 i hi')

/-- Keeping the old alphabet and one specified guard gives one insertion
into the old anchored word, at that guard's actual assigned cut. -/
theorem filter_single_guard (old : Fin m → α) (guard : Fin G → α)
    (cuts : Fin G → Fin m) (target : Fin G) (keep : α → Bool)
    (hold : ∀ i, keep (old i) = true)
    (hguard : ∀ j, keep (guard j) = decide (j = target)) :
    (render old guard cuts).filter keep =
      insertLetter ((List.finRange m).map old) (guard target) (cuts target).val := by
  have hresident (cut : Fin m) :
      ((controlsAt cuts cut).map guard).filter keep =
        if cuts target = cut then [guard target] else [] := by
    rw [List.filter_map]
    have hfun : keep ∘ guard = (fun j => decide (j = target)) := by
      funext j
      exact hguard j
    rw [hfun, List.filter_eq]
    have hnd : (controlsAt cuts cut).Nodup := List.Nodup.filter _ (List.nodup_finRange G)
    by_cases hc : cuts target = cut
    · have hmem : target ∈ controlsAt cuts cut := (mem_controlsAt cuts cut target).mpr hc
      rw [if_pos hc, List.count_eq_one_of_mem hnd hmem]
      rfl
    · have hnot : target ∉ controlsAt cuts cut := by simpa only [mem_controlsAt] using hc
      rw [if_neg hc, List.count_eq_zero_of_not_mem hnot]
      rfl
  have hblock (cut : Fin m) :
      (block old guard cuts cut).filter keep =
        (if cut = cuts target then [guard target] else []) ++ [old cut] := by
    simp only [block, List.filter_append, hresident, List.filter_cons, hold,
      Bool.true_eq, ↓reduceIte, List.filter_nil]
    by_cases hc : cuts target = cut
    · simp only [hc, if_pos rfl]
    · have hcs : cut ≠ cuts target := Ne.symm hc
      simp only [if_neg hc, if_neg hcs]
  have hindex : (cuts target).val < (List.finRange m).length := by simp
  have helem : (List.finRange m)[(cuts target).val]'hindex = cuts target := by
    apply Fin.ext
    simp
  have hr := flatMap_one_insertion (List.finRange m) (List.nodup_finRange m)
    (cuts target).val hindex old (guard target)
  rw [helem] at hr
  rw [render, List.filter_flatMap]
  simpa only [hblock] using hr

/-- A concrete predicate that keeps all old letters and exactly one guard. -/
def keepGuard (old : Fin m → α) (target : α) (x : α) : Bool :=
  decide (x = target ∨ ∃ i, old i = x)

theorem keepGuard_old (old : Fin m → α) (target : α) (i : Fin m) :
    keepGuard old target (old i) = true := by
  simp [keepGuard]

theorem keepGuard_guard (old : Fin m → α) (guard : Fin G → α)
    (hg : Function.Injective guard) (hcross : ∀ j i, guard j ≠ old i)
    (target j : Fin G) : keepGuard old (guard target) (guard j) = decide (j = target) := by
  have hnone : ¬ ∃ i, old i = guard j := by
    rintro ⟨i, hi⟩
    exact hcross j i hi.symm
  simp only [keepGuard, hnone, or_false, hg.eq_iff]

/-- Equality of cyclic guard backgrounds determines the entire labelled
cut map. In particular different injective guard assignments cannot collide. -/
theorem cuts_eq_of_cyclicEq (old : Fin m → α) (guard : Fin G → α)
    (ho : Function.Injective old) (hg : Function.Injective guard)
    (hcross : ∀ j i, guard j ≠ old i)
    (first second : Fin G → Fin m)
    (hcyc : CyclicEq (render old guard first) (render old guard second)) : first = second := by
  funext target
  let keep := keepGuard old (guard target)
  have hfirst := filter_single_guard old guard first target keep
    (keepGuard_old old (guard target)) (keepGuard_guard old guard hg hcross target)
  have hsecond := filter_single_guard old guard second target keep
    (keepGuard_old old (guard target)) (keepGuard_guard old guard hg hcross target)
  have hne : (render old guard first).filter keep ≠ [] := by
    rw [hfirst]
    exact List.length_pos_iff.mp (by simp)
  have hf := hcyc.filter keep hne
  rw [hfirst, hsecond] at hf
  have hnd : ((List.finRange m).map old).Nodup := (List.nodup_finRange m).map ho
  have hfresh : guard target ∉ (List.finRange m).map old := by
    intro hm
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hm
    exact hcross target i he.symm
  apply Fin.ext
  exact (insertLetter_cyclicEq_iff_index_eq hnd hfresh
    (by simpa using (first target).isLt) (by simpa using (second target).isLt)).mp hf

end CoefficientTwoPrecision.GuardBackgrounds

#print axioms CoefficientTwoPrecision.GuardBackgrounds.filter_single_guard
#print axioms CoefficientTwoPrecision.GuardBackgrounds.cuts_eq_of_cyclicEq
