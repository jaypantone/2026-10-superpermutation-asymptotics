import Quantitative.TranslatedControlOrder
import Quantitative.TargetTrace

/-!
# The actual background crossings of a complete target schedule

Each crossing records the target slot and its current cut before that
slot advances. The order of the target word affects the chronological
crossing list, but not its inventory. A slot used M times crosses the
entire background circle exactly once. Consequently, when every one of
the k slots is used M times, every background symbol has exactly k
exceptional short updates.
-/

namespace CoefficientTwoPrecision.CrossingInventory

open LiteralSchedule StationaryUpdate StationarySuccessor PositiveSchedule

variable {M k : Nat}

def orbit (hM : 0 < M) (start : Fin M) : Nat → List (Fin M)
  | 0 => []
  | n + 1 => start :: orbit hM (successor hM start) n

def crossings (hM : 0 < M) : List (Fin k) → (Fin k → Fin M) → List (Fin k × Fin M)
  | [], _ => []
  | target :: word, cuts =>
      (target, cuts target) :: crossings hM word (advanceCuts hM target cuts)

theorem orbit_formula (hM : 0 < M) (start : Fin M) (n : Nat) :
    orbit hM start n =
      (List.range n).map (fun i => (⟨(start.val + i) % M, Nat.mod_lt _ hM⟩ : Fin M)) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [orbit, List.range_succ_eq_map, List.map_cons, List.map_map, ih]
    congr 1
    · apply Fin.ext
      simp only [Nat.add_zero, Nat.mod_eq_of_lt start.isLt]
    · apply List.map_congr_left
      intro i _
      apply Fin.ext
      change (((start.val + 1) % M + i) % M) = (start.val + (i + 1)) % M
      rw [Nat.mod_add_mod]
      congr 1
      omega

theorem orbit_full [NeZero M] (start : Fin M) :
    (orbit (NeZero.pos M) start M).Perm (List.finRange M) := by
  have heq : orbit (NeZero.pos M) start M =
      (List.finRange M).map (fun cut => cut + start) := by
    rw [orbit_formula]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.val_cast]
      rw [Nat.add_comm]
  rw [heq, TranslatedControlOrder.finRange_translate]
  exact List.rotate_perm _ _

/-- Remove the first item from one designated block in a flat list. -/
theorem flatMap_pop {β γ : Type} [DecidableEq β]
    (order : List β) (hnd : order.Nodup) (target : β) (hmem : target ∈ order)
    (first rest : β → List γ) (item : γ)
    (hat : first target = item :: rest target)
    (hother : ∀ j, j ≠ target → first j = rest j) :
    (order.flatMap first).Perm (item :: order.flatMap rest) := by
  induction order with
  | nil => simp at hmem
  | cons j order ih =>
    have hnd' := List.nodup_cons.mp hnd
    by_cases hj : j = target
    · subst j
      have htail : order.flatMap first = order.flatMap rest := by
        apply List.flatMap_congr
        intro a ha
        exact hother a (fun heq => hnd'.1 (heq ▸ ha))
      simp only [List.flatMap_cons, hat, List.cons_append, htail]
      exact List.Perm.refl _
    · have ht : target ∈ order := by
        exact (List.mem_cons.mp hmem).resolve_left (Ne.symm hj)
      simp only [List.flatMap_cons, hother j hj]
      exact ((ih hnd'.2 ht).append_left (rest j)).trans List.perm_middle

theorem crossings_inventory (hM : 0 < M) (word : List (Fin k)) (cuts : Fin k → Fin M) :
    (crossings hM word cuts).Perm
      ((List.finRange k).flatMap (fun target =>
        (orbit hM (cuts target) (word.count target)).map (fun cut => (target, cut)))) := by
  induction word generalizing cuts with
  | nil => simp [crossings, orbit]
  | cons target word ih =>
    let old := fun j : Fin k =>
      (orbit hM (cuts j) ((target :: word).count j)).map (fun cut => (j, cut))
    let new := fun j : Fin k =>
      (orbit hM (advanceCuts hM target cuts j) (word.count j)).map (fun cut => (j, cut))
    have hat : old target = (target, cuts target) :: new target := by
      simp only [old, new, List.count_cons_self, orbit, List.map_cons,
        advanceCuts, moveCut, ↓reduceIte]
    have hother : ∀ j, j ≠ target → old j = new j := by
      intro j hj
      simp only [old, new, List.count_cons_of_ne (Ne.symm hj), advanceCuts, moveCut, if_neg hj]
    have hpop := flatMap_pop (List.finRange k) (List.nodup_finRange k) target
      (List.mem_finRange target) old new (target, cuts target) hat hother
    exact ((ih (advanceCuts hM target cuts)).cons (target, cuts target)).trans hpop.symm

theorem flatMap_perm {β γ : Type} (order : List β) (first second : β → List γ)
    (h : ∀ i ∈ order, (first i).Perm (second i)) :
    (order.flatMap first).Perm (order.flatMap second) := by
  induction order with
  | nil => exact List.Perm.refl []
  | cons i order ih =>
    exact (h i (by simp)).append (ih (fun j hj => h j (by simp [hj])))

/-- The actual chronological list has exactly one crossing of each pair
consisting of a stationary slot and a background symbol. -/
theorem complete_inventory [NeZero M] (word : List (Fin k)) (cuts : Fin k → Fin M)
    (hcounts : ∀ target, word.count target = M) :
    (crossings (NeZero.pos M) word cuts).Perm
      ((List.finRange k).flatMap (fun target => (List.finRange M).map (fun cut => (target, cut)))) := by
  apply (crossings_inventory (NeZero.pos M) word cuts).trans
  apply flatMap_perm
  intro target _
  rw [hcounts target]
  exact (orbit_full (cuts target)).map (fun cut => (target, cut))

theorem complete_background_count [NeZero M] (word : List (Fin k)) (cuts : Fin k → Fin M)
    (hcounts : ∀ target, word.count target = M) (background : Fin M) :
    ((crossings (NeZero.pos M) word cuts).map Prod.snd).count background = k := by
  have h := (complete_inventory word cuts hcounts).map Prod.snd
  rw [h.count_eq]
  simp only [List.map_flatMap, List.map_map, Function.comp_def, List.map_id_fun', id_eq]
  have hcount : (List.finRange M).count background = 1 :=
    List.count_eq_one_of_mem (List.nodup_finRange M) (List.mem_finRange background)
  have hsum (order : List (Fin k)) :
      (order.flatMap (fun _ => List.finRange M)).count background = order.length := by
    induction order with
    | nil => simp
    | cons target order ih => simp only [List.flatMap_cons, List.count_append, hcount, ih, List.length_cons]; omega
  simpa only [List.length_finRange] using hsum (List.finRange k)

/-- The indexed crossing is the same cut appearing in the actual target
suffix of `TraceSteps.trace_step`. -/
theorem crossing_at (hM : 0 < M) (word : List (Fin k)) (cuts : Fin k → Fin M) (n : Nat) :
    (crossings hM word cuts)[n]? =
      (word[n]?).map (fun target => (target, executeCuts hM (word.take n) cuts target)) := by
  induction word generalizing cuts n with
  | nil => simp [crossings]
  | cons target word ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simpa only [crossings, List.getElem?_cons_succ, List.take_succ_cons, executeCuts] using
        (ih (advanceCuts hM target cuts) n)

end CoefficientTwoPrecision.CrossingInventory

#print axioms CoefficientTwoPrecision.CrossingInventory.complete_inventory
#print axioms CoefficientTwoPrecision.CrossingInventory.complete_background_count
#print axioms CoefficientTwoPrecision.CrossingInventory.crossing_at
