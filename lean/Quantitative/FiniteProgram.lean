import Quantitative.MacroCatalogue
import Quantitative.NormalContour
import Quantitative.RepairProgram

/-!
# Actual finite target batches for a permitted macro program

The catalogue program uses natural-number targets. Here every target is
constructed as an element of Fin k, and every batch is proved to be a
permutation of all k slots. Flattening and forgetting the bounds recovers
the exact catalogue word. The count, role-return, and final-target facts
required by the literal closed-trace construction are therefore concrete.
-/

namespace CoefficientTwoPrecision.FiniteProgram

open PositiveParking JointStates MacroCatalogue NormalContour LiteralSchedule PositiveSchedule
open RepairProgram RepairIntervals RepairGroups

def swapTwo {β : Type} : List β → List β
  | a :: b :: tail => b :: a :: tail
  | word => word

theorem swapTwo_perm {β : Type} (word : List β) : (swapTwo word).Perm word := by
  cases word with
  | nil => exact List.Perm.refl []
  | cons a tail =>
    cases tail with
    | nil => exact List.Perm.refl [a]
    | cons b tail => exact List.Perm.swap a b tail

def finiteMenu (k : Nat) : Bool → List (Fin k)
  | false => List.finRange k
  | true => swapTwo (List.finRange k)

theorem finiteMenu_perm (k : Nat) (choice : Bool) :
    (finiteMenu k choice).Perm (List.finRange k) := by
  cases choice
  · exact List.Perm.refl _
  · exact swapTwo_perm _

theorem swapTwo_map_val {k : Nat} (word : List (Fin k)) :
    (swapTwo word).map Fin.val = swapFirstTwo (word.map Fin.val) := by
  cases word with
  | nil => rfl
  | cons a tail => cases tail <;> rfl

theorem finiteMenu_map (k : Nat) (choice : Bool) :
    (finiteMenu k choice).map Fin.val = menu (List.range k) choice := by
  cases choice
  · exact map_finRange_val k
  · rw [finiteMenu, swapTwo_map_val, map_finRange_val]
    rfl

def macroBatches (k : Nat) : Macro → List (List (Fin k))
  | .normal => [List.finRange k]
  | .parking choice => [finiteMenu k choice, (finiteMenu k choice).reverse]

def batches (k : Nat) (program : List Macro) : List (List (Fin k)) :=
  program.flatMap (macroBatches k)

def word (k : Nat) (program : List Macro) : List (Fin k) := (batches k program).flatten

theorem batches_orders (k : Nat) (program : List Macro) :
    ∀ order ∈ batches k program, order.Perm (List.finRange k) := by
  intro order horder
  obtain ⟨instruction, _, hmember⟩ := List.mem_flatMap.mp horder
  cases instruction with
  | normal =>
    have heq : order = List.finRange k := by simpa only [macroBatches, List.mem_singleton] using hmember
    rw [heq]
  | parking choice =>
    simp only [macroBatches, List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with rfl | rfl
    · exact finiteMenu_perm k choice
    · exact (List.reverse_perm _).trans (finiteMenu_perm k choice)

theorem batches_length (k : Nat) (program : List Macro) : (batches k program).length = batchCount program := by
  induction program with
  | nil => rfl
  | cons instruction program ih =>
    cases instruction <;> simp only [batches, List.flatMap_cons, List.length_append, macroBatches,
      List.length_cons, List.length_nil, batchCount] at * <;> omega

theorem word_map (k : Nat) (program : List Macro) : (word k program).map Fin.val = programWord k program := by
  induction program with
  | nil => rfl
  | cons instruction program ih =>
    cases instruction with
    | normal =>
      change ((List.finRange k ++ word k program).map Fin.val) = List.range k ++ programWord k program
      rw [List.map_append, map_finRange_val, ih]
    | parking choice =>
      change ((finiteMenu k choice ++ ((finiteMenu k choice).reverse ++ word k program)).map Fin.val) =
        (menu (List.range k) choice ++ (menu (List.range k) choice).reverse) ++ programWord k program
      rw [List.map_append, List.map_append, List.map_reverse, finiteMenu_map, ih, List.append_assoc]

theorem word_append (k : Nat) (first last : List Macro) :
    word k (first ++ last) = word k first ++ word k last := by
  simp only [word, batches, List.flatMap_append, List.flatten_append]

theorem word_count (k : Nat) (program : List Macro) (target : Fin k) :
    (word k program).count target = batchCount program := by
  have h := program_count k program target.val target.isLt
  rw [← word_map, List.count_map_of_injective _ Fin.val Fin.val_injective target] at h
  exact h

theorem program_labels {α : Type} (k : Nat) (program : List Macro) (labels : Option Nat → α) :
    executeLabels (word k program) labels =
      execute updateLabels (repeatWord (normalCount program) (List.range k)) labels := by
  rw [executeLabels_eq_execute, word_map]
  induction program generalizing labels with
  | nil => rfl
  | cons instruction program ih =>
    cases instruction with
    | normal =>
      simp only [programWord, List.flatMap_cons, macroWord, execute_append, normalCount, repeatWord]
      exact ih _
    | parking choice =>
      change execute updateLabels
        ((menu (List.range k) choice ++ (menu (List.range k) choice).reverse) ++ programWord k program) labels = _
      rw [execute_append, parking_restores_all_labels]
      exact ih labels

theorem program_labels_return {α : Type} (k : Nat) (program : List Macro)
    (hdiv : k + 1 ∣ normalCount program) (labels : Option Nat → α) :
    executeLabels (word k program) labels = labels := by
  rw [program_labels]
  obtain ⟨cycles, hcycles⟩ := hdiv
  rw [hcycles, Nat.mul_comm]
  exact execute_multiple_period updateLabels (List.range k) (k + 1)
    (normal_labels_period k) cycles labels

theorem finRange_last (k : Nat) (hk : 0 < k) :
    (List.finRange k).getLast? = some (⟨k - 1, by omega⟩ : Fin k) := by
  rw [List.getLast?_eq_getElem?, List.length_finRange,
    List.getElem?_eq_getElem (by simp only [List.length_finRange]; omega), List.getElem_finRange]
  rfl

theorem word_last_normal (k : Nat) (hk : 0 < k) (program : List Macro) :
    (word k (program ++ [.normal])).getLast? = some (⟨k - 1, by omega⟩ : Fin k) := by
  rw [word_append]
  have hsingle : word k [.normal] = List.finRange k := by simp [word, batches, macroBatches]
  rw [hsingle]
  rw [List.getLast?_append, finRange_last k hk]
  rfl

theorem word_first_normal (k : Nat) (program : List Macro) :
    word k (.normal :: program) = List.finRange k ++ word k program := rfl

/-- The safe cut leaves an actual untouched normal batch at the beginning
of the compiled program, before the first parking interval. -/
theorem compile_starts_normal {Label : Type*} (r M : Nat) (hr : 0 < r) (hM : 0 < M)
    (phase : EventGroup (2 * r + 1) Label → Nat)
    (choice : EventGroup (2 * r + 1) Label → Bool)
    (groups : List (EventGroup (2 * r + 1) Label))
    (hphase : ∀ G ∈ groups, phase G < r)
    (hfirst : ∀ G ∈ groups, r < G.first) :
    ∃ rest, compile r phase choice M 0 groups = .normal :: rest := by
  cases groups with
  | nil =>
    refine ⟨List.replicate (M - 1) .normal, ?_⟩
    change List.replicate (M - 0) Macro.normal = _
    conv_lhs => rw [Nat.sub_zero, show M = (M - 1) + 1 by omega, List.replicate_succ]
  | cons G groups =>
    have hbound := (repairStart_bounds r (phase G) G.first hr (hphase G (by simp))
      (Nat.le_of_lt (hfirst G (by simp)))).1
    have hpositive : 0 < groupStart r phase G := by dsimp only [groupStart]; have := hfirst G (by simp); omega
    refine ⟨List.replicate (groupStart r phase G - 1) .normal ++
      List.replicate (groupParking r phase G / 2) (.parking (choice G)) ++
      .normal :: compile r phase choice M (groupEnd r phase G) groups, ?_⟩
    simp only [compile, Nat.sub_zero]
    conv_lhs => rw [show groupStart r phase G = (groupStart r phase G - 1) + 1 by omega,
      List.replicate_succ]
    simp only [List.cons_append]

end CoefficientTwoPrecision.FiniteProgram

#print axioms CoefficientTwoPrecision.FiniteProgram.word_map
#print axioms CoefficientTwoPrecision.FiniteProgram.word_count
#print axioms CoefficientTwoPrecision.FiniteProgram.program_labels_return
#print axioms CoefficientTwoPrecision.FiniteProgram.compile_starts_normal
