import Quantitative.TargetTrace
import Quantitative.JointStates

/-!
# The joint catalogue contains every permitted program prefix

A macro is one normal batch or one parking pair from the two-order menu.
The program is an actual concatenated target word. Its whole macros have
a uniform cut increment and the role action of its normal macros alone.
Every proper prefix lies inside one macro, where both its role action and
its phase vector are represented by one joint catalogue element.
-/

namespace CoefficientTwoPrecision.MacroCatalogue

open PositiveParking JointStates

inductive Macro where
  | normal
  | parking (choice : Bool)
  deriving DecidableEq

def macroWord (k : Nat) : Macro → List Nat
  | .normal => List.range k
  | .parking choice => menu (List.range k) choice ++ (menu (List.range k) choice).reverse

def programWord (k : Nat) (program : List Macro) : List Nat :=
  program.flatMap (macroWord k)

def normalCount : List Macro → Nat
  | [] => 0
  | .normal :: rest => normalCount rest + 1
  | .parking _ :: rest => normalCount rest

def batchCount : List Macro → Nat
  | [] => 0
  | .normal :: rest => 1 + batchCount rest
  | .parking _ :: rest => 2 + batchCount rest

theorem menu_perm (k : Nat) (choice : Bool) :
    (menu (List.range k) choice).Perm (List.range k) := by
  cases choice
  · exact List.Perm.refl _
  · exact swapFirstTwo_perm _

theorem menu_count (k a : Nat) (ha : a < k) (choice : Bool) :
    (menu (List.range k) choice).count a = 1 := by
  rw [(menu_perm k choice).count_eq]
  exact List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr ha)

theorem program_action (k : Nat) (program : List Macro) (initial : Assignment) :
    execute updateLabels (programWord k program) initial =
      execute updateLabels (repeatWord (normalCount program) (List.range k)) initial := by
  induction program generalizing initial with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction with
    | normal =>
      simp only [programWord, List.flatMap_cons, macroWord, execute_append,
        normalCount, repeatWord]
      exact ih _
    | parking choice =>
      change execute updateLabels
        ((menu (List.range k) choice ++ (menu (List.range k) choice).reverse) ++
          programWord k rest) initial = _
      rw [execute_append, parking_restores_all_labels]
      exact ih initial

theorem program_count (k : Nat) (program : List Macro) (a : Nat) (ha : a < k) :
    (programWord k program).count a = batchCount program := by
  induction program with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction with
    | normal =>
      have hone : (List.range k).count a = 1 :=
        List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr ha)
      change ((List.range k) ++ programWord k rest).count a = 1 + batchCount rest
      rw [List.count_append, hone, ih]
    | parking choice =>
      change ((menu (List.range k) choice ++ (menu (List.range k) choice).reverse) ++
        programWord k rest).count a = 2 + batchCount rest
      simp only [List.count_append, List.count_reverse, menu_count k a ha choice, ih]

theorem normalBoundary_mod (k n : Nat) :
    normalBoundary (List.range k) n = normalBoundary (List.range k) (n % (k + 1)) := by
  have hsplit : n = n % (k + 1) + (n / (k + 1)) * (k + 1) := by
    simpa only [Nat.mul_comm] using (Nat.mod_add_div n (k + 1)).symm
  unfold normalBoundary
  conv_lhs => rw [hsplit, repeatWord_add, execute_append]
  exact execute_multiple_period updateLabels (List.range k) (k + 1)
    (normal_labels_period k) (n / (k + 1)) _

/-- A list prefix that ends before the whole program lies in one macro. -/
theorem prefix_view (k : Nat) (program : List Macro) (n : Nat)
    (hn : n < (programWord k program).length) :
    ∃ before instruction after ell,
      program = before ++ instruction :: after ∧
      ell < (macroWord k instruction).length ∧
      (programWord k program).take n =
        programWord k before ++ (macroWord k instruction).take ell := by
  induction program generalizing n with
  | nil => simp [programWord] at hn
  | cons instruction rest ih =>
    change n < (macroWord k instruction ++ programWord k rest).length at hn
    by_cases hlocal : n < (macroWord k instruction).length
    · refine ⟨[], instruction, rest, n, rfl, hlocal, ?_⟩
      exact List.take_append_of_le_length hlocal.le
    · have hrest : n - (macroWord k instruction).length < (programWord k rest).length := by
        rw [List.length_append] at hn
        omega
      obtain ⟨before, next, after, ell, hprogram, hell, htake⟩ := ih _ hrest
      refine ⟨instruction :: before, next, after, ell, ?_, hell, ?_⟩
      · simp only [List.cons_append, hprogram]
      · have hn' : n = (macroWord k instruction).length +
            (n - (macroWord k instruction).length) := by omega
        change (macroWord k instruction ++ programWord k rest).take n = _
        rw [hn', List.take_length_add_append, htake]
        simp only [programWord, List.flatMap_cons, List.append_assoc]

/-- Cut increments in a proper parking prefix split at the midpoint.
The role action is not reset at that midpoint. -/
theorem parking_prefix_counts (k : Nat) (choice : Bool) (ell : Nat) (hell : ell < 2 * k) :
    ∃ completed : Nat, ∀ a < k,
      (pairPrefix (menu (List.range k) choice) ell).count a =
        completed + phase (menu (List.range k) choice) ell a := by
  have hlen : (menu (List.range k) choice).length = k := by
    rw [menu_length, List.length_range]
  by_cases hfirst : ell < k
  · refine ⟨0, ?_⟩
    intro a ha
    rw [pairPrefix_first_half _ _ (by omega)]
    simp only [phase, hlen, hfirst, ↓reduceIte, Nat.zero_add]
  · refine ⟨1, ?_⟩
    intro a ha
    have heq : ell = (menu (List.range k) choice).length + (ell - k) := by omega
    rw [heq, pairPrefix_second_half, List.count_append, menu_count k a ha choice]
    have hsecond : (menu (List.range k) choice).length + (ell - k) <
        2 * (menu (List.range k) choice).length := by omega
    have hnfirst : ¬ (menu (List.range k) choice).length + (ell - k) <
        (menu (List.range k) choice).length := by omega
    simp only [phase, hnfirst, ↓reduceIte, hsecond, Nat.add_sub_cancel_left]

/-- The single catalogue element records both the full role action and
the cut phases of a proper program prefix. -/
theorem proper_prefix_state (k : Nat) (program : List Macro) (n : Nat)
    (hn : n < (programWord k program).length) :
    ∃ state ∈ catalogue k (List.range k), ∃ translation : Nat,
      execute updateLabels ((programWord k program).take n) (id : Assignment) = state.labels ∧
      ∀ a < k, ((programWord k program).take n).count a = translation + state.phases a := by
  obtain ⟨before, instruction, after, ell, _, hell, htake⟩ := prefix_view k program n hn
  rw [htake]
  let s := normalCount before % (k + 1)
  have hs : s < k + 1 := Nat.mod_lt _ (by omega)
  have hboundary : execute updateLabels (programWord k before) (id : Assignment) =
      normalBoundary (List.range k) s := by
    rw [program_action]
    exact normalBoundary_mod k (normalCount before)
  cases instruction with
  | normal =>
    have hell' : ell < k := by simpa only [macroWord, List.length_range] using hell
    let state : State := {
      labels := execute updateLabels ((List.range k).take ell) (normalBoundary (List.range k) s)
      phases := fun a => ((List.range k).take ell).count a }
    refine ⟨state, normal_prefix_mem k (List.range k) s ell List.length_range hs hell',
      batchCount before, ?_, ?_⟩
    · rw [execute_append, hboundary]
      rfl
    · intro a ha
      rw [List.count_append, program_count k before a ha]
      rfl
  | parking choice =>
    have hell' : ell < 2 * k := by
      simpa only [macroWord, List.length_append, List.length_reverse, menu_length,
        List.length_range, Nat.two_mul] using hell
    let state := joint (List.range k) s (menu (List.range k) choice) ell
    obtain ⟨completed, hcounts⟩ := parking_prefix_counts k choice ell hell'
    refine ⟨state, pair_prefix_mem k (List.range k) s ell choice hs hell'.le,
      batchCount before + completed, ?_, ?_⟩
    · rw [execute_append, hboundary]
      rfl
    · intro a ha
      rw [List.count_append, program_count k before a ha]
      change batchCount before + (pairPrefix (menu (List.range k) choice) ell).count a = _
      rw [hcounts a ha]
      exact (Nat.add_assoc _ _ _).symm

end CoefficientTwoPrecision.MacroCatalogue

#print axioms CoefficientTwoPrecision.MacroCatalogue.program_action
#print axioms CoefficientTwoPrecision.MacroCatalogue.proper_prefix_state
