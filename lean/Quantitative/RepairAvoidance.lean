import Quantitative.RepairProgramSlices

/-!
# Actual forbidden-role avoidance in the compiled repair program

A forbidden pair consists of a named initial role and a stationary slot.
The normal role cycle gives an explicit phase at which that named role is
mobile. The two-menu construction gives an explicit parking order whose
first target is different from the forbidden slot.

The final theorem applies these choices to the actual program produced by
`RepairProgram.compile`. It identifies the parking block with a literal
target-word prefix and proves avoidance at every update boundary in that
block. Both the forward position of the protected role and the inverse
assignment of the forbidden slot are controlled.
-/

namespace CoefficientTwoPrecision.RepairAvoidance

open PositiveParking JointStates MacroCatalogue RepairIntervals RepairGroups
open RepairProgram RepairProgramSlices

/-- The residue at which the named initial role reaches the mobile role
under the canonical normal cycle. -/
def mobilePhase (k : ℕ) (role : Option ℕ) : ℕ :=
  (k + 1 - roleIndex role) % (k + 1)

theorem mobilePhase_lt (k : ℕ) (role : Option ℕ) : mobilePhase k role < k + 1 :=
  Nat.mod_lt _ (Nat.succ_pos _)

theorem mobilePhase_mobile (k : ℕ) (role : Option ℕ) (hrole : roleIndex role ≤ k) :
    execute PositiveParking.star (repeatWord (mobilePhase k role) (List.range k)) role = none := by
  apply roleIndex_injective
  rw [normal_repeated_roleIndex k (mobilePhase k role) role hrole]
  change (roleIndex role + mobilePhase k role) % (k + 1) = 0
  by_cases hzero : roleIndex role = 0
  · simp [mobilePhase, hzero]
  · have hsmall : k + 1 - roleIndex role < k + 1 := by omega
    rw [mobilePhase, Nat.mod_eq_of_lt hsmall]
    have hsum : roleIndex role + (k + 1 - roleIndex role) = k + 1 := by omega
    rw [hsum, Nat.mod_self]

/-- Use the order beginning at slot one exactly when slot zero is
forbidden; otherwise the normal order beginning at zero is suitable. -/
def parkingChoice (forbidden : ℕ) : Bool := decide (forbidden = 0)

theorem parkingChoice_safe (k forbidden : ℕ) (hk : 2 ≤ k) :
    (menu (List.range k) (parkingChoice forbidden)).head? ≠ some forbidden := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  by_cases hforbidden : forbidden = 0
  · subst forbidden
    simp [parkingChoice, menu, swapFirstTwo, List.range_succ_eq_map]
  · simp [parkingChoice, hforbidden, menu, List.range_succ_eq_map, Ne.symm hforbidden]

theorem program_position_action (k : ℕ) (program : List Macro) (role : Option ℕ) :
    execute PositiveParking.star (programWord k program) role =
      execute PositiveParking.star (repeatWord (normalCount program) (List.range k)) role := by
  induction program generalizing role with
  | nil => rfl
  | cons instruction program ih =>
    cases instruction with
    | normal =>
      simp only [programWord, List.flatMap_cons, macroWord, execute_append,
        normalCount, repeatWord]
      exact ih _
    | parking choice =>
      change execute PositiveParking.star
        ((menu (List.range k) choice ++ (menu (List.range k) choice).reverse) ++
          programWord k program) role = _
      rw [execute_append, execute_reverse_cancel PositiveParking.star PositiveParking.star_involutive]
      exact ih role

theorem normal_position_mod (k count : ℕ) (role : Option ℕ) :
    execute PositiveParking.star (repeatWord count (List.range k)) role =
      execute PositiveParking.star (repeatWord (count % (k + 1)) (List.range k)) role := by
  have hsplit : count = count % (k + 1) + (count / (k + 1)) * (k + 1) := by
    simpa only [Nat.mul_comm] using (Nat.mod_add_div count (k + 1)).symm
  conv_lhs => rw [hsplit, repeatWord_add, execute_append]
  exact execute_multiple_period PositiveParking.star (List.range k) (k + 1)
    (normal_position_period k) (count / (k + 1)) _

theorem program_phase_mobile (k : ℕ) (program : List Macro) (role : Option ℕ)
    (hrole : roleIndex role ≤ k) (hphase : normalCount program % (k + 1) = mobilePhase k role) :
    execute PositiveParking.star (programWord k program) role = none := by
  rw [program_position_action, normal_position_mod, hphase]
  exact mobilePhase_mobile k role hrole

/-- Every prefix endpoint is either the initial position or one of the
positions actually visited while executing the full target word. -/
theorem take_position (word : List ℕ) (role : Option ℕ) (t : ℕ) :
    execute PositiveParking.star (word.take t) role = role ∨
      execute PositiveParking.star (word.take t) role ∈ positions word role := by
  induction word generalizing role t with
  | nil => simp [positions]
  | cons target word ih =>
    cases t with
    | zero => exact Or.inl rfl
    | succ t =>
      change execute PositiveParking.star (word.take t) (PositiveParking.star target role) = role ∨
        execute PositiveParking.star (word.take t) (PositiveParking.star target role) ∈
          PositiveParking.star target role :: positions word (PositiveParking.star target role)
      rcases ih (PositiveParking.star target role) t with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))

theorem chosen_parking_prefix_avoids (k forbidden pairs t : ℕ) (hk : 2 ≤ k) :
    execute PositiveParking.star
      ((repeatWord pairs
        (menu (List.range k) (parkingChoice forbidden) ++
          (menu (List.range k) (parkingChoice forbidden)).reverse)).take t) none ≠
      some forbidden := by
  let order := menu (List.range k) (parkingChoice forbidden)
  have hlength : order.length = k := by simp only [order, menu_length, List.length_range]
  have hnodup : order.Nodup := (menu_perm k (parkingChoice forbidden)).nodup_iff.mpr List.nodup_range
  have hfirst := parkingChoice_safe k forbidden hk
  cases horder : order with
  | nil => simp only [horder, List.length_nil] at hlength; omega
  | cons first rest =>
    have hfirstNe : first ≠ forbidden := by
      change order.head? ≠ some forbidden at hfirst
      rw [horder] at hfirst
      simpa only [List.head?_cons, ne_eq, Option.some.injEq] using hfirst
    have hrest : first ∉ rest := (List.nodup_cons.mp (horder ▸ hnodup)).1
    have havoid := repeated_parking_avoids first forbidden rest hrest hfirstNe pairs
    change execute PositiveParking.star ((repeatWord pairs (order ++ order.reverse)).take t) none ≠ some forbidden
    rw [horder]
    intro heq
    rcases take_position (repeatWord pairs ((first :: rest) ++ (first :: rest).reverse)) none t with h | h
    · rw [heq] at h
      cases h
    · rw [heq] at h
      exact havoid h

theorem programWord_append (k : ℕ) (first second : List Macro) :
    programWord k (first ++ second) = programWord k first ++ programWord k second := by
  simp only [programWord, List.flatMap_append]

theorem parking_programWord (k pairs : ℕ) (choice : Bool) :
    programWord k (List.replicate pairs (Macro.parking choice)) =
      repeatWord pairs (menu (List.range k) choice ++ (menu (List.range k) choice).reverse) := by
  induction pairs with
  | zero => rfl
  | succ pairs ih =>
    change (menu (List.range k) choice ++ (menu (List.range k) choice).reverse) ++
        programWord k (List.replicate pairs (Macro.parking choice)) =
      (menu (List.range k) choice ++ (menu (List.range k) choice).reverse) ++
        repeatWord pairs (menu (List.range k) choice ++ (menu (List.range k) choice).reverse)
    rw [ih]

theorem labels_injective (word : List ℕ) (assignment : Option ℕ → Option ℕ)
    (hinjective : Function.Injective assignment) :
    Function.Injective (execute updateLabels word assignment) := by
  induction word generalizing assignment with
  | nil => exact hinjective
  | cons target word ih =>
    apply ih
    intro p q hpq
    have hstar := hinjective hpq
    have h := congrArg (PositiveParking.star target) hstar
    simpa only [PositiveParking.star_involutive] using h

theorem label_avoids_of_position_avoids (word : List ℕ) (role : Option ℕ) (forbidden : ℕ)
    (hposition : execute PositiveParking.star word role ≠ some forbidden) :
    (execute updateLabels word id) (some forbidden) ≠ role := by
  intro heq
  have hfollow := labels_follow_positions word id role
  have hinjective := labels_injective word id Function.injective_id
  exact hposition (hinjective (hfollow.trans heq.symm))

abbrev ForbiddenPair := Option ℕ × ℕ

def groupPhase (k : ℕ) (G : EventGroup (2 * (k + 1) + 1) ForbiddenPair) : ℕ :=
  mobilePhase k G.label.1

def groupChoice (k : ℕ) (G : EventGroup (2 * (k + 1) + 1) ForbiddenPair) : Bool :=
  parkingChoice G.label.2

/-- Every update boundary in a group's actual compiled parking block
avoids that group's forbidden pair. The displayed word is a prefix of the
full compiled target word, not an independently supplied execution. -/
theorem compiled_repair_avoids (k M : ℕ) (hk : 2 ≤ k)
    (groups : List (EventGroup (2 * (k + 1) + 1) ForbiddenPair))
    (hfirst : ∀ G ∈ groups, k + 1 ≤ G.first) (hbefore : groups.Pairwise Before)
    (G : EventGroup (2 * (k + 1) + 1) ForbiddenPair) (hG : G ∈ groups)
    (hrole : roleIndex G.label.1 ≤ k) :
    ∃ beforeProgram afterProgram : List Macro,
      compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups =
        beforeProgram ++
          List.replicate (groupParking (k + 1) (groupPhase k) G / 2) (Macro.parking (groupChoice k G)) ++
          .normal :: afterProgram ∧
      batchCount beforeProgram = groupStart (k + 1) (groupPhase k) G ∧
      ∀ t ≤ (programWord k
          (List.replicate (groupParking (k + 1) (groupPhase k) G / 2) (Macro.parking (groupChoice k G)))).length,
        let word := (programWord k (compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups)).take
          ((programWord k beforeProgram).length + t)
        execute PositiveParking.star word G.label.1 ≠ some G.label.2 ∧
          (execute updateLabels word id) (some G.label.2) ≠ G.label.1 := by
  obtain ⟨beforeProgram, afterProgram, hprogram, hbatch, hphase⟩ :=
    repair_slice (k + 1) M (groupPhase k) (groupChoice k) groups (Nat.succ_pos _)
      (fun H _ => mobilePhase_lt k H.label.1) hfirst hbefore G hG
  have hmobile : execute PositiveParking.star (programWord k beforeProgram) G.label.1 = none :=
    program_phase_mobile k beforeProgram G.label.1 hrole hphase
  refine ⟨beforeProgram, afterProgram, hprogram, hbatch, ?_⟩
  intro t ht
  let parking : List Macro := List.replicate
    (groupParking (k + 1) (groupPhase k) G / 2) (Macro.parking (groupChoice k G))
  have hword : programWord k (compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups) =
      programWord k beforeProgram ++ (programWord k parking ++ programWord k (.normal :: afterProgram)) := by
    rw [hprogram, programWord_append, programWord_append]
    simp only [parking, List.append_assoc]
  have htake : (programWord k (compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups)).take
      ((programWord k beforeProgram).length + t) =
      programWord k beforeProgram ++ (programWord k parking).take t := by
    rw [hword, List.take_length_add_append, List.take_append_of_le_length ht]
  have hposition : execute PositiveParking.star
      ((programWord k (compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups)).take
        ((programWord k beforeProgram).length + t)) G.label.1 ≠ some G.label.2 := by
    rw [htake, execute_append, hmobile]
    dsimp only [parking]
    rw [parking_programWord]
    exact chosen_parking_prefix_avoids k G.label.2
      (groupParking (k + 1) (groupPhase k) G / 2) t hk
  exact ⟨hposition, label_avoids_of_position_avoids _ _ _ hposition⟩

end CoefficientTwoPrecision.RepairAvoidance

#print axioms CoefficientTwoPrecision.RepairAvoidance.mobilePhase_mobile
#print axioms CoefficientTwoPrecision.RepairAvoidance.chosen_parking_prefix_avoids
#print axioms CoefficientTwoPrecision.RepairAvoidance.compiled_repair_avoids
