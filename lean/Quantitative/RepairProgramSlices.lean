import Quantitative.CyclicRepairSchedule

/-!
# Locating each constructed repair in the actual target program

For every event group, the compiled program contains the specified block
of parking pairs followed by its normal cleanup. The preceding macros
occupy exactly the chosen starting number of batches. Their normal role
count has the same residue modulo r as that starting time, because every
earlier replacement removes a multiple of r normal batches.

This locates the intervals used by the event proof inside the literal
macro program; it is not a separate assumed execution trace.
-/

namespace CoefficientTwoPrecision.RepairProgramSlices

open RepairIntervals RepairGroups RepairProgram MacroCatalogue

variable {Label : Type*}

theorem compile_contains_repair (r : ℕ)
    (phase : EventGroup (2 * r + 1) Label → ℕ)
    (choice : EventGroup (2 * r + 1) Label → Bool) (stop cursor : ℕ)
    (groups : List (EventGroup (2 * r + 1) Label)) (hr : 0 < r)
    (hphases : ∀ G ∈ groups, phase G < r)
    (hfirst : ∀ G ∈ groups, r ≤ G.first)
    (hcursor : ∀ G ∈ groups, cursor ≤ groupStart r phase G)
    (hbefore : groups.Pairwise Before)
    (target : EventGroup (2 * r + 1) Label) (htarget : target ∈ groups) :
    ∃ beforeProgram suffix : List Macro, ∃ omitted : ℕ,
      compile r phase choice stop cursor groups =
        beforeProgram ++ List.replicate (groupParking r phase target / 2) (.parking (choice target)) ++
          .normal :: suffix ∧
      batchCount beforeProgram = groupStart r phase target - cursor ∧
      r ∣ omitted ∧
      normalCount beforeProgram + omitted = groupStart r phase target - cursor := by
  induction groups generalizing cursor with
  | nil => simp at htarget
  | cons G groups ih =>
    have hpG := hphases G (by simp)
    have hfG := hfirst G (by simp)
    have hcG := hcursor G (by simp)
    obtain ⟨hGbefore, htailBefore⟩ := List.pairwise_cons.mp hbefore
    rcases List.mem_cons.mp htarget with htargetEq | htarget
    · subst G
      refine ⟨List.replicate (groupStart r phase target - cursor) .normal,
        compile r phase choice stop (groupEnd r phase target) groups, 0, rfl, ?_,
        dvd_zero r, ?_⟩
      · exact batchCount_replicate_normal _
      · rw [normalCount_replicate_normal, Nat.add_zero]
    · have hcTail : ∀ H ∈ groups, groupEnd r phase G ≤ groupStart r phase H := by
        intro H hH
        exact groupEnd_le_next r phase G H hr hpG (hphases H (by simp [hH]))
          hfG (hfirst H (by simp [hH])) (hGbefore H hH)
      obtain ⟨beforeProgram, suffix, omitted, hprogram, hbatch, hdiv, hnormal⟩ :=
        ih (groupEnd r phase G)
          (fun H hH => hphases H (List.mem_cons_of_mem G hH))
          (fun H hH => hfirst H (List.mem_cons_of_mem G hH)) hcTail
          htailBefore htarget
      let earlier : List Macro :=
        List.replicate (groupStart r phase G - cursor) .normal ++
        List.replicate (groupParking r phase G / 2) (.parking (choice G)) ++
        .normal :: beforeProgram
      have htargetStart := hcTail target htarget
      have hhalf : 2 * (groupParking r phase G / 2) = groupParking r phase G :=
        Nat.mul_div_cancel' (groupParking_even r phase G)
      refine ⟨earlier, suffix, groupParking r phase G + omitted, ?_, ?_,
        dvd_add (groupParking_dvd r phase G) hdiv, ?_⟩
      · simp only [compile, hprogram, earlier, List.append_assoc, List.cons_append]
      · simp only [earlier, batchCount_append, batchCount_replicate_normal,
          batchCount_replicate_parking, batchCount, hbatch, hhalf]
        dsimp only [groupEnd] at htargetStart ⊢
        omega
      · simp only [earlier, normalCount_append, normalCount_replicate_normal,
          normalCount_replicate_parking, normalCount, Nat.zero_add]
        dsimp only [groupEnd] at hnormal htargetStart
        omega

/-- At the chosen start of each repair, both the actual batch index and
the normal role phase agree with its ordinary event-time coordinate. -/
theorem repair_slice (r M : ℕ)
    (phase : EventGroup (2 * r + 1) Label → ℕ)
    (choice : EventGroup (2 * r + 1) Label → Bool)
    (groups : List (EventGroup (2 * r + 1) Label)) (hr : 0 < r)
    (hphases : ∀ G ∈ groups, phase G < r)
    (hfirst : ∀ G ∈ groups, r ≤ G.first)
    (hbefore : groups.Pairwise Before)
    (G : EventGroup (2 * r + 1) Label) (hG : G ∈ groups) :
    ∃ beforeProgram suffix : List Macro,
      compile r phase choice M 0 groups =
        beforeProgram ++ List.replicate (groupParking r phase G / 2) (.parking (choice G)) ++
          .normal :: suffix ∧
      batchCount beforeProgram = groupStart r phase G ∧
      normalCount beforeProgram % r = phase G := by
  obtain ⟨beforeProgram, suffix, omitted, hprogram, hbatch, hdiv, hnormal⟩ :=
    compile_contains_repair r phase choice M 0 groups hr hphases hfirst
      (fun _ _ => Nat.zero_le _) hbefore G hG
  simp only [Nat.sub_zero] at hbatch hnormal
  have hmod := congrArg (fun x : ℕ => x % r) hnormal
  have homitted := Nat.mod_eq_zero_of_dvd hdiv
  have hphase := (repairStart_bounds r (phase G) G.first hr (hphases G hG) (hfirst G hG)).2.2
  simp only [Nat.add_mod, homitted, Nat.add_zero, Nat.mod_mod] at hmod
  exact ⟨beforeProgram, suffix, hprogram, hbatch, hmod.trans hphase⟩

end CoefficientTwoPrecision.RepairProgramSlices

#print axioms CoefficientTwoPrecision.RepairProgramSlices.compile_contains_repair
#print axioms CoefficientTwoPrecision.RepairProgramSlices.repair_slice
