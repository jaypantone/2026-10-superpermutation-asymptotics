import Quantitative.RepairAvoidance

/-!
# Every actual event batch lies inside its compiled parking block

The grouped event list determines the parking intervals. An update
prefix in an event batch lies after the group's start and before its
parking block ends. The existing literal parking theorem therefore
applies to this prefix of the full compiled program.
-/

namespace CoefficientTwoPrecision.CompiledEventAvoidance

open PositiveParking JointStates MacroCatalogue RepairIntervals RepairGroups
open RepairProgram RepairAvoidance

theorem programWord_length (k : Nat) (program : List Macro) :
    (programWord k program).length = k * batchCount program := by
  induction program with
  | nil => simp [programWord, batchCount]
  | cons instruction rest ih =>
      cases instruction with
      | normal =>
          change (List.range k ++ programWord k rest).length = k * (1 + batchCount rest)
          rw [List.length_append, List.length_range, ih]
          ring
      | parking choice =>
          change ((menu (List.range k) choice ++ (menu (List.range k) choice).reverse) ++
            programWord k rest).length = k * (2 + batchCount rest)
          rw [List.length_append, List.length_append, List.length_reverse, menu_length,
            List.length_range, ih]
          ring

theorem event_prefix_avoids (k M : Nat) (hk : 2 ≤ k)
    (groups : List (EventGroup (2 * (k + 1) + 1) ForbiddenPair))
    (hfirst : ∀ G ∈ groups, k + 1 ≤ G.first) (hbefore : groups.Pairwise Before)
    (event : Nat × ForbiddenPair) (hevent : event ∈ groups.flatMap EventGroup.events)
    (hrole : roleIndex event.2.1 ≤ k) (n : Nat) (htime : n / k = event.1) :
    (execute updateLabels
      ((programWord k (compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups)).take n)
      id) (some event.2.2) ≠ event.2.1 := by
  obtain ⟨G, hG, hin⟩ := List.mem_flatMap.mp hevent
  obtain ⟨hleft, hright, hlabel⟩ := G.bounds event hin
  have hgroupRole : roleIndex G.label.1 ≤ k := by simpa only [hlabel] using hrole
  obtain ⟨beforeProgram, afterProgram, hprogram, hbatch, havoid⟩ :=
    compiled_repair_avoids k M hk groups hfirst hbefore G hG hgroupRole
  let start := groupStart (k + 1) (groupPhase k) G
  let parking := List.replicate (groupParking (k + 1) (groupPhase k) G / 2)
    (Macro.parking (groupChoice k G))
  have hstart : start ≤ G.first :=
    (repairStart_bounds (k + 1) (groupPhase k G) G.first (by omega)
      (mobilePhase_lt k G.label.1) (hfirst G hG)).2.1
  have hend : G.last + 1 ≤ start + groupParking (k + 1) (groupPhase k) G :=
    (parkingLength_bounds (k + 1) start G.last (by omega)
      (hstart.trans G.first_le_last)).1
  have hbeforeLength : (programWord k beforeProgram).length = k * start := by
    rw [programWord_length, hbatch]
  have hparkingLength : (programWord k parking).length =
      k * groupParking (k + 1) (groupPhase k) G := by
    rw [programWord_length, batchCount_replicate_parking]
    rw [Nat.mul_div_cancel' (groupParking_even (k + 1) (groupPhase k) G)]
  have hnLower : (programWord k beforeProgram).length ≤ n := by
    rw [hbeforeLength, Nat.mul_comm]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp
    rw [htime]
    exact hstart.trans hleft
  have hnUpper : n ≤ (programWord k beforeProgram).length + (programWord k parking).length := by
    have hn : n < (event.1 + 1) * k :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mp (by omega)
    have hb : event.1 + 1 ≤ start + groupParking (k + 1) (groupPhase k) G := by omega
    have hmul := Nat.mul_le_mul_right k hb
    rw [hbeforeLength, hparkingLength]
    nlinarith only [hn, hmul]
  have hwithin : n - (programWord k beforeProgram).length ≤ (programWord k parking).length := by
    omega
  have he := (havoid (n - (programWord k beforeProgram).length) hwithin).2
  have hindex : (programWord k beforeProgram).length +
      (n - (programWord k beforeProgram).length) = n := by omega
  simpa only [hindex, ← hlabel] using he

end CoefficientTwoPrecision.CompiledEventAvoidance

#print axioms CoefficientTwoPrecision.CompiledEventAvoidance.event_prefix_avoids
