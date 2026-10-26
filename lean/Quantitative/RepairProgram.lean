import Quantitative.RepairGroups
import Quantitative.MacroCatalogue

/-!
# Splicing the constructed repair intervals into an actual macro program

For each event group, insert normal batches up to its rounded start,
then the required number of parking pairs, then one normal cleanup batch.
The result is an actual list of the normal and parking constructors used
by `MacroCatalogue`. The disjointness already proved for event groups
ensures that no natural-number subtraction in this construction truncates
a requested prefix.

The batch count is exactly the prescribed circumference. Replacing a
multiple of r normal batches by parking pairs preserves the number of
normal batches modulo r. A final normal batch remains when all repair
intervals end strictly before the cut.
-/

namespace CoefficientTwoPrecision.RepairProgram

open RepairIntervals RepairGroups MacroCatalogue

variable {Label : Type*}

def groupStart (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ)
    (G : EventGroup (2 * r + 1) Label) : ℕ := repairStart r (phase G) G.first

def groupParking (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ)
    (G : EventGroup (2 * r + 1) Label) : ℕ :=
  parkingLength r (groupStart r phase G) G.last

def groupEnd (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ)
    (G : EventGroup (2 * r + 1) Label) : ℕ :=
  groupStart r phase G + groupParking r phase G + 1

/-- The actual macro list. A parking constructor represents two batches. -/
def compile (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ)
    (choice : EventGroup (2 * r + 1) Label → Bool) (stop : ℕ) :
    ℕ → List (EventGroup (2 * r + 1) Label) → List Macro
  | cursor, [] => List.replicate (stop - cursor) .normal
  | cursor, G :: groups =>
      List.replicate (groupStart r phase G - cursor) .normal ++
      List.replicate (groupParking r phase G / 2) (.parking (choice G)) ++
      .normal :: compile r phase choice stop (groupEnd r phase G) groups

def removed (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ) :
    List (EventGroup (2 * r + 1) Label) → ℕ
  | [] => 0
  | G :: groups => groupParking r phase G + removed r phase groups

theorem batchCount_append (left right : List Macro) :
    batchCount (left ++ right) = batchCount left + batchCount right := by
  induction left with
  | nil => simp only [List.nil_append, batchCount, Nat.zero_add]
  | cons instruction left ih =>
    cases instruction <;> simp only [List.cons_append, batchCount, ih, Nat.add_assoc]

theorem normalCount_append (left right : List Macro) :
    normalCount (left ++ right) = normalCount left + normalCount right := by
  induction left with
  | nil => simp only [List.nil_append, normalCount, Nat.zero_add]
  | cons instruction left ih =>
    cases instruction <;> simp only [List.cons_append, normalCount, ih] <;> omega

theorem batchCount_replicate_normal (n : ℕ) :
    batchCount (List.replicate n .normal) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, batchCount, ih]; omega

theorem batchCount_replicate_parking (n : ℕ) (choice : Bool) :
    batchCount (List.replicate n (.parking choice)) = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, batchCount, ih]; omega

theorem normalCount_replicate_normal (n : ℕ) :
    normalCount (List.replicate n .normal) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, normalCount, ih]

theorem normalCount_replicate_parking (n : ℕ) (choice : Bool) :
    normalCount (List.replicate n (.parking choice)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, normalCount, ih]

theorem groupParking_even (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ)
    (G : EventGroup (2 * r + 1) Label) : 2 ∣ groupParking r phase G := by
  refine ⟨r * ((G.last + 2 * r - groupStart r phase G) / (2 * r)), ?_⟩
  unfold groupParking parkingLength
  ring

theorem groupParking_dvd (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ)
    (G : EventGroup (2 * r + 1) Label) : r ∣ groupParking r phase G := by
  refine ⟨2 * ((G.last + 2 * r - groupStart r phase G) / (2 * r)), ?_⟩
  unfold groupParking parkingLength
  ring

theorem removed_dvd (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ)
    (groups : List (EventGroup (2 * r + 1) Label)) : r ∣ removed r phase groups := by
  induction groups with
  | nil => exact dvd_zero r
  | cons G groups ih => exact dvd_add (groupParking_dvd r phase G) ih

theorem groupEnd_le_next (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ)
    (G H : EventGroup (2 * r + 1) Label) (hr : 0 < r)
    (hpG : phase G < r) (hpH : phase H < r)
    (hfG : r ≤ G.first) (hfH : r ≤ H.first) (hbefore : Before G H) :
    groupEnd r phase G ≤ groupStart r phase H :=
  rounded_intervals_disjoint r (phase G) (phase H) G H hr hpG hpH hfG hfH hbefore

/-- Exact batch and normal-batch counts of the compiled program. -/
theorem compile_counts (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ)
    (choice : EventGroup (2 * r + 1) Label → Bool) (stop cursor : ℕ)
    (groups : List (EventGroup (2 * r + 1) Label)) (hr : 0 < r)
    (hphases : ∀ G ∈ groups, phase G < r)
    (hfirst : ∀ G ∈ groups, r ≤ G.first)
    (hcursor : ∀ G ∈ groups, cursor ≤ groupStart r phase G)
    (hfit : ∀ G ∈ groups, groupEnd r phase G ≤ stop)
    (hbefore : groups.Pairwise Before) :
    batchCount (compile r phase choice stop cursor groups) = stop - cursor ∧
      normalCount (compile r phase choice stop cursor groups) + removed r phase groups =
        stop - cursor := by
  induction groups generalizing cursor with
  | nil => simp only [compile, removed, batchCount_replicate_normal,
      normalCount_replicate_normal, Nat.add_zero, and_self]
  | cons G groups ih =>
    have hpG := hphases G (by simp)
    have hfG := hfirst G (by simp)
    have hcG := hcursor G (by simp)
    have heG := hfit G (by simp)
    obtain ⟨hGbefore, htailBefore⟩ := List.pairwise_cons.mp hbefore
    have hcTail : ∀ H ∈ groups, groupEnd r phase G ≤ groupStart r phase H := by
      intro H hH
      exact groupEnd_le_next r phase G H hr hpG (hphases H (by simp [hH]))
        hfG (hfirst H (by simp [hH])) (hGbefore H hH)
    obtain ⟨hbatch, hnormal⟩ := ih (groupEnd r phase G)
      (fun H hH => hphases H (List.mem_cons_of_mem G hH))
      (fun H hH => hfirst H (List.mem_cons_of_mem G hH)) hcTail
      (fun H hH => hfit H (List.mem_cons_of_mem G hH)) htailBefore
    have hhalf : 2 * (groupParking r phase G / 2) = groupParking r phase G :=
      Nat.mul_div_cancel' (groupParking_even r phase G)
    have hend : groupEnd r phase G = groupStart r phase G + groupParking r phase G + 1 := rfl
    constructor
    · simp only [compile, batchCount_append, batchCount_replicate_normal,
        batchCount_replicate_parking, batchCount, hbatch, hhalf]
      omega
    · simp only [compile, normalCount_append, normalCount_replicate_normal,
        normalCount_replicate_parking, normalCount, removed, Nat.zero_add]
      omega

/-- The normal suffix is nonempty if every repair ends strictly before
the cut. This constructs an actual final normal macro. -/
theorem compile_ends_normal (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ)
    (choice : EventGroup (2 * r + 1) Label → Bool) (stop cursor : ℕ)
    (groups : List (EventGroup (2 * r + 1) Label)) (hcursor : cursor < stop)
    (hfit : ∀ G ∈ groups, groupEnd r phase G < stop) :
    ∃ beforeProgram : List Macro, compile r phase choice stop cursor groups = beforeProgram ++ [.normal] := by
  induction groups generalizing cursor with
  | nil =>
    refine ⟨List.replicate (stop - cursor - 1) .normal, ?_⟩
    have hlength : stop - cursor = (stop - cursor - 1) + 1 := by omega
    change List.replicate (stop - cursor) Macro.normal = _
    conv_lhs => rw [hlength, List.replicate_add]
    rfl
  | cons G groups ih =>
    obtain ⟨beforeProgram, hprefix⟩ := ih (groupEnd r phase G) (hfit G (by simp))
      (fun H hH => hfit H (List.mem_cons_of_mem G hH))
    refine ⟨List.replicate (groupStart r phase G - cursor) .normal ++
      List.replicate (groupParking r phase G / 2) (.parking (choice G)) ++
        .normal :: beforeProgram, ?_⟩
    simp only [compile, hprefix, List.append_assoc, List.cons_append]

/-- The constructed global program has the original circumference and
the correct normal role count modulo r, and retains a final normal batch. -/
theorem constructed_program_counts (r M : ℕ)
    (phase : EventGroup (2 * r + 1) Label → ℕ)
    (choice : EventGroup (2 * r + 1) Label → Bool)
    (groups : List (EventGroup (2 * r + 1) Label)) (hr : 0 < r) (hM : 0 < M)
    (hphases : ∀ G ∈ groups, phase G < r)
    (hfirst : ∀ G ∈ groups, r ≤ G.first)
    (hfit : ∀ G ∈ groups, groupEnd r phase G < M)
    (hbefore : groups.Pairwise Before) :
    batchCount (compile r phase choice M 0 groups) = M ∧
      normalCount (compile r phase choice M 0 groups) % r = M % r ∧
      ∃ beforeProgram : List Macro, compile r phase choice M 0 groups = beforeProgram ++ [.normal] := by
  obtain ⟨hbatch, hnormal⟩ := compile_counts r phase choice M 0 groups hr hphases hfirst
    (fun _ _ => Nat.zero_le _) (fun G hG => (hfit G hG).le) hbefore
  simp only [Nat.sub_zero] at hbatch hnormal
  have hmod := congrArg (fun x : ℕ => x % r) hnormal
  have hremoved := Nat.mod_eq_zero_of_dvd (removed_dvd r phase groups)
  simp only [Nat.add_mod, hremoved, Nat.add_zero, Nat.mod_mod] at hmod
  exact ⟨hbatch, hmod, compile_ends_normal r phase choice M 0 groups hM hfit⟩

end CoefficientTwoPrecision.RepairProgram

#print axioms CoefficientTwoPrecision.RepairProgram.compile_counts
#print axioms CoefficientTwoPrecision.RepairProgram.constructed_program_counts
