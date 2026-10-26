import Quantitative.RepairProgram

/-!
# An actual repair program from separated cyclic events

Two events are close on the batch circle if one time is the other time
plus an integer displacement of absolute value at most 2L. The separation
hypothesis says that close events have the same forbidden-pair label.

Starting from a finite set of cyclic events, this file chooses a safe cut,
lifts the events to ordinary natural-number times, constructs their groups,
and splices their rounded repairs into an actual macro list. The phase and
parking-menu choice for each forbidden pair are parameters; the local role
lemmas supply these choices. No event grouping, interval partition, or
macro program is supplied as an existence hypothesis.
-/

namespace CoefficientTwoPrecision.CyclicRepairSchedule

open RepairIntervals RepairGroups RepairProgram MacroCatalogue

variable {M : ℕ} {Label : Type*} [DecidableEq Label]

/-- Circular separation expressed without selecting an origin on the
circle. A negative displacement covers the reverse direction as well. -/
def Separated (events : Finset (ZMod M × Label)) (L : ℕ) : Prop :=
  ∀ x ∈ events, ∀ y ∈ events, ∀ d : ℤ,
    |d| ≤ (2 * L : ℕ) → y.1 = x.1 + (d : ZMod M) → x.2 = y.2

def liftEvent (cut : ZMod M) (event : ZMod M × Label) : ℕ × Label :=
  ((event.1 - cut).val, event.2)

noncomputable def liftedEvents (events : Finset (ZMod M × Label)) (cut : ZMod M) :
    List (ℕ × Label) := events.toList.map (liftEvent cut)

theorem lifted_length (events : Finset (ZMod M × Label)) (cut : ZMod M) :
    (liftedEvents events cut).length = events.card := by
  simp only [liftedEvents, List.length_map, Finset.length_toList]

/-- A close pair after cutting is also a close pair on the original
circle. The proof keeps the signed displacement, including possible wrap. -/
theorem lifted_labels [NeZero M]
    (events : Finset (ZMod M × Label)) (L : ℕ) (cut : ZMod M)
    (hseparated : Separated events L) :
    ∀ x ∈ liftedEvents events cut, ∀ y ∈ liftedEvents events cut,
      x.1 ≤ y.1 → y.1 ≤ x.1 + 2 * L → x.2 = y.2 := by
  intro x hx y hy horder hclose
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
  obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hy
  have hXe : X ∈ events := Finset.mem_toList.mp hX
  have hYe : Y ∈ events := Finset.mem_toList.mp hY
  let d : ℤ := ((Y.1 - cut).val : ℤ) - ((X.1 - cut).val : ℤ)
  have hd0 : 0 ≤ d := by dsimp [d, liftEvent] at *; omega
  have hd : |d| ≤ (2 * L : ℕ) := by
    rw [abs_of_nonneg hd0]
    dsimp [d, liftEvent] at *
    omega
  have heq : Y.1 = X.1 + (d : ZMod M) := by
    simp only [d, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    ring
  exact hseparated X hXe Y hYe d hd heq

/-- Construct the cut and all event groups from the finite cyclic event
set. Every group remains away from both ends of the cut-open circle. -/
theorem exists_grouped_circle [NeZero M]
    (events : Finset (ZMod M × Label)) (L : ℕ)
    (hroom : (2 * L + 1) * events.card < M)
    (hseparated : Separated events L) :
    ∃ cut : ZMod M, ∃ groups : List (EventGroup L Label),
      (groups.flatMap EventGroup.events).Perm (liftedEvents events cut) ∧
      groups.Pairwise Before ∧
      ∀ G ∈ groups, L < G.first ∧ G.last + L < M := by
  obtain ⟨cut, _, hcoordinates⟩ := exists_safe_cut events L hroom
  obtain ⟨groups, hperm, hbefore⟩ := group_events L (liftedEvents events cut)
    (lifted_labels events L cut hseparated)
  refine ⟨cut, groups, hperm, hbefore, ?_⟩
  intro G hG
  have hcoord : ∀ t label, (t, label) ∈ G.events → L < t ∧ t + L < M := by
    intro t label ht
    have hflat : (t, label) ∈ groups.flatMap EventGroup.events :=
      List.mem_flatMap.mpr ⟨G, hG, ht⟩
    have hlift := hperm.mem_iff.mp hflat
    obtain ⟨event, hevent, heq⟩ := List.mem_map.mp hlift
    have hb := hcoordinates event (Finset.mem_toList.mp hevent)
    have htEq : (event.1 - cut).val = t := congrArg Prod.fst heq
    simpa only [htEq] using hb
  exact ⟨(hcoord G.first G.label G.first_mem).1,
    (hcoord G.last G.label G.last_mem).2⟩

def changedBatches (r : ℕ) (phase : Label → ℕ) :
    List (EventGroup (2 * r + 1) Label) → ℕ
  | [] => 0
  | G :: groups => groupParking r (fun H => phase H.label) G + 1 + changedBatches r phase groups

theorem changedBatches_bound (r : ℕ) (phase : Label → ℕ)
    (groups : List (EventGroup (2 * r + 1) Label)) (hr : 0 < r)
    (hphase : ∀ label, phase label < r)
    (hfirst : ∀ G ∈ groups, r ≤ G.first) :
    changedBatches r phase groups ≤
      2 * (2 * r + 1) * (groups.flatMap EventGroup.events).length := by
  induction groups with
  | nil => simp only [changedBatches, List.flatMap_nil, List.length_nil, Nat.mul_zero, le_refl]
  | cons G groups ih =>
    have hG := changed_batches_le r (phase G.label) G hr (hphase G.label) (hfirst G (by simp))
    have htail := ih (fun H hH => hfirst H (List.mem_cons_of_mem G hH))
    simpa only [changedBatches, List.flatMap_cons, List.length_append, Nat.mul_add,
      groupParking, groupStart] using Nat.add_le_add hG htail

/-- A complete finite schedule, with an actual macro list specified by
the compiler. Its use still requires the local role lemma to choose the
phase and parking order for each forbidden pair. -/
theorem exists_repair_program [NeZero M]
    (events : Finset (ZMod M × Label)) (r : ℕ) (hr : 0 < r)
    (hroom : (2 * (2 * r + 1) + 1) * events.card < M)
    (hseparated : Separated events (2 * r + 1))
    (phase : Label → ℕ) (hphase : ∀ label, phase label < r)
    (choice : Label → Bool) :
    ∃ cut : ZMod M, ∃ groups : List (EventGroup (2 * r + 1) Label),
      (groups.flatMap EventGroup.events).Perm (liftedEvents events cut) ∧
      groups.Pairwise Before ∧
      (∀ G ∈ groups, 2 * r + 1 < G.first ∧ G.last + (2 * r + 1) < M) ∧
      batchCount (compile r (fun G => phase G.label) (fun G => choice G.label) M 0 groups) = M ∧
      normalCount (compile r (fun G => phase G.label) (fun G => choice G.label) M 0 groups) % r = M % r ∧
      changedBatches r phase groups ≤ 2 * (2 * r + 1) * events.card ∧
      ∃ beforeProgram : List Macro,
        compile r (fun G => phase G.label) (fun G => choice G.label) M 0 groups = beforeProgram ++ [.normal] := by
  obtain ⟨cut, groups, hperm, hbefore, hbounds⟩ :=
    exists_grouped_circle events (2 * r + 1) hroom hseparated
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hroom
  have hfirst : ∀ G ∈ groups, r ≤ G.first := by
    intro G hG
    have h := (hbounds G hG).1
    omega
  have hfit : ∀ G ∈ groups, groupEnd r (fun H => phase H.label) G < M := by
    intro G hG
    obtain ⟨_, _, _, _, hend, _⟩ := rounded_repair_interval r (phase G.label) G.first G.last
      hr (hphase G.label) (hbounds G hG).1 G.first_le_last
    exact lt_of_le_of_lt hend (hbounds G hG).2
  obtain ⟨hbatch, hnormal, hlast⟩ := constructed_program_counts r M
    (fun G => phase G.label) (fun G => choice G.label) groups hr hM
    (fun G _ => hphase G.label) hfirst hfit hbefore
  have hchanged := changedBatches_bound r phase groups hr hphase hfirst
  rw [hperm.length_eq, lifted_length] at hchanged
  exact ⟨cut, groups, hperm, hbefore, hbounds, hbatch, hnormal, hchanged, hlast⟩

end CoefficientTwoPrecision.CyclicRepairSchedule

#print axioms CoefficientTwoPrecision.CyclicRepairSchedule.exists_grouped_circle
#print axioms CoefficientTwoPrecision.CyclicRepairSchedule.exists_repair_program
