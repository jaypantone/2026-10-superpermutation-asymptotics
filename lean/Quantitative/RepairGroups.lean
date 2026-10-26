import Quantitative.RepairIntervals
import Mathlib.Data.List.Sort

/-!
# Constructing disjoint groups of nearby labelled events

The input is a finite list of event times after cutting the batch circle.
Events whose times differ by at most 2L have the same forbidden-pair label.
Sorting and a left-to-right grouping construct actual event groups. Each
group has one label, and successive groups have a gap greater than 2L.
No partition or interval schedule is assumed as an input.

The group record below includes its actual event list. Its endpoint and
length bounds are proved during construction. These bounds imply that the
rounded repair intervals from `RepairIntervals` are disjoint and use at
most 2L changed batches per input event.
-/

namespace CoefficientTwoPrecision.RepairGroups

open RepairIntervals

variable {Label : Type*}

structure EventGroup (L : ℕ) (Label : Type*) where
  events : List (ℕ × Label)
  first : ℕ
  last : ℕ
  label : Label
  first_mem : (first, label) ∈ events
  last_mem : (last, label) ∈ events
  bounds : ∀ event ∈ events, first ≤ event.1 ∧ event.1 ≤ last ∧ event.2 = label
  span : last + 2 * L ≤ first + 2 * L * events.length

namespace EventGroup

theorem first_le_last {L : ℕ} (G : EventGroup L Label) : G.first ≤ G.last :=
  (G.bounds _ G.first_mem).2.1

def singleton (L : ℕ) (event : ℕ × Label) : EventGroup L Label where
  events := [event]
  first := event.1
  last := event.1
  label := event.2
  first_mem := by simp
  last_mem := by simp
  bounds := by
    intro e he
    have heq : e = event := List.mem_singleton.mp he
    subst e
    exact ⟨le_rfl, le_rfl, rfl⟩
  span := by simp

/-- Add the immediately preceding nearby event to the first group. -/
def prepend {L : ℕ} (event : ℕ × Label) (G : EventGroup L Label)
    (hearly : event.1 ≤ G.first) (hclose : G.first ≤ event.1 + 2 * L)
    (hlabel : event.2 = G.label) : EventGroup L Label where
  events := event :: G.events
  first := event.1
  last := G.last
  label := event.2
  first_mem := by simp
  last_mem := by simpa only [hlabel] using List.mem_cons_of_mem event G.last_mem
  bounds := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨le_rfl, hearly.trans G.first_le_last, rfl⟩
    · obtain ⟨hfirst, hlast, hlab⟩ := G.bounds e he
      exact ⟨hearly.trans hfirst, hlast, hlab.trans hlabel.symm⟩
  span := by
    have hspan := G.span
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

end EventGroup

def Before {L : ℕ} (G H : EventGroup L Label) : Prop := G.last + 2 * L < H.first

/-- Consecutive gaps at most 2L are merged. The proof also gives exact
coverage of the input list, so it neither drops nor duplicates an event. -/
theorem group_ordered_events (L : ℕ) (events : List (ℕ × Label))
    (hordered : events.Pairwise (fun x y => x.1 ≤ y.1))
    (hlabels : ∀ x ∈ events, ∀ y ∈ events,
      x.1 ≤ y.1 → y.1 ≤ x.1 + 2 * L → x.2 = y.2) :
    ∃ groups : List (EventGroup L Label),
      groups.flatMap EventGroup.events = events ∧ groups.Pairwise Before := by
  induction events with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons event events ih =>
    obtain ⟨hearly, htail⟩ := List.pairwise_cons.mp hordered
    have hlabelsTail : ∀ x ∈ events, ∀ y ∈ events,
        x.1 ≤ y.1 → y.1 ≤ x.1 + 2 * L → x.2 = y.2 := by
      intro x hx y hy
      exact hlabels x (List.mem_cons_of_mem event hx) y (List.mem_cons_of_mem event hy)
    obtain ⟨groups, hflat, hpairs⟩ := ih htail hlabelsTail
    cases groups with
    | nil =>
      have hempty : events = [] := hflat.symm
      subst events
      exact ⟨[EventGroup.singleton L event], rfl, by simp⟩
    | cons G groups =>
      have hmembers : ∀ x ∈ G.events, x ∈ events := by
        intro x hx
        rw [← hflat]
        exact List.mem_append_left _ hx
      have hGfirst := hmembers (G.first, G.label) G.first_mem
      have hfirst : event.1 ≤ G.first := hearly _ hGfirst
      obtain ⟨hGbefore, hrest⟩ := List.pairwise_cons.mp hpairs
      by_cases hclose : G.first ≤ event.1 + 2 * L
      · have hlabel : event.2 = G.label :=
          hlabels event (by simp) (G.first, G.label)
            (List.mem_cons_of_mem event hGfirst) hfirst hclose
        refine ⟨EventGroup.prepend event G hfirst hclose hlabel :: groups, ?_, ?_⟩
        · change event :: (G.events ++ groups.flatMap EventGroup.events) = event :: events
          exact congrArg (List.cons event) hflat
        · apply List.pairwise_cons.mpr
          exact ⟨fun H hH => hGbefore H hH, hrest⟩
      · have hgap : event.1 + 2 * L < G.first := Nat.lt_of_not_ge hclose
        refine ⟨EventGroup.singleton L event :: G :: groups, ?_, ?_⟩
        · change event :: (G.events ++ groups.flatMap EventGroup.events) = event :: events
          exact congrArg (List.cons event) hflat
        · apply List.pairwise_cons.mpr
          refine ⟨?_, hpairs⟩
          intro H hH
          rcases List.mem_cons.mp hH with rfl | hH
          · exact hgap
          · have hnext := hGbefore H hH
            have horder := G.first_le_last
            change event.1 + 2 * L < H.first
            dsimp only [Before] at hnext
            omega

/-- Every finite event list can be grouped; the output is a permutation
of the input when flattened. Sorting uses only the time coordinates. -/
theorem group_events (L : ℕ) (events : List (ℕ × Label))
    (hlabels : ∀ x ∈ events, ∀ y ∈ events,
      x.1 ≤ y.1 → y.1 ≤ x.1 + 2 * L → x.2 = y.2) :
    ∃ groups : List (EventGroup L Label),
      (groups.flatMap EventGroup.events).Perm events ∧ groups.Pairwise Before := by
  let compare : (ℕ × Label) → (ℕ × Label) → Bool := fun x y => decide (x.1 ≤ y.1)
  let ordered := events.mergeSort compare
  have hperm : ordered.Perm events := List.mergeSort_perm events compare
  have hsort : ordered.Pairwise (fun x y => x.1 ≤ y.1) := by
    simpa only [ordered, compare, decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := compare)
        (fun x y z hxy hyz => by
          simpa only [compare, decide_eq_true_eq] using
            (Nat.le_trans (by simpa only [compare, decide_eq_true_eq] using hxy)
              (by simpa only [compare, decide_eq_true_eq] using hyz)))
        (fun x y => by simpa [compare] using Nat.le_total x.1 y.1) events)
  have hlabelsOrdered : ∀ x ∈ ordered, ∀ y ∈ ordered,
      x.1 ≤ y.1 → y.1 ≤ x.1 + 2 * L → x.2 = y.2 := by
    intro x hx y hy
    exact hlabels x (hperm.mem_iff.mp hx) y (hperm.mem_iff.mp hy)
  obtain ⟨groups, hflat, hbefore⟩ := group_ordered_events L ordered hsort hlabelsOrdered
  exact ⟨groups, hflat.symm ▸ hperm, hbefore⟩

/-- Rounded repairs of different ordered groups cannot overlap. -/
theorem rounded_intervals_disjoint (r phaseG phaseH : ℕ)
    (G H : EventGroup (2 * r + 1) Label) (hr : 0 < r)
    (hphaseG : phaseG < r) (hphaseH : phaseH < r)
    (hfirstG : r ≤ G.first) (hfirstH : r ≤ H.first) (hbefore : Before G H) :
    repairStart r phaseG G.first +
        parkingLength r (repairStart r phaseG G.first) G.last + 1 ≤
      repairStart r phaseH H.first := by
  obtain ⟨_, hstartG, _⟩ := repairStart_bounds r phaseG G.first hr hphaseG hfirstG
  obtain ⟨hnearH, _, _⟩ := repairStart_bounds r phaseH H.first hr hphaseH hfirstH
  obtain ⟨_, hendG, _⟩ := parkingLength_bounds r (repairStart r phaseG G.first) G.last hr
    (hstartG.trans G.first_le_last)
  dsimp only [Before] at hbefore
  omega

/-- The number of replaced batches, including cleanup, is bounded by the
number of events in the group times 2L. -/
theorem changed_batches_le (r phase : ℕ) (G : EventGroup (2 * r + 1) Label)
    (hr : 0 < r) (hphase : phase < r) (hfirst : r ≤ G.first) :
    parkingLength r (repairStart r phase G.first) G.last + 1 ≤
      2 * (2 * r + 1) * G.events.length := by
  obtain ⟨hnear, hstart, _⟩ := repairStart_bounds r phase G.first hr hphase hfirst
  obtain ⟨_, hend, _⟩ := parkingLength_bounds r (repairStart r phase G.first) G.last hr
    (hstart.trans G.first_le_last)
  have hspan := G.span
  omega

end CoefficientTwoPrecision.RepairGroups

#print axioms CoefficientTwoPrecision.RepairGroups.group_events
#print axioms CoefficientTwoPrecision.RepairGroups.rounded_intervals_disjoint
#print axioms CoefficientTwoPrecision.RepairGroups.changed_batches_le
