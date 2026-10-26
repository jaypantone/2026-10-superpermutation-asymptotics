import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Cutting the event circle and rounding a repair interval

Events are actual residues modulo the number of batches, together with
their forbidden-pair labels. A finite counting argument constructs a cut
outside every closed radius-L event neighborhood. Consequently every
event has a representative strictly between L and M-L after the cut.

For a group of events with first time f and last time e, the repair start
is the last boundary at or before f with a prescribed normal role phase.
The parking length is rounded up to a multiple of 2r. Both choices are
explicit natural-number formulas. Their bounds place the repair, including
its cleanup batch, inside the radius-(2r+1) interval around the group.

This file does not yet group overlapping event neighborhoods or construct
the target word. It supplies actual cut and interval choices for that
construction, rather than assuming their existence.
-/

namespace CoefficientTwoPrecision.RepairIntervals

variable {M : ℕ} {Label : Type*} [DecidableEq Label]

/-- All integer cut positions covered by the closed radius-L neighborhoods
of the event times. The offsets 0,...,2L represent -L,...,L. -/
def forbiddenCuts (events : Finset (ZMod M × Label)) (L : ℕ) : Finset (ZMod M) :=
  (events ×ˢ Finset.range (2 * L + 1)).image
    (fun p => p.1.1 - (L : ZMod M) + (p.2 : ZMod M))

theorem forbiddenCuts_card (events : Finset (ZMod M × Label)) (L : ℕ) :
    (forbiddenCuts events L).card ≤ (2 * L + 1) * events.card := by
  have h := Finset.card_image_le
    (s := events ×ˢ Finset.range (2 * L + 1))
    (f := fun p : (ZMod M × Label) × ℕ => p.1.1 - (L : ZMod M) + (p.2 : ZMod M))
  simpa only [forbiddenCuts, Finset.card_product, Finset.card_range, Nat.mul_comm] using h

theorem mem_forbiddenCuts (events : Finset (ZMod M × Label)) (L : ℕ)
    (event : ZMod M × Label) (hevent : event ∈ events) (d : ℕ) (hd : d ≤ 2 * L) :
    event.1 - (L : ZMod M) + (d : ZMod M) ∈ forbiddenCuts events L := by
  apply Finset.mem_image.mpr
  exact ⟨(event, d), Finset.mem_product.mpr ⟨hevent, Finset.mem_range.mpr (by omega)⟩, rfl⟩

/-- A cut outside all neighborhoods gives ordinary event coordinates with
room on both sides. The proof treats the forward and backward arcs of the
circle separately, so no assumption about a distribution of events enters. -/
theorem event_coordinate_bounds [NeZero M]
    (events : Finset (ZMod M × Label)) (L : ℕ) (cut : ZMod M)
    (hcut : cut ∉ forbiddenCuts events L)
    (event : ZMod M × Label) (hevent : event ∈ events) :
    L < (event.1 - cut).val ∧ (event.1 - cut).val + L < M := by
  let x : ZMod M := event.1 - cut
  have hx : (x.val : ZMod M) = x := ZMod.natCast_zmod_val x
  constructor
  · by_contra h
    have hsmall : x.val ≤ L := by simpa only [x] using Nat.le_of_not_gt h
    have hmem := mem_forbiddenCuts events L event hevent (L - x.val) (by omega)
    have hid : event.1 - (L : ZMod M) + ((L - x.val : ℕ) : ZMod M) = cut := by
      rw [Nat.cast_sub hsmall, hx]
      dsimp [x]
      ring
    exact hcut (hid ▸ hmem)
  · by_contra h
    have hlarge : M ≤ x.val + L := by simpa only [x] using Nat.le_of_not_gt h
    have hxM : x.val < M := x.val_lt
    have hmem := mem_forbiddenCuts events L event hevent (M + L - x.val) (by omega)
    have hid : event.1 - (L : ZMod M) + ((M + L - x.val : ℕ) : ZMod M) = cut := by
      rw [Nat.cast_sub (by omega : x.val ≤ M + L), Nat.cast_add,
        ZMod.natCast_self, hx]
      dsimp [x]
      ring
    exact hcut (hid ▸ hmem)

/-- Construct a cut in a retained normal gap from the exact finite event
set. Labels may repeat, and several labels may initially have the same
time; the counting statement remains valid. -/
theorem exists_safe_cut [NeZero M]
    (events : Finset (ZMod M × Label)) (L : ℕ)
    (hroom : (2 * L + 1) * events.card < M) :
    ∃ cut : ZMod M, cut ∉ forbiddenCuts events L ∧
      ∀ event ∈ events,
        L < (event.1 - cut).val ∧ (event.1 - cut).val + L < M := by
  have hcard : (forbiddenCuts events L).card < (Finset.univ : Finset (ZMod M)).card := by
    simpa only [Finset.card_univ, ZMod.card] using
      lt_of_le_of_lt (forbiddenCuts_card events L) hroom
  obtain ⟨cut, _, hcut⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨cut, hcut, fun event hevent => event_coordinate_bounds events L cut hcut event hevent⟩

/-- The last boundary with the specified residue before the first event. -/
def repairStart (r phase first : ℕ) : ℕ :=
  phase + r * ((first - phase) / r)

/-- The least multiple of 2r whose endpoint is strictly after the last
event. The expression is written using division of natural numbers. -/
def parkingLength (r start last : ℕ) : ℕ :=
  (2 * r) * ((last + 2 * r - start) / (2 * r))

theorem repairStart_bounds (r phase first : ℕ) (hr : 0 < r)
    (hphase : phase < r) (hfirst : r ≤ first) :
    first + 1 ≤ repairStart r phase first + r ∧
      repairStart r phase first ≤ first ∧
      repairStart r phase first % r = phase := by
  have hpf : phase ≤ first := by omega
  have hmod := Nat.mod_lt (first - phase) hr
  have hdiv := Nat.mod_add_div (first - phase) r
  have hsum : (first - phase) % r + repairStart r phase first = first := by
    dsimp [repairStart]
    omega
  refine ⟨by omega, by omega, ?_⟩
  simp only [repairStart, Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
    Nat.mod_eq_of_lt hphase]

theorem parkingLength_bounds (r start last : ℕ) (hr : 0 < r)
    (hstart : start ≤ last) :
    last + 1 ≤ start + parkingLength r start last ∧
      start + parkingLength r start last ≤ last + 2 * r ∧
      2 * r ∣ parkingLength r start last := by
  have h2r : 0 < 2 * r := by omega
  have hmod := Nat.mod_lt (last + 2 * r - start) h2r
  have hdiv := Nat.mod_add_div (last + 2 * r - start) (2 * r)
  have hsum : (last + 2 * r - start) % (2 * r) +
      parkingLength r start last = last + 2 * r - start := by
    exact hdiv
  refine ⟨by omega, by omega, ?_⟩
  exact ⟨(last + 2 * r - start) / (2 * r), rfl⟩

/-- Every event between `first` and `last` occurs during parking. The
cleanup is later, and the entire replacement fits inside the expanded
event interval. In particular, if these event coordinates came from the
safe cut above, batch zero is retained as a normal batch. -/
theorem rounded_repair_interval (r phase first last : ℕ) (hr : 0 < r)
    (hphase : phase < r) (hfirst : 2 * r + 1 < first) (horder : first ≤ last) :
    let start := repairStart r phase first
    let P := parkingLength r start last
    0 < start ∧ start % r = phase ∧ 2 * r ∣ P ∧
      first - (2 * r + 1) ≤ start ∧
      start + P + 1 ≤ last + (2 * r + 1) ∧
      (∀ t, first ≤ t → t ≤ last → start ≤ t ∧ t < start + P) := by
  dsimp only
  obtain ⟨hnear, hstart, hres⟩ := repairStart_bounds r phase first hr hphase (by omega)
  obtain ⟨hafter, hend, hdiv⟩ := parkingLength_bounds r
    (repairStart r phase first) last hr (hstart.trans horder)
  refine ⟨by omega, hres, hdiv, by omega, by omega, ?_⟩
  intro t hft hte
  exact ⟨hstart.trans hft, by omega⟩

end CoefficientTwoPrecision.RepairIntervals

#print axioms CoefficientTwoPrecision.RepairIntervals.exists_safe_cut
#print axioms CoefficientTwoPrecision.RepairIntervals.rounded_repair_interval
