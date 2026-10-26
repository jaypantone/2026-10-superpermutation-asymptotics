import Quantitative.ModularRoots
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite counting by fibres

The estimates count all choices of the remaining coordinates. They do not
assume that an independently selected packing is uniformly distributed.
-/

namespace CoefficientTwoPrecision.FiniteFibers

open Finset

/-- Bound a finite set by the number of possible images times a uniform
upper bound for each fibre. -/
theorem card_le_of_fiber_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → β) (D : Nat)
    (hmap : Set.MapsTo f S T)
    (hfiber : ∀ b ∈ T, (S.filter (fun a => f a = b)).card ≤ D) :
    S.card ≤ T.card * D := by
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    ∑ b ∈ T, (S.filter (fun a => f a = b)).card ≤ ∑ _b ∈ T, D :=
      Finset.sum_le_sum hfiber
    _ = T.card * D := by simp

theorem fin_root_count (M : Nat) (hM : 0 < M) (a b : Int) (ha : a ≠ 0) :
    (Finset.univ.filter (fun x : Fin M => Int.ModEq (M : Int) (a * x.val) b)).card ≤
      a.natAbs := by
  let S := Finset.univ.filter (fun x : Fin M => Int.ModEq (M : Int) (a * x.val) b)
  let T := (Finset.range M).filter (fun x : Nat => Int.ModEq (M : Int) (a * x) b)
  have hmap : Set.MapsTo (fun x : Fin M => x.val) (S : Set (Fin M)) (T : Set Nat) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.isLt, (Finset.mem_filter.mp hx).2⟩
  have hinj : (S : Set (Fin M)).InjOn Fin.val := by
    intro x _ y _ hxy
    exact Fin.ext hxy
  exact (Finset.card_le_card_of_injOn Fin.val hmap hinj).trans
    (ModularRoots.integer_root_count M hM a b ha)

/-- One nonzero coefficient controls a congruence, even when its right
side is an arbitrary function of all the other coordinates. -/
theorem dependent_root_count {β : Type*} [Fintype β] [DecidableEq β]
    (M : Nat) (hM : 0 < M) (a : Int) (ha : a ≠ 0) (rhs : β → Int) :
    (Finset.univ.filter (fun p : β × Fin M =>
      Int.ModEq (M : Int) (a * p.2.val) (rhs p.1))).card ≤
      Fintype.card β * a.natAbs := by
  let S := Finset.univ.filter (fun p : β × Fin M =>
    Int.ModEq (M : Int) (a * p.2.val) (rhs p.1))
  have hfiber (b : β) : (S.filter (fun p => p.1 = b)).card ≤ a.natAbs := by
    let T := Finset.univ.filter (fun x : Fin M => Int.ModEq (M : Int) (a * x.val) (rhs b))
    have hmap : Set.MapsTo (fun p : β × Fin M => p.2)
        ((S.filter (fun p => p.1 = b)) : Set (β × Fin M)) (T : Set (Fin M)) := by
      intro p hp
      obtain ⟨hp, hfirst⟩ := Finset.mem_filter.mp hp
      have heq := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hfirst] using heq⟩
    have hinj : ((S.filter (fun p => p.1 = b)) : Set (β × Fin M)).InjOn Prod.snd := by
      intro p hp q hq hsnd
      apply Prod.ext
      · exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
      · exact hsnd
    exact (Finset.card_le_card_of_injOn Prod.snd hmap hinj).trans
      (fin_root_count M hM a (rhs b) ha)
  simpa only [Finset.card_univ] using
    card_le_of_fiber_bound S Finset.univ Prod.fst a.natAbs
      (fun _ _ => Finset.mem_univ _) (fun b _ => hfiber b)

theorem vector_root_count (M d : Nat) (hM : 0 < M) (a : Int) (ha : a ≠ 0)
    (rhs : (Fin d → Fin M) → Int) :
    (Finset.univ.filter (fun p : (Fin d → Fin M) × Fin M =>
      Int.ModEq (M : Int) (a * p.2.val) (rhs p.1))).card ≤
      M ^ d * a.natAbs := by
  simpa using dependent_root_count M hM a ha rhs

/-- Count a union of bad events by summing their counts. Each event is
counted separately, including events with identical solution sets. -/
theorem bad_union_count {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (bad : ι → Finset α) (D : Nat)
    (hbad : ∀ i ∈ I, (bad i).card ≤ D) :
    (I.biUnion bad).card ≤ I.card * D := by
  calc
    (I.biUnion bad).card ≤ ∑ i ∈ I, (bad i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, D := Finset.sum_le_sum hbad
    _ = I.card * D := by simp

end CoefficientTwoPrecision.FiniteFibers

#print axioms CoefficientTwoPrecision.FiniteFibers.vector_root_count
#print axioms CoefficientTwoPrecision.FiniteFibers.bad_union_count
