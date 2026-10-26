import Quantitative.LinearCount
import Quantitative.RobustMatching

/-!
# An actual finite set of robust ordered modular frames

The finite construction excludes every pair of indexed differences that
lies within four residues. Every excluded congruence has a nonzero
coefficient of absolute value at most two. Counting these congruences
gives the explicit deficit 18*(d+2)^4*M^(d-1).

This file counts ordered coordinate vectors. Passing to sorted frames
and constructing the labelled disjoint envelopes are separate steps.
-/

namespace CoefficientTwoPrecision.FrameCounting

open FrameAlgebra RobustMatching

abbrev Index (d : Nat) := DifferenceIndex (Point d)

def coefficient {d : Nat} : Index d → Fin d → Int
  | none, _ => 0
  | some p, j => coordinate p.val.1 j - coordinate p.val.2 j

theorem coefficient_injective {d : Nat} (hd : 3 ≤ d) :
    Function.Injective (@coefficient d) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have h := ordered_difference_injective hd b.val.1 b.val.2 b.val.1 b.val.1 b.property
        (fun j => by have hj := congrFun hab j; simpa [coefficient] using hj.symm)
      exact False.elim (b.property h.2.symm)
  | some a =>
    cases b with
    | none =>
      have h := ordered_difference_injective hd a.val.1 a.val.2 a.val.1 a.val.1 a.property
        (fun j => by have hj := congrFun hab j; simpa [coefficient] using hj)
      exact False.elim (a.property h.2.symm)
    | some b =>
      have hp := ordered_difference_injective hd a.val.1 a.val.2 b.val.1 b.val.2 a.property
        (fun j => congrFun hab j)
      exact congrArg some (Subtype.ext (Prod.ext hp.1 hp.2))

theorem coordinate_bounds {d : Nat} (p : Point d) (j : Fin d) :
    0 ≤ coordinate p j ∧ coordinate p j ≤ 1 := by
  cases p with
  | none => simp [coordinate]
  | some p =>
    cases p with
    | none => simp [coordinate]
    | some i => by_cases hi : i = j <;> simp [coordinate, hi]

theorem coefficient_bounds {d : Nat} (a : Index d) (j : Fin d) :
    -1 ≤ coefficient a j ∧ coefficient a j ≤ 1 := by
  cases a with
  | none => simp [coefficient]
  | some a =>
    have h1 := coordinate_bounds a.val.1 j
    have h2 := coordinate_bounds a.val.2 j
    simp only [coefficient]
    omega

theorem coefficient_difference_bound {d : Nat} (a b : Index d) (j : Fin d) :
    (coefficient a j - coefficient b j).natAbs ≤ 2 := by
  have ha := coefficient_bounds a j
  have hb := coefficient_bounds b j
  omega

def cuts {M d : Nat} (x : Fin d → Fin M) (p : Point d) : ZMod M :=
  ((∑ j, coordinate p j * (x j).val : Int) : ZMod M)

theorem difference_eq_sum {M d : Nat} (x : Fin d → Fin M) (a : Index d) :
    difference (cuts x) a = ((∑ j, coefficient a j * (x j).val : Int) : ZMod M) := by
  cases a with
  | none => simp [difference, coefficient]
  | some a => simp [difference, coefficient, cuts, sub_mul, Finset.sum_sub_distrib]

def badEvent (M d : Nat) (event : Index d × Index d × Fin 9) :
    Finset (Fin d → Fin M) :=
  if event.1 = event.2.1 then ∅ else
    Finset.univ.filter (fun x => Int.ModEq (M : Int)
      (∑ j, (coefficient event.1 j - coefficient event.2.1 j) * (x j).val)
      ((event.2.2.val : Int) - 4))

theorem badEvent_card (M d : Nat) (hM : 0 < M) (hd : 3 ≤ d)
    (event : Index d × Index d × Fin 9) :
    (badEvent M d event).card ≤ 2 * M ^ (d - 1) := by
  by_cases heq : event.1 = event.2.1
  · simp [badEvent, heq]
  · have hne : coefficient event.1 ≠ coefficient event.2.1 :=
      fun h => heq (coefficient_injective hd h)
    obtain ⟨j, hj⟩ : ∃ j, coefficient event.1 j ≠ coefficient event.2.1 j := by
      by_contra hn
      apply hne
      funext j
      exact not_not.mp (fun h => hn ⟨j, h⟩)
    have hbound := LinearCount.linear_root_count M d hM
      (fun j => coefficient event.1 j - coefficient event.2.1 j)
      ((event.2.2.val : Int) - 4) j (sub_ne_zero.mpr hj)
    rw [badEvent, if_neg heq]
    exact hbound.trans (by
      have hmul := Nat.mul_le_mul_left (M ^ (d - 1))
        (coefficient_difference_bound event.1 event.2.1 j)
      simpa only [Nat.mul_comm] using hmul)

theorem index_card_le (d : Nat) : Fintype.card (Index d) ≤ (d + 2) ^ 2 := by
  let f : Index d → Point d × Point d
    | none => (none, none)
    | some a => a.val
  have hinj : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        have h : b.val.1 = b.val.2 := by
          have h1 := congrArg Prod.fst hab
          have h2 := congrArg Prod.snd hab
          exact h1.symm.trans h2
        exact False.elim (b.property h)
    | some a =>
      cases b with
      | none =>
        have h : a.val.1 = a.val.2 := by
          have h1 := congrArg Prod.fst hab
          have h2 := congrArg Prod.snd hab
          exact h1.trans h2.symm
        exact False.elim (a.property h)
      | some b => exact congrArg some (Subtype.ext hab)
  have h := Fintype.card_le_of_injective f hinj
  simpa [Point, pow_two, Nat.add_assoc] using h

def badFrames (M d : Nat) : Finset (Fin d → Fin M) :=
  Finset.univ.biUnion (badEvent M d)

def goodFrames (M d : Nat) : Finset (Fin d → Fin M) :=
  Finset.univ \ badFrames M d

/-- Every retained vector satisfies the same indexed robustness condition
used in the literal matching proof. -/
theorem goodFrames_robust {M d : Nat} {x : Fin d → Fin M}
    (hx : x ∈ goodFrames M d) : Robust (cuts x) := by
  intro a b e hlo hhi heq
  by_contra hab
  let v : Fin 9 := ⟨(e + 4).toNat, by omega⟩
  have hv : (v.val : Int) - 4 = e := by
    dsimp [v]
    omega
  have hdiff :
      ((∑ j, (coefficient a j - coefficient b j) * (x j).val : Int) : ZMod M) =
        (e : ZMod M) := by
    rw [difference_eq_sum, difference_eq_sum] at heq
    simp only [sub_mul, Finset.sum_sub_distrib, Int.cast_sub]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using heq)
  have hmod := (ZMod.intCast_eq_intCast_iff _ e M).mp hdiff
  have hbad : x ∈ badEvent M d (a, b, v) := by
    simp only [badEvent, if_neg hab]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hv] using hmod⟩
  have hunion : x ∈ badFrames M d :=
    Finset.mem_biUnion.mpr ⟨(a, b, v), Finset.mem_univ _, hbad⟩
  exact (Finset.mem_sdiff.mp hx).2 hunion

theorem badFrames_card (M d : Nat) (hM : 0 < M) (hd : 3 ≤ d) :
    (badFrames M d).card ≤ 18 * (d + 2) ^ 4 * M ^ (d - 1) := by
  classical
  have h := FiniteFibers.bad_union_count Finset.univ (badEvent M d)
    (2 * M ^ (d - 1)) (fun e _ => badEvent_card M d hM hd e)
  have hc := index_card_le d
  have hsquare := Nat.mul_le_mul hc hc
  have hevents : Fintype.card (Index d × Index d × Fin 9) ≤ 9 * (d + 2) ^ 4 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith only [hsquare]
  apply h.trans
  simp only [Finset.card_univ]
  calc
    Fintype.card (Index d × Index d × Fin 9) * (2 * M ^ (d - 1)) ≤
        (9 * (d + 2) ^ 4) * (2 * M ^ (d - 1)) := Nat.mul_le_mul_right _ hevents
    _ = 18 * (d + 2) ^ 4 * M ^ (d - 1) := by ring

theorem goodFrames_card (M d : Nat) (hM : 0 < M) (hd : 3 ≤ d) :
    M ^ d ≤ (goodFrames M d).card + 18 * (d + 2) ^ 4 * M ^ (d - 1) := by
  have h := Finset.card_le_card_sdiff_add_card
    (s := (Finset.univ : Finset (Fin d → Fin M))) (t := badFrames M d)
  have hb := badFrames_card M d hM hd
  have hu : (Finset.univ : Finset (Fin d → Fin M)).card = M ^ d := by simp
  rw [hu] at h
  exact h.trans (Nat.add_le_add_left hb _)

end CoefficientTwoPrecision.FrameCounting

#print axioms CoefficientTwoPrecision.FrameCounting.goodFrames_card
#print axioms CoefficientTwoPrecision.FrameCounting.goodFrames_robust
