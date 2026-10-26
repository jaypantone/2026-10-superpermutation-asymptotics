import Quantitative.SortedFrameCells

/-!
# Ambient counts for guard-free proximity equations

The count is over all increasing physical frames. The selected family may
be any subset. A sum-position and winding cell maps injectively to its
increasing free coordinates, where one coefficient is nonzero. Thus the
factorial denominator survives the passage from coordinates to frames.
-/

namespace CoefficientTwoPrecision.GuardFreeCount

open FrameAlgebra AffineReconstruction SortedFrameSupply SortedFrameCells

variable {d : Nat}

def coordinateForm (s : Fin (d + 1)) (j l : Fin (d + 2)) (i : Fin d) : Int :=
  coordinate ((pointSlot s).symm j) i - coordinate ((pointSlot s).symm l) i

def cutShift (M : Nat) (s : Fin (d + 1)) (ell : Fin d) (j : Fin (d + 2)) : Int :=
  if j = s.succ then (ell.val : Int) * M else 0

def cellRhs (M : Nat) (s : Fin (d + 1)) (ell : Fin d)
    (a : Int) (j l : Fin (d + 2)) (b : Int) : Int :=
  b + a * (cutShift M s ell j - cutShift M s ell l)

noncomputable def cellSolutions (m M : Nat) (s : Fin (d + 1)) (ell : Fin d)
    (a : Int) (j l : Fin (d + 2)) (b : Int) : Finset (Fin (d + 2) → Fin M) := by
  classical
  exact Finset.univ.filter (fun q => StrictMono q ∧ (q 0).val = 0 ∧
    (q s.succ).val + ell.val * M = ∑ i, (freeCoordinates s q i).val ∧
    Int.ModEq (m : Int) (a * ((q j).val - ((q l).val : Int))) b)

theorem cell_mapsTo (m M : Nat) (s : Fin (d + 1)) (ell : Fin d)
    (a : Int) (j l : Fin (d + 2)) (b : Int) :
    Set.MapsTo (freeCoordinates s)
      (cellSolutions m M s ell a j l b : Set (Fin (d + 2) → Fin M))
      (SortedLinearCount.solutions m M d (fun i => a * coordinateForm s j l i)
        (cellRhs M s ell a j l b) : Set (Fin d → Fin M)) := by
  classical
  intro q hq
  obtain ⟨hmono, hz, hell, hrel⟩ := (Finset.mem_filter.mp hq).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, freeCoordinates_strictMono s q hmono, ?_⟩
  have he : a * (((q j).val : Int) - (q l).val) =
      (∑ i, (a * coordinateForm s j l i) * ((freeCoordinates s q i).val : Int)) -
        a * (cutShift M s ell j - cutShift M s ell l) := by
    rw [cut_expression s q ell hz hell j, cut_expression s q ell hz hell l]
    simp only [coordinateForm, cutShift, sub_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, mul_assoc]
    ring
  rw [he] at hrel
  have hs := hrel.add_right (a * (cutShift M s ell j - cutShift M s ell l))
  simpa only [sub_add_cancel, cellRhs] using hs

theorem cell_injective (m M : Nat) (s : Fin (d + 1)) (ell : Fin d)
    (a : Int) (j l : Fin (d + 2)) (b : Int) :
    (cellSolutions m M s ell a j l b : Set (Fin (d + 2) → Fin M)).InjOn
      (freeCoordinates s) := by
  classical
  intro q hq q' hq' he
  obtain ⟨hmono, hz, hell, hrel⟩ := (Finset.mem_filter.mp hq).2
  obtain ⟨hmono', hz', hell', hrel'⟩ := (Finset.mem_filter.mp hq').2
  funext i
  apply Fin.ext
  have hi := cut_expression s q ell hz hell i
  have hi' := cut_expression s q' ell hz' hell' i
  rw [he] at hi
  omega

theorem cell_count (m M : Nat) (hm : 0 < m) (hM : M ≤ 2 * m)
    (hd : 3 ≤ d) (s : Fin (d + 1)) (ell : Fin d) (a : Int) (ha : a ≠ 0)
    (j l : Fin (d + 2)) (hne : j ≠ l) (b : Int) :
    (d - 1).factorial * (cellSolutions m M s ell a j l b).card ≤
      M ^ (d - 1) * (2 * a.natAbs) := by
  classical
  obtain ⟨i, hi⟩ := difference_nonzero hd s j l hne
  have hcoefficient : a * coordinateForm s j l i ≠ 0 := mul_ne_zero ha hi
  have hcard := Finset.card_le_card_of_injOn (freeCoordinates s)
    (cell_mapsTo m M s ell a j l b) (cell_injective m M s ell a j l b)
  have hbound := SortedLinearCount.solutions_card_factorial m M d hm hM
    (fun i => a * coordinateForm s j l i) (cellRhs M s ell a j l b) i hcoefficient
  have habs : (a * coordinateForm s j l i).natAbs ≤ a.natAbs := by
    rw [Int.natAbs_mul]
    simpa only [coordinateForm, Nat.mul_one] using
      Nat.mul_le_mul_left a.natAbs (difference_abs s j l i)
  exact (Nat.mul_le_mul_left (d - 1).factorial hcard).trans
    (hbound.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 habs)))

noncomputable def allCells (m M d : Nat) (a : Int) (j l : Fin (d + 2)) (b : Int) :
    Finset (Fin (d + 2) → Fin M) := by
  classical
  exact Finset.univ.biUnion (fun s : Fin (d + 1) =>
    Finset.univ.biUnion (fun ell : Fin d => cellSolutions m M s ell a j l b))

theorem allCells_count (m M : Nat) (hm : 0 < m) (hM : M ≤ 2 * m)
    (hd : 3 ≤ d) (a : Int) (ha : a ≠ 0) (j l : Fin (d + 2)) (hne : j ≠ l) (b : Int) :
    (d - 1).factorial * (allCells m M d a j l b).card ≤
      (d + 1) * d * (M ^ (d - 1) * (2 * a.natAbs)) := by
  classical
  have hc : (allCells m M d a j l b).card ≤
      ∑ s : Fin (d + 1), ∑ ell : Fin d, (cellSolutions m M s ell a j l b).card := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro s _
    exact Finset.card_biUnion_le
  calc
    (d - 1).factorial * (allCells m M d a j l b).card ≤
        (d - 1).factorial *
          (∑ s : Fin (d + 1), ∑ ell : Fin d, (cellSolutions m M s ell a j l b).card) :=
      Nat.mul_le_mul_left _ hc
    _ = ∑ s : Fin (d + 1), ∑ ell : Fin d,
        (d - 1).factorial * (cellSolutions m M s ell a j l b).card := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ _s : Fin (d + 1), ∑ _ell : Fin d, M ^ (d - 1) * (2 * a.natAbs) := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro ell _
      exact cell_count m M hm hM hd s ell a ha j l hne b
    _ = _ := by simp; ring

theorem physicalFrame_mem_allCells (m M : Nat) [NeZero M] (hM : 0 < M) (hd : 0 < d)
    (a : Int) (j l : Fin (d + 2)) (b : Int) (q : Fin (d + 2) → Fin M)
    (hq : q ∈ physicalFrames M d)
    (hrel : Int.ModEq (m : Int) (a * ((q j).val - ((q l).val : Int))) b) :
    q ∈ allCells m M d a j l b := by
  classical
  obtain ⟨sumSlot, hs, hmono, hz, hrobust, hframe⟩ := physicalFrame_properties q hq
  let s := sumSlot.pred hs
  have hsEq : s.succ = sumSlot := Fin.succ_pred sumSlot hs
  have hframeInt : Int.ModEq (M : Int)
      (∑ i, frameWeight d s.succ i * ((q i).val : Int)) 0 := by
    apply (ZMod.intCast_eq_intCast_iff _ _ M).mp
    push_cast
    simpa only [hsEq] using hframe
  have hzVal : (q 0).val = 0 := by rw [hz]; rfl
  obtain ⟨ell, hell⟩ := winding_exists hM hd s q hzVal hframeInt
  apply Finset.mem_biUnion.mpr
  refine ⟨s, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
  exact ⟨ell, Finset.mem_univ _, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hmono, hzVal, hell, hrel⟩⟩

theorem physical_count (m M : Nat) [NeZero M] (hm : 0 < m) (hMpos : 0 < M)
    (hM : M ≤ 2 * m) (hd : 3 ≤ d) (a : Int) (ha : a ≠ 0)
    (j l : Fin (d + 2)) (hne : j ≠ l) (b : Int) :
    (d - 1).factorial * ((physicalFrames M d).filter
      (fun q => Int.ModEq (m : Int) (a * ((q j).val - ((q l).val : Int))) b)).card ≤
        (d + 1) * d * (M ^ (d - 1) * (2 * a.natAbs)) := by
  classical
  have hsub : (physicalFrames M d).filter
      (fun q => Int.ModEq (m : Int) (a * ((q j).val - ((q l).val : Int))) b) ⊆
      allCells m M d a j l b := by
    intro q hq
    exact physicalFrame_mem_allCells m M hMpos (by omega) a j l b q
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans
    (allCells_count m M hm hM hd a ha j l hne b)

end CoefficientTwoPrecision.GuardFreeCount

#print axioms CoefficientTwoPrecision.GuardFreeCount.cell_count
#print axioms CoefficientTwoPrecision.GuardFreeCount.physical_count
