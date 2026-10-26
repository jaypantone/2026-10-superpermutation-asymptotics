import Quantitative.SortedFrameSupply
import Quantitative.SortedLinearCount
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Sum-position and winding cells of an actual sorted frame

Remove the anchored zero and the sum position from an increasing frame.
The remaining d coordinates are still increasing. On each fixed sum
position and winding, every frame cut is an integral affine expression
in these coordinates. Distinct cuts give different coefficient vectors.
-/

namespace CoefficientTwoPrecision.SortedFrameCells

open FrameAlgebra FrameCounting AffineReconstruction SortedFrameSupply

variable {M d : Nat}

def pointSlot (sumPosition : Fin (d + 1)) : Point d ≃ Fin (d + 2) :=
  ((finSuccEquiv' (0 : Fin (d + 2))).trans
    (Equiv.optionCongr (finSuccEquiv' sumPosition))).symm

def freeSlot (sumPosition : Fin (d + 1)) (i : Fin d) : Fin (d + 2) :=
  (sumPosition.succAbove i).succ

@[simp] theorem pointSlot_zero (s : Fin (d + 1)) : pointSlot s none = 0 := rfl

@[simp] theorem pointSlot_sum (s : Fin (d + 1)) : pointSlot s (some none) = s.succ := by
  simp [pointSlot, Equiv.optionCongr, finSuccEquiv', Fin.succAbove_zero]

@[simp] theorem pointSlot_coordinate (s : Fin (d + 1)) (i : Fin d) :
    pointSlot s (some (some i)) = freeSlot s i := by
  simp [pointSlot, freeSlot, Equiv.optionCongr, finSuccEquiv', Fin.succAbove_zero]

theorem freeSlot_strictMono (s : Fin (d + 1)) : StrictMono (freeSlot s) :=
  Fin.strictMono_succ.comp (Fin.strictMono_succAbove s)

def freeCoordinates (s : Fin (d + 1)) (q : Fin (d + 2) → Fin M) : Fin d → Fin M :=
  fun i => q (freeSlot s i)

theorem freeCoordinates_strictMono (s : Fin (d + 1)) (q : Fin (d + 2) → Fin M)
    (hq : StrictMono q) : StrictMono (freeCoordinates s q) :=
  hq.comp (freeSlot_strictMono s)

theorem frame_relation_split (s : Fin (d + 1)) (q : Fin (d + 2) → Fin M)
    (hz : (q 0).val = 0) :
    (∑ j, frameWeight d s.succ j * ((q j).val : Int)) =
      (q s.succ).val - ∑ i, ((freeCoordinates s q i).val : Int) := by
  rw [Fin.sum_univ_succ]
  simp only [hz, Nat.cast_zero, mul_zero, zero_add]
  rw [Fin.sum_univ_succAbove _ s]
  simp [frameWeight, Fin.succ_ne_zero, Fin.succAbove_ne, Fin.succ_inj,
    freeCoordinates, freeSlot, sub_eq_add_neg]

/-- The winding is derived from the actual affine relation and residues. -/
theorem winding_exists (hm : 0 < M) (hd : 0 < d) (s : Fin (d + 1))
    (q : Fin (d + 2) → Fin M) (hz : (q 0).val = 0)
    (hrel : Int.ModEq (M : Int) (∑ j, frameWeight d s.succ j * ((q j).val : Int)) 0) :
    ∃ ell : Fin d, (q s.succ).val + ell.val * M =
      ∑ i, (freeCoordinates s q i).val := by
  rw [frame_relation_split s q hz] at hrel
  have hs := hrel.add_right (∑ i, ((freeCoordinates s q i).val : Int))
  simp only [sub_add_cancel, zero_add] at hs
  have hsNat : Nat.ModEq M (q s.succ).val (∑ i, (freeCoordinates s q i).val) := by
    apply Int.natCast_modEq_iff.mp
    simpa only [Nat.cast_sum] using hs
  let total := ∑ i, (freeCoordinates s q i).val
  have htotal : total < d * M := by
    have hb : total ≤ d * (M - 1) := by
      calc
        total ≤ ∑ _i : Fin d, (M - 1) := by
          dsimp only [total]
          apply Finset.sum_le_sum
          intro i _
          have hi := (freeCoordinates s q i).isLt
          omega
        _ = d * (M - 1) := by simp
    have hp : M - 1 + 1 = M := by omega
    nlinarith
  let ell : Fin d := ⟨total / M, (Nat.div_lt_iff_lt_mul hm).mpr htotal⟩
  have hmod : (q s.succ).val = total % M := by
    have he := hsNat
    change (q s.succ).val % M = total % M at he
    rwa [Nat.mod_eq_of_lt (q s.succ).isLt] at he
  refine ⟨ell, ?_⟩
  rw [hmod]
  change total % M + (total / M) * M = total
  simpa only [Nat.mul_comm] using Nat.mod_add_div total M

theorem cut_expression (s : Fin (d + 1)) (q : Fin (d + 2) → Fin M)
    (ell : Fin d) (hz : (q 0).val = 0)
    (hell : (q s.succ).val + ell.val * M = ∑ i, (freeCoordinates s q i).val)
    (j : Fin (d + 2)) :
    ((q j).val : Int) =
      (∑ i, coordinate ((pointSlot s).symm j) i * ((freeCoordinates s q i).val : Int)) -
        (if j = s.succ then (ell.val : Int) * M else 0) := by
  have hzero : (pointSlot s).symm 0 = none := by
    apply (pointSlot s).injective
    simp
  have hsum : (pointSlot s).symm s.succ = some none := by
    apply (pointSlot s).injective
    simp
  have hcoord (i : Fin d) : (pointSlot s).symm (freeSlot s i) = some (some i) := by
    apply (pointSlot s).injective
    simp
  obtain ⟨p, rfl⟩ := (pointSlot s).surjective j
  cases p with
  | none => simp [hz, hzero, coordinate, (Fin.succ_ne_zero s).symm]
  | some p =>
      cases p with
      | none =>
          simp only [pointSlot_sum, hsum, coordinate, one_mul, ite_true]
          have hc : ((q s.succ).val : Int) + ell.val * M =
              ∑ i, ((freeCoordinates s q i).val : Int) := by exact_mod_cast hell
          linarith
      | some i =>
          have hne : freeSlot s i ≠ s.succ := by
            exact fun he => Fin.succAbove_ne s i (Fin.succ_inj.mp he)
          simp only [pointSlot_coordinate, hcoord, coordinate, ite_mul, one_mul,
            zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_neg hne, sub_zero]
          rfl

theorem difference_nonzero (hd : 3 ≤ d) (s : Fin (d + 1))
    (j l : Fin (d + 2)) (hne : j ≠ l) :
    ∃ i : Fin d, coordinate ((pointSlot s).symm j) i -
      coordinate ((pointSlot s).symm l) i ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hp : (pointSlot s).symm j ≠ (pointSlot s).symm l :=
    fun he => hne ((pointSlot s).symm.injective he)
  have he := ordered_difference_injective hd ((pointSlot s).symm j)
    ((pointSlot s).symm l) none none hp (fun i => by simpa [coordinate] using hn i)
  exact hp (he.1.trans he.2.symm)

theorem difference_abs (s : Fin (d + 1)) (j l : Fin (d + 2)) (i : Fin d) :
    (coordinate ((pointSlot s).symm j) i -
      coordinate ((pointSlot s).symm l) i).natAbs ≤ 1 := by
  have hj := coordinate_bounds ((pointSlot s).symm j) i
  have hl := coordinate_bounds ((pointSlot s).symm l) i
  omega

end CoefficientTwoPrecision.SortedFrameCells

#print axioms CoefficientTwoPrecision.SortedFrameCells.winding_exists
#print axioms CoefficientTwoPrecision.SortedFrameCells.cut_expression
#print axioms CoefficientTwoPrecision.SortedFrameCells.difference_nonzero
