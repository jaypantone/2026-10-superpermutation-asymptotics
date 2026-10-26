import Quantitative.TranslatedControlOrder
import Quantitative.RobustSafety
import Quantitative.BatchSafety

/-!
# Binary perturbations preserve the physical order of an anchored frame

Robustness excludes consecutive cuts and a cut immediately before zero.
Thus adding either zero or one to each cut preserves its increasing order
before any common cyclic translation. This is the order used by the actual
renderer, not an arbitrary matching of the stationary positions.
-/

namespace CoefficientTwoPrecision.PhasedControlOrder

open RobustMatching RobustSafety BatchSafety

variable {M k : Nat} [NeZero M]

theorem no_unit_difference (q : Fin k → Fin M)
    (hrobust : Robust (fun i => cutValue (q i))) (i j : Fin k)
    (hne : i ≠ j) (e : Int) (hlo : -4 ≤ e) (hhi : e ≤ 4) :
    cutValue (q i) - cutValue (q j) ≠ (e : ZMod M) := by
  intro heq
  have h := hrobust (pairIndex i j) none e hlo hhi (by
    rw [difference_pairIndex]
    simpa only [difference, zero_add] using heq)
  exact hne (index_zero_implies_diagonal i j h)

theorem increasing_gap (q : Fin k → Fin M) (hmono : StrictMono q)
    (hrobust : Robust (fun i => cutValue (q i))) (i j : Fin k) (hij : i < j) :
    (q i).val + 1 < (q j).val := by
  have hlt : (q i).val < (q j).val := hmono hij
  by_contra hgap
  have heq : (q j).val = (q i).val + 1 := by omega
  apply no_unit_difference q hrobust j i (ne_of_gt hij) 1 (by norm_num) (by norm_num)
  simp only [cutValue, heq, Nat.cast_add, Nat.cast_one, Int.cast_one]
  ring

theorem last_gap (hM : 2 ≤ M) (q : Fin k → Fin M)
    (hrobust : Robust (fun i => cutValue (q i))) (zeroSlot : Fin k)
    (hzero : q zeroSlot = 0) (i : Fin k) : (q i).val + 1 < M := by
  by_cases hi : i = zeroSlot
  · subst i
    simp only [hzero, Fin.val_zero]
    omega
  · by_contra hgap
    have heq : (q i).val + 1 = M := by have := (q i).isLt; omega
    apply no_unit_difference q hrobust i zeroSlot hi (-1) (by norm_num) (by norm_num)
    have hcast := congrArg (fun n : Nat => (n : ZMod M)) heq
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at hcast
    simp only [cutValue, hzero, Fin.val_zero, Nat.cast_zero, sub_zero,
      Int.cast_neg, Int.cast_one]
    linear_combination hcast

def phaseNat (phase : Bool) : Nat := if phase then 1 else 0

theorem phaseNat_le (phase : Bool) : phaseNat phase ≤ 1 := by cases phase <;> decide

def phased (hM : 2 ≤ M) (q : Fin k → Fin M)
    (hrobust : Robust (fun i => cutValue (q i))) (zeroSlot : Fin k)
    (hzero : q zeroSlot = 0) (phases : Fin k → Bool) : Fin k → Fin M :=
  fun i => ⟨(q i).val + phaseNat (phases i), by
    have := last_gap hM q hrobust zeroSlot hzero i
    have := phaseNat_le (phases i)
    omega⟩

theorem phased_strictMono (hM : 2 ≤ M) (q : Fin k → Fin M)
    (hmono : StrictMono q) (hrobust : Robust (fun i => cutValue (q i)))
    (zeroSlot : Fin k) (hzero : q zeroSlot = 0) (phases : Fin k → Bool) :
    StrictMono (phased hM q hrobust zeroSlot hzero phases) := by
  intro i j hij
  have hg := increasing_gap q hmono hrobust i j hij
  have hp := phaseNat_le (phases i)
  change (q i).val + phaseNat (phases i) < (q j).val + phaseNat (phases j)
  omega

theorem phased_value (hM : 2 ≤ M) (q : Fin k → Fin M)
    (hrobust : Robust (fun i => cutValue (q i))) (zeroSlot : Fin k)
    (hzero : q zeroSlot = 0) (phases : Fin k → Bool) (i : Fin k) :
    cutValue (phased hM q hrobust zeroSlot hzero phases i) =
      cutValue (q i) + (bit (phases i) : ZMod M) := by
  simp only [phased, cutValue, Nat.cast_add]
  cases phases i <;> simp [phaseNat, bit]

end CoefficientTwoPrecision.PhasedControlOrder

#print axioms CoefficientTwoPrecision.PhasedControlOrder.phased_strictMono
#print axioms CoefficientTwoPrecision.PhasedControlOrder.phased_value
