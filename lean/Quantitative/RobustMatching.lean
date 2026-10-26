import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# The robust-difference matching argument for local simplicity

The difference family is indexed: zero has one index, and every ordered
off-diagonal pair has its own index. Thus the robustness predicate forbids
repeated ordered differences, including opposite differences of order two.

The main theorem proves that two stationary-label matches with different
source slots must both be diagonal. It uses the actual translated-cut
equalities and binary phases. Extracting these matches from equality of
rendered cyclic rows and excluding a repeat inside the remaining full run
are later literal-combinatorial obligations.
-/

namespace CoefficientTwoPrecision.RobustMatching

variable {M : Nat} {Slot : Type} [DecidableEq Slot]

abbrev DifferenceIndex (Slot : Type) := Option {p : Slot × Slot // p.1 ≠ p.2}

def difference (q : Slot → ZMod M) : DifferenceIndex Slot → ZMod M
  | none => 0
  | some p => q p.val.1 - q p.val.2

def pairIndex (i j : Slot) : DifferenceIndex Slot :=
  if h : i = j then none else some ⟨(i, j), h⟩

theorem difference_pairIndex (q : Slot → ZMod M) (i j : Slot) :
    difference q (pairIndex i j) = q i - q j := by
  by_cases h : i = j
  · subst j
    simp [pairIndex, difference]
  · simp [pairIndex, difference, h]

/-- Circular separation at least five, expressed without choosing real
distances or assuming that the modulus is prime. -/
def Robust (q : Slot → ZMod M) : Prop :=
  ∀ (a b : DifferenceIndex Slot) (e : ℤ),
    -4 ≤ e → e ≤ 4 → difference q a = difference q b + (e : ZMod M) → a = b

def bit : Bool → ℤ
  | false => 0
  | true => 1

theorem equal_cuts_difference (q : Slot → ZMod M) (t t' : ZMod M)
    (i j : Slot) (a b : Bool)
    (h : q i + t + (bit a : ZMod M) = q j + t' + (bit b : ZMod M)) :
    q i - q j = t' - t + ((bit b - bit a : ℤ) : ZMod M) := by
  push_cast
  linear_combination h

/-- Two matches imply equality of their indexed cut differences. -/
theorem matched_difference_indices (q : Slot → ZMod M) (hrobust : Robust q)
    (t t' : ZMod M) (i j i' j' : Slot) (a b a' b' : Bool)
    (hfirst : q i + t + (bit a : ZMod M) = q j + t' + (bit b : ZMod M))
    (hsecond : q i' + t + (bit a' : ZMod M) = q j' + t' + (bit b' : ZMod M)) :
    pairIndex i j = pairIndex i' j' := by
  let e : ℤ := (bit b - bit a) - (bit b' - bit a')
  have hlo : -4 ≤ e := by
    cases a <;> cases b <;> cases a' <;> cases b' <;> norm_num [e, bit]
  have hhi : e ≤ 4 := by
    cases a <;> cases b <;> cases a' <;> cases b' <;> norm_num [e, bit]
  apply hrobust _ _ e hlo hhi
  rw [difference_pairIndex, difference_pairIndex]
  have h1 := equal_cuts_difference q t t' i j a b hfirst
  have h2 := equal_cuts_difference q t t' i' j' a' b' hsecond
  rw [h1, h2]
  simp only [e, Int.cast_sub]
  ring

theorem pairIndex_equal_diagonal (i j i' j' : Slot) (hne : i ≠ i')
    (h : pairIndex i j = pairIndex i' j') : i = j ∧ i' = j' := by
  by_cases hij : i = j
  · refine ⟨hij, ?_⟩
    by_contra hne'
    simp [pairIndex, hij, hne'] at h
  · by_cases hij' : i' = j'
    · simp [pairIndex, hij, hij'] at h
    · have hp : (i, j) = (i', j') := by
        have hs : (⟨(i, j), hij⟩ : {p : Slot × Slot // p.1 ≠ p.2}) =
            ⟨(i', j'), hij'⟩ := by
          simpa only [pairIndex, dif_neg hij, dif_neg hij', Option.some.injEq] using h
        exact congrArg Subtype.val hs
      exact False.elim (hne (congrArg Prod.fst hp))

/-- The central local-simplicity implication: distinct shared stationary
labels cannot occupy different physical slots in equal cyclic rows. -/
theorem two_matches_diagonal (q : Slot → ZMod M) (hrobust : Robust q)
    (t t' : ZMod M) (i j i' j' : Slot) (hne : i ≠ i') (a b a' b' : Bool)
    (hfirst : q i + t + (bit a : ZMod M) = q j + t' + (bit b : ZMod M))
    (hsecond : q i' + t + (bit a' : ZMod M) = q j' + t' + (bit b' : ZMod M)) :
    i = j ∧ i' = j' :=
  pairIndex_equal_diagonal i j i' j' hne
    (matched_difference_indices q hrobust t t' i j i' j' a b a' b' hfirst hsecond)

/-- Once a match is diagonal, the two batch translations are equal or
neighbours on the background circle. -/
theorem diagonal_time_difference (q : Slot → ZMod M) (t t' : ZMod M)
    (i : Slot) (a b : Bool)
    (h : q i + t + (bit a : ZMod M) = q i + t' + (bit b : ZMod M)) :
    t' - t = 0 ∨ t' - t = 1 ∨ t' - t = -1 := by
  have heq : t' - t = ((bit a - bit b : ℤ) : ZMod M) := by
    push_cast
    linear_combination -h
  rw [heq]
  cases a <;> cases b <;> norm_num [bit]

/-- Robustness itself implies distinct stationary cuts. -/
theorem robust_injective (q : Slot → ZMod M) (hrobust : Robust q) :
    Function.Injective q := by
  intro i j hij
  by_contra hne
  have h := hrobust (pairIndex i j) none 0 (by norm_num) (by norm_num) (by
    rw [difference_pairIndex, hij]
    simp [difference])
  simp [pairIndex, hne] at h

end CoefficientTwoPrecision.RobustMatching

#print axioms CoefficientTwoPrecision.RobustMatching.two_matches_diagonal
#print axioms CoefficientTwoPrecision.RobustMatching.diagonal_time_difference
#print axioms CoefficientTwoPrecision.RobustMatching.robust_injective
