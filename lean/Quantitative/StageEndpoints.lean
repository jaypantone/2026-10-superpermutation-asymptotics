import Quantitative.StageExtension
import SuperpermutationUpperBound43586371.AllSizesG
import Mathlib.Data.List.Permutation

/-!
# Initial and final stages of the actual word construction

The initial stage has no rows and one pending cyclic class on two letters.
Its only finite check concerns the six permutations of three letters and
uses kernel reduction. Empty extensions then give the no-seed start at any
larger supplied ordinary alphabet. The final bridge closes the actual
pending lists and invokes the supplied literal word-spelling theorem.

The word theorem here assumes a Stage with the exact mass identity. It does
not assume or assert the existence of the asymptotically efficient source
families needed to reach that stage.
-/

namespace CoefficientTwoPrecision.StageEndpoints

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371
open CoefficientTwoPrecision.SourceUniverse CoefficientTwoPrecision.StageExtension

/-- All cyclic classes of three letters lie above the unique two-letter class. -/
theorem initial_coverage (y : List Nat) (hy : y.Perm [2, 0, 1]) :
    InInsertionBlock 2 [0, 1] y := by
  have hfinite : ∀ t ∈ ([2, 0, 1] : List Nat).permutations',
      InInsertionBlock 2 [0, 1] t := by
    unfold InInsertionBlock
    decide
  exact hfinite y (List.mem_permutations'.mpr hy)

/-- The literal initial stage has one pending class and no selected row. -/
theorem initial : Stage [0, 1] 2 [] [] [[0, 1]] 0 0 0 1 := by
  refine ⟨by decide, by decide, by decide, by decide,
    ⟨by simp, by simp, by simp⟩, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro c hc
    simp at hc
  · intro c hc
    simp at hc
  · intro rs hrs
    simp at hrs
  · intro e he
    have he' : e = [0, 1] := List.mem_singleton.mp he
    subst e
    exact List.Perm.refl _
  · intro y hy
    exact Or.inr ⟨[0, 1], by simp, initial_coverage y hy⟩

@[simp] theorem transportSequence_empty (h : Nat) (letters : List Nat) :
    transportSequence [] h letters = [] := by
  induction letters with
  | nil => rfl
  | cons a rest ih => simp [transportSequence, ih, transportComps]

@[simp] theorem circleSequence_empty (letters : List Nat) :
    circleSequence [] letters = [] := by
  induction letters with
  | nil => rfl
  | cons a rest ih => simp [circleSequence, ih, extendCircles]

/-- A no-seed start on any specified fresh ordinary letters, with the exact
factorial number of pending cyclic classes. Controls are newest first. -/
theorem initial_padded (extra : List Nat) (next : Nat)
    (hnd : (next :: (extra ++ [2, 0, 1])).Nodup)
    (h9 : 9 ∉ next :: (extra ++ [2, 0, 1]))
    (h10 : 10 ∉ next :: (extra ++ [2, 0, 1])) :
    Stage (extra ++ [2, 0, 1]) next [] []
      (sourceUniverse (extra ++ [2]) [0, 1]) 0 0 0 (extra.length + 2).factorial := by
  have E := empty_many initial extra next hnd h9 h10
  have hcount : risingCount 2 (extra.length + 1) = (extra.length + 2).factorial := by
    have hc := risingCount_mul_factorial 2 (extra.length + 1) (by decide)
    simpa only [Nat.reduceSub, Nat.factorial_one, Nat.mul_one,
      show 2 + (extra.length + 1) - 1 = extra.length + 2 by omega] using hc
  simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    transportSequence_empty, circleSequence_empty, pendingUniverse,
    List.flatMap_singleton, Nat.mul_zero, Nat.mul_one, hcount] using E

/-- Closing actual pending charts and spelling the resulting closed level
produces an actual superpermutation with the finite joining bound. -/
theorem word_of_stage {A0 : List Nat} {z : Nat}
    {comps : List (List (Row Nat))} {circles pending : List (List Nat)}
    {R Q c P : Nat} (S : Stage A0 z comps circles pending R Q c P)
    (hmass : R + P * A0.length = A0.length.factorial)
    (hfull : (10 :: ((z :: A0) ++ [9])).Perm (List.range (A0.length + 3)))
    (a : Nat) (ha : 2 ≤ a) (ham : a ≤ A0.length + 1) :
    ∃ w : Word (A0.length + 3), IsSuperpermutation w ∧
      w.length ≤ F3 (A0.length + 3) + Q + A0.length * (c + P) +
        (a - 2) * (c + P) +
        (A0.length + 1 - a) *
          min (c + P) ((A0.length + 3 - 1).descFactorial (A0.length + 1 - a)) := by
  have C := S.close
  have C' := C.congr hmass rfl rfl
  exact C'.word rfl hfull a ha ham

end CoefficientTwoPrecision.StageEndpoints

#print axioms CoefficientTwoPrecision.StageEndpoints.initial
#print axioms CoefficientTwoPrecision.StageEndpoints.initial_padded
#print axioms CoefficientTwoPrecision.StageEndpoints.word_of_stage
