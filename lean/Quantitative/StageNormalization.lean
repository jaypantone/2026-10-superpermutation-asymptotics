import Quantitative.StageExtension
import Quantitative.CountNormalization

/-!
# Normalized identities for the actual arbitrary-width Stage constructor

Every numerator below is the length or charge sum of the concrete lists
returned by `StageExtension.advance_width`. The proofs use that constructor's
original `Stage` fields and then the factorial identities in
`CountNormalization`. Thus these are identities for an actual constructed
stage, not recurrences postulated for unrelated numerical sequences.
-/

namespace CoefficientTwoPrecision.StageNormalization

open SuperpermutationUpperBound SuperpermutationUpperBound43586371
open SourceUniverse StageExtension

variable {A0 : List ℕ} {z : ℕ} {comps : List (List (Row ℕ))}
  {circles pending : List (List ℕ)} {R Q c P : ℕ}

theorem advance_pending (S : Stage A0 z comps circles pending R Q c P)
    (extra : List ℕ) (next : ℕ)
    (hnd : (next :: (extra ++ z :: A0)).Nodup)
    (h9 : 9 ∉ next :: (extra ++ z :: A0))
    (h10 : 10 ∉ next :: (extra ++ z :: A0))
    (K : WidthBlockFamily A0 (extra ++ [z]) next) :
    ((pending.flatMap K.remaining).length : ℚ) /
        (((extra ++ z :: A0).length - 1).factorial : ℚ) =
      ((pending.length : ℚ) / ((A0.length - 1).factorial : ℚ)) *
        (1 - (K.sourceRows : ℚ) / (risingCount A0.length (extra.length + 1) : ℚ)) := by
  have E := advance_width S extra next hnd h9 h10 K
  have hsize : (extra ++ z :: A0).length = A0.length + (extra.length + 1) := by
    simp only [List.length_append, List.length_cons]
    omega
  have hm : 0 < A0.length := lt_of_lt_of_le (by decide : 0 < 2) S.two
  have hB : K.sourceRows ≤ risingCount A0.length (extra.length + 1) := by
    simpa only [List.length_append, List.length_singleton] using K.sourceBound
  rw [E.npend, S.npend, hsize]
  exact normalized_pending_update A0.length (extra.length + 1) P K.sourceRows hm hB

theorem advance_charge (S : Stage A0 z comps circles pending R Q c P)
    (extra : List ℕ) (next : ℕ)
    (hnd : (next :: (extra ++ z :: A0)).Nodup)
    (h9 : 9 ∉ next :: (extra ++ z :: A0))
    (h10 : 10 ∉ next :: (extra ++ z :: A0))
    (K : WidthBlockFamily A0 (extra ++ [z]) next) :
    (((transportSequence comps A0.length (next :: extra) ++ pending.flatMap K.comps).flatten.map
        Row.charge).sum : ℚ) / ((extra ++ z :: A0).length.factorial : ℚ) =
      ((comps.flatten.map Row.charge).sum : ℚ) / (A0.length.factorial : ℚ) +
        ((pending.length : ℚ) / ((A0.length - 1).factorial : ℚ)) *
          ((K.sourceCharge : ℚ) / (risingCount A0.length (extra.length + 1) : ℚ)) := by
  have E := advance_width S extra next hnd h9 h10 K
  have hsize : (extra ++ z :: A0).length = A0.length + (extra.length + 1) := by
    simp only [List.length_append, List.length_cons]
    omega
  have hm : 0 < A0.length := lt_of_lt_of_le (by decide : 0 < 2) S.two
  rw [E.charge, S.charge, S.npend, hsize]
  simpa only [Nat.add_assoc] using
    normalized_charge_update A0.length (extra.length + 1) Q P K.sourceCharge hm

theorem advance_circles (S : Stage A0 z comps circles pending R Q c P)
    (extra : List ℕ) (next : ℕ)
    (hnd : (next :: (extra ++ z :: A0)).Nodup)
    (h9 : 9 ∉ next :: (extra ++ z :: A0))
    (h10 : 10 ∉ next :: (extra ++ z :: A0))
    (K : WidthBlockFamily A0 (extra ++ [z]) next) :
    ((circleSequence circles (next :: extra) ++ pending.flatMap K.circles).length : ℚ) /
        (((extra ++ z :: A0).length - 1).factorial : ℚ) =
      (circles.length : ℚ) / ((A0.length - 1).factorial : ℚ) +
        ((pending.length : ℚ) / ((A0.length - 1).factorial : ℚ)) *
          ((K.advancedCircles : ℚ) / (risingCount A0.length (extra.length + 1) : ℚ)) := by
  have E := advance_width S extra next hnd h9 h10 K
  have hsize : (extra ++ z :: A0).length = A0.length + (extra.length + 1) := by
    simp only [List.length_append, List.length_cons]
    omega
  have hm : 0 < A0.length := lt_of_lt_of_le (by decide : 0 < 2) S.two
  rw [E.ncirc, S.ncirc, S.npend, hsize]
  exact normalized_circle_update A0.length (extra.length + 1) c P K.advancedCircles hm

/-- The mass identity is preserved by the actual list constructor. -/
theorem advance_mass (S : Stage A0 z comps circles pending R Q c P)
    (extra : List ℕ) (next : ℕ)
    (hnd : (next :: (extra ++ z :: A0)).Nodup)
    (h9 : 9 ∉ next :: (extra ++ z :: A0))
    (h10 : 10 ∉ next :: (extra ++ z :: A0))
    (K : WidthBlockFamily A0 (extra ++ [z]) next)
    (hmass : comps.flatten.length + A0.length * pending.length = A0.length.factorial) :
    (transportSequence comps A0.length (next :: extra) ++ pending.flatMap K.comps).flatten.length +
        (extra ++ z :: A0).length * (pending.flatMap K.remaining).length =
      (extra ++ z :: A0).length.factorial := by
  have E := advance_width S extra next hnd h9 h10 K
  have hsize : (extra ++ z :: A0).length = A0.length + (extra.length + 1) := by
    simp only [List.length_append, List.length_cons]
    omega
  have hm : 0 < A0.length := lt_of_lt_of_le (by decide : 0 < 2) S.two
  have hB : K.sourceRows ≤ risingCount A0.length (extra.length + 1) := by
    simpa only [List.length_append, List.length_singleton] using K.sourceBound
  rw [S.rows, S.npend] at hmass
  rw [E.rows, E.npend, hsize]
  simpa only [Nat.add_assoc] using
    integer_update_mass_factorial A0.length (extra.length + 1) R P K.sourceRows hm hB hmass

end CoefficientTwoPrecision.StageNormalization

#print axioms CoefficientTwoPrecision.StageNormalization.advance_pending
#print axioms CoefficientTwoPrecision.StageNormalization.advance_charge
#print axioms CoefficientTwoPrecision.StageNormalization.advance_circles
#print axioms CoefficientTwoPrecision.StageNormalization.advance_mass
