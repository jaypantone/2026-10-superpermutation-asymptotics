import Quantitative.ProximityCatalogue
import Quantitative.GuardCandidateLoss

/-!
# The actual candidate filter that separates forbidden events

This second deletion uses the same fixed labelled frame family as the
first deletion. It removes candidates satisfying a proximity equation
for two different forbidden pairs. The resulting separation statement
concerns the actual primary-event time sets of each surviving candidate.
-/

namespace CoefficientTwoPrecision.ProximitySurvivors

open GuardCatalogue CandidateSpace LabelledReconstruction PrimaryCatalogue PrimaryRank
open ProximityCatalogue

variable {m d A : Nat}

noncomputable def frameTerm (hA : 0 < A) (active : Active d A)
    (q : Fin (d + 2) → Fin (m + guardNumber d A))
    (event : PairEvent d A hA active) : Int :=
  coefficient hA active event.1 * coefficient hA active event.2.1 *
    ((q (slot hA active event.1)).val - ((q (slot hA active event.2.1)).val : Int))

def Equation (hA : 0 < A) (active : Active d A)
    (x : Fin (guardNumber d A) → Fin m)
    (q : Fin (d + 2) → Fin (m + guardNumber d A))
    (event : PairEvent d A hA active) : Prop :=
  Int.ModEq (m : Int)
    (frameTerm hA active q event +
      ∑ u, guardCross hA active event.1 event.2.1 u * (x u).val)
    (rightSide hA active event)

def Bad (hA : 0 < A) (candidate : Candidate m d A) : Prop :=
  ∃ event : PairEvent d A hA candidate.1,
    forbiddenPair hA candidate.1 event.1 ≠ forbiddenPair hA candidate.1 event.2.1 ∧
      Equation hA candidate.1 candidate.2.1 candidate.2.2.1 event

noncomputable def survivors (m d A : Nat) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) : Finset (Candidate m d A) := by
  classical
  exact (GuardCandidateLoss.retained m d A hA S).filter (fun candidate => ¬ Bad hA candidate)

theorem mem_survivors (hA : 0 < A) (S : Finset (Labelled (m + guardNumber d A) d))
    (candidate : Candidate m d A) :
    candidate ∈ survivors m d A hA S ↔ candidate.2.2 ∈ S ∧
      candidate.2.1 ∈ goodEmbeddings m d A hA candidate.1 ∧ ¬ Bad hA candidate := by
  classical
  simp only [survivors, Finset.mem_filter, GuardCandidateLoss.mem_retained, and_assoc]

theorem survivors_subset (hA : 0 < A) (S : Finset (Labelled (m + guardNumber d A) d)) :
    survivors m d A hA S ⊆ GuardCandidateLoss.retained m d A hA S := by
  classical
  exact Finset.filter_subset _ _

theorem events_separated (hsize : radius d < m + guardNumber d A) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) (candidate : Candidate m d A)
    (hcandidate : candidate ∈ survivors m d A hA S)
    (first second : Event d A hA candidate.1)
    (hdistinct : forbiddenPair hA candidate.1 first ≠ forbiddenPair hA candidate.1 second)
    (timeFirst timeSecond : Fin (m + guardNumber d A))
    (hfirst : timeFirst ∈ times m hA candidate.1 candidate.2.1 candidate.2.2.1 first)
    (hsecond : timeSecond ∈ times m hA candidate.1 candidate.2.1 candidate.2.2.1 second) :
    ¬ Close (radius d) timeFirst timeSecond := by
  intro hclose
  have hnot := ((mem_survivors hA S candidate).mp hcandidate).2.2
  obtain ⟨event, hleft, hright, heq⟩ := nearby_entry hsize hA candidate.1 first second
    candidate.2.1 candidate.2.2.1 timeFirst timeSecond hfirst hsecond hclose
  apply hnot
  refine ⟨event, by simpa only [hleft, hright] using hdistinct, ?_⟩
  simpa only [Equation, frameTerm, hleft, hright] using heq

theorem equation_iff_guards (hA : 0 < A) (active : Active d A)
    (x : Fin (guardNumber d A) → Fin m)
    (q : Fin (d + 2) → Fin (m + guardNumber d A))
    (event : PairEvent d A hA active) :
    Equation hA active x q event ↔
      Int.ModEq (m : Int) (∑ u, guardCross hA active event.1 event.2.1 u * (x u).val)
        (rightSide hA active event - frameTerm hA active q event) := by
  constructor
  · intro h
    simpa only [add_sub_cancel_left] using h.sub_right (frameTerm hA active q event)
  · intro h
    have hs := h.add_right (frameTerm hA active q event)
    change Int.ModEq (m : Int)
      (frameTerm hA active q event +
        ∑ u, guardCross hA active event.1 event.2.1 u * (x u).val)
      (rightSide hA active event)
    convert hs using 1 <;> ring

theorem equation_guard_free (hA : 0 < A) (active : Active d A)
    (x : Fin (guardNumber d A) → Fin m)
    (q : Fin (d + 2) → Fin (m + guardNumber d A))
    (event : PairEvent d A hA active)
    (hzero : ∀ u, guardCross hA active event.1 event.2.1 u = 0) :
    Equation hA active x q event ↔
      Int.ModEq (m : Int) (frameTerm hA active q event) (rightSide hA active event) := by
  simp only [Equation, hzero, zero_mul, Finset.sum_const_zero, add_zero]

end CoefficientTwoPrecision.ProximitySurvivors

#print axioms CoefficientTwoPrecision.ProximitySurvivors.events_separated
