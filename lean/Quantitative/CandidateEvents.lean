import Quantitative.ProximitySurvivors
import Quantitative.CyclicRepairSchedule

/-!
# The canonical finite event set supplied to the repair schedule

An event occurrence contributes its canonical batch residue and the
actual forbidden physical-row/slot pair. Repeated catalogue descriptions
are removed by taking an image. The count can only decrease, and the
survivor predicate supplies exactly the circular separation required by
the existing repair-program constructor.
-/

namespace CoefficientTwoPrecision.CandidateEvents

open GuardCatalogue CandidateSpace LabelledReconstruction PrimaryCatalogue
open ProximityCatalogue ProximitySurvivors

variable {m d A : Nat}

noncomputable def events (hA : 0 < A) (candidate : Candidate m d A) :
    Finset (ZMod (m + guardNumber d A) × (Fin (d + 3) × Fin (d + 2))) := by
  classical
  exact (occurrences m hA candidate.1 candidate.2.1 candidate.2.2.1).image
    (fun occurrence => ((occurrence.2.val : ZMod (m + guardNumber d A)),
      forbiddenPair hA candidate.1 occurrence.1))

theorem event_mem (hA : 0 < A) (candidate : Candidate m d A)
    (event : Event d A hA candidate.1) (time : Fin (m + guardNumber d A))
    (htime : time ∈ times m hA candidate.1 candidate.2.1 candidate.2.2.1 event) :
    ((time.val : ZMod (m + guardNumber d A)), forbiddenPair hA candidate.1 event) ∈
      events hA candidate := by
  classical
  exact Finset.mem_image.mpr
    ⟨⟨event, time⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, htime⟩, rfl⟩

theorem events_card (hm : 0 < m) (hM : m + guardNumber d A ≤ 2 * m)
    (hd : 2 ≤ d) (hA : 0 < A) (candidate : Candidate m d A) :
    (events hA candidate).card ≤ occurrenceBound d A := by
  classical
  exact Finset.card_image_le.trans
    (occurrences_card m hm hM hd hA candidate.1 candidate.2.1 candidate.2.2.1)

theorem events_separated (hsize : radius d < m + guardNumber d A) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) (candidate : Candidate m d A)
    (hcandidate : candidate ∈ survivors m d A hA S) :
    CyclicRepairSchedule.Separated (events hA candidate) (2 * (d + 3) + 1) := by
  classical
  intro x hx y hy delta hdelta heq
  obtain ⟨first, hfirst, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨second, hsecond, rfl⟩ := Finset.mem_image.mp hy
  have htFirst := (Finset.mem_sigma.mp hfirst).2
  have htSecond := (Finset.mem_sigma.mp hsecond).2
  by_contra hne
  apply ProximitySurvivors.events_separated hsize hA S candidate hcandidate
    first.1 second.1 hne first.2 second.2 htFirst htSecond
  refine ⟨delta, ?_, ?_⟩
  · have hrad : 2 * (2 * (d + 3) + 1) = radius d := by unfold radius; ring
    have hd : |delta| ≤ (radius d : Int) := by simpa only [hrad] using hdelta
    have hc : (delta.natAbs : Int) ≤ (radius d : Int) := by
      simpa only [Int.natCast_natAbs] using hd
    exact_mod_cast hc
  · apply (ZMod.intCast_eq_intCast_iff _ _ (m + guardNumber d A)).mp
    push_cast
    change (second.2.val : ZMod (m + guardNumber d A)) - first.2.val = delta
    change (second.2.val : ZMod (m + guardNumber d A)) = first.2.val + delta at heq
    rw [heq]
    ring

theorem grouped_circle [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hM : m + guardNumber d A ≤ 2 * m) (hd : 2 ≤ d)
    (hsize : radius d < m + guardNumber d A) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) (candidate : Candidate m d A)
    (hcandidate : candidate ∈ survivors m d A hA S)
    (hroom : (2 * (2 * (d + 3) + 1) + 1) * occurrenceBound d A < m + guardNumber d A) :
    ∃ cut : ZMod (m + guardNumber d A),
    ∃ groups : List (RepairGroups.EventGroup (2 * (d + 3) + 1)
      (Fin (d + 3) × Fin (d + 2))),
      (groups.flatMap RepairGroups.EventGroup.events).Perm
        (CyclicRepairSchedule.liftedEvents (events hA candidate) cut) ∧
      groups.Pairwise RepairGroups.Before ∧
      ∀ group ∈ groups, 2 * (d + 3) + 1 < group.first ∧
        group.last + (2 * (d + 3) + 1) < m + guardNumber d A := by
  apply CyclicRepairSchedule.exists_grouped_circle
  · exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (events_card hm hM hd hA candidate)) hroom
  · exact events_separated hsize hA S candidate hcandidate

end CoefficientTwoPrecision.CandidateEvents

#print axioms CoefficientTwoPrecision.CandidateEvents.events_card
#print axioms CoefficientTwoPrecision.CandidateEvents.events_separated
#print axioms CoefficientTwoPrecision.CandidateEvents.grouped_circle
