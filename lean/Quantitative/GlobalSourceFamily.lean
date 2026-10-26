import Quantitative.CandidateRowState
import Quantitative.ContourCollection

/-!
# The constructed globally disjoint canonical source family

Every surviving candidate contributes the actual contour built from its
converted event set. The recorded trace proves its canonical row state
and repaired avoidance. Together with literal packing, these facts prove
cross-candidate cyclic disjointness. Enumerating the finite survivor set
then gives the actual family, its insertion property, all local counts,
and the global cyclic-distinctness condition required by Stage assembly.
-/

namespace CoefficientTwoPrecision.GlobalSourceFamily

open SuperpermutationUpperBound GuardCatalogue GridBackground PhysicalOldCuts
open CandidateSpace LabelledReconstruction ProximityCatalogue ProximitySurvivors
open CandidateConstruction CandidateRowState SourceFamilyAdapter SourceUniverse SourceAdvancement
open SortedFrameSupply PrimaryCatalogue ContourCollection

variable {m d A : Nat} [NeZero (m + guardNumber d A)]
variable (hA : 0 < A) (old : Fin m → Nat) (ho : Function.Injective old)
variable (physical : Physical d A → Nat) (hl : Function.Injective physical)
variable (hcross : ∀ p i, physical p ≠ old i)
variable (controls oldWord : List Nat)
variable (rowIndex : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
variable (S : Finset (Labelled (m + guardNumber d A) d))

def Packed : Prop :=
  ∀ (bg : Fin (m + guardNumber d A) → Nat) (embed : FiniteRoles.Role (d + 2) → Nat),
    Function.Injective bg → Function.Injective embed → (∀ i c, bg i ≠ embed c) →
    ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
      ∀ first second : List Nat, LiteralPacking.InEnvelope bg embed source first →
        LiteralPacking.InEnvelope bg embed target second → ¬ first.IsRotated second

theorem witnesses_disjoint (hm : 0 < m) (hd : 3 ≤ d)
    (hS : S ⊆ labelledFrames (m + guardNumber d A) d) (hpacking : Packed S)
    (first second : Candidate m d A)
    (hfirst : first ∈ survivors m d A hA S) (hsecond : second ∈ survivors m d A hA S)
    (hne : first ≠ second) (hMpos : 0 < m + guardNumber d A)
    (C : Witness hA old ho physical hl hcross controls oldWord rowIndex first hMpos)
    (D : Witness hA old ho physical hl hcross controls oldWord rowIndex second hMpos)
    (row other : Row Nat) (hrow : row ∈ C.contour.rows) (hother : other ∈ D.contour.rows) :
    ¬ row.base.IsRotated other.base := by
  obtain ⟨roleL, localL, gapL, timeL, phaseL, hbaseL, hframeL, hlocalL, havoidL⟩ :=
    row_state hA old ho physical hl hcross rowIndex C hd S hS hfirst row hrow
  obtain ⟨roleR, localR, gapR, timeR, phaseR, hbaseR, hframeR, hlocalR, havoidR⟩ :=
    row_state hA old ho physical hl hcross rowIndex D hd S hS hsecond other hother
  have henvelopeL := literal_envelope hA old ho physical hl hcross rowIndex C row hrow
  have henvelopeR := literal_envelope hA old ho physical hl hcross rowIndex D other hother
  rw [hbaseL] at henvelopeL
  rw [hbaseR] at henvelopeR
  have hnot := CandidateCollision.actual_rows_disjoint hm (by omega) hA old ho physical hl hcross
    rowIndex S hpacking first second hfirst hsecond hne roleL roleR localL localR gapL gapR
    hframeL hframeR timeL phaseL hlocalL henvelopeL henvelopeR havoidL
  simpa only [hbaseL, hbaseR] using hnot

include ho hl hcross rowIndex in
/-- Every premise concerns the actual alphabet, selected packing, or
construction parameters. The family and all of its source properties are
constructed in the proof, including global cyclic distinctness. -/
theorem exists_family (hm : 0 < m) (hd : 3 ≤ d)
    (hM : 2 * (d + 2) ≤ m + guardNumber d A)
    (hupper : m + guardNumber d A ≤ 2 * m)
    (hdiv : d + 3 ∣ m + guardNumber d A)
    (hsize : radius d < m + guardNumber d A)
    (hroom : (2 * (2 * (d + 3) + 1) + 1) * occurrenceBound d A < m + guardNumber d A)
    (holdPos : 0 < oldWord.length) (hnd : (controls ++ oldWord).Nodup)
    (h9 : 9 ∉ controls ++ oldWord)
    (hword : (List.finRange m).map old = oldWord)
    (hold : ∀ a, a ∈ oldWord ↔ ∃ i, old i = a)
    (hcontrol : ∀ a, a ∈ controls ↔ ∃ p, physical p = a)
    (hS : S ⊆ labelledFrames (m + guardNumber d A) d) (hpacking : Packed S) :
    ∃ F : List (SourceContour (controls ++ oldWord) (m + guardNumber d A + (d + 2) - 1)),
      F.length = (survivors m d A hA S).card ∧
      (∀ row ∈ sourceRows F, InsertionAbove controls oldWord row.base) ∧
      (sourceRows F).Pairwise (fun row other => ¬ CyclicEq row.base other.base) ∧
      ∀ C ∈ F,
        (C.rows.map Row.charge).sum = 2 * (d + 3 - 1) * (m + guardNumber d A) ∧
        portGcd C.rows (m + guardNumber d A + (d + 2) - 1) ≤ d + 3 - 1 ∧
        |(C.rows.length : ℚ) -
          (((m + guardNumber d A) * ((d + 3 - 2) * (m + guardNumber d A) +
            (d + 3) * (d + 3 - 1) + 1) : Nat) : ℚ)| ≤
          ((10 * (d + 3) ^ 2 * occurrenceBound d A * (m + guardNumber d A) : Nat) : ℚ) := by
  classical
  let T := survivors m d A hA S
  have hMpos : 0 < m + guardNumber d A := by omega
  have hexists (candidate : T) : Nonempty
      (Witness hA old ho physical hl hcross controls oldWord rowIndex candidate.val hMpos) :=
    exists_witness hA old ho physical hl hcross hm hd hM hupper hdiv hsize hroom
      controls oldWord holdPos hnd h9 hword hold hcontrol rowIndex S hS candidate.val candidate.property
  let chosen (candidate : T) := Classical.choice (hexists candidate)
  let contour (candidate : T) := (chosen candidate).contour
  let F := collection T contour
  refine ⟨F, collection_length T contour, ?_, ?_, ?_⟩
  · exact collection_insertion T contour controls oldWord
      (fun candidate row hrow => (chosen candidate).insertion row hrow)
  · apply collection_distinct T contour (fun candidate => (chosen candidate).simple)
    intro first second hne row hrow other hother
    apply witnesses_disjoint hA old ho physical hl hcross controls oldWord rowIndex S
      hm hd hS hpacking first.val second.val first.property second.property
      (fun he => hne (Subtype.ext he)) hMpos (chosen first) (chosen second) row other hrow hother
  · apply collection_forall T contour
    intro candidate
    have hcharge := (chosen candidate).charge
    have hgcd := (chosen candidate).gcd_le
    have herror := (chosen candidate).row_error
    have hsub : d + 3 - 1 = d + 2 := by omega
    have hsub2 : d + 3 - 2 = d + 2 - 1 := by omega
    have hbaseline : (m + guardNumber d A) *
        ((d + 2 - 1) * (m + guardNumber d A) + (d + 2) * (d + 2 + 1) + 1) =
        (m + guardNumber d A) *
        ((d + 3 - 2) * (m + guardNumber d A) + (d + 3) * (d + 3 - 1) + 1) := by
      rw [hsub, hsub2]
      ring
    refine ⟨?_, by simpa only [hsub] using hgcd, ?_⟩
    · rw [hsub]
      exact hcharge.trans (by ring)
    · rw [hbaseline] at herror
      exact herror

end CoefficientTwoPrecision.GlobalSourceFamily

#print axioms CoefficientTwoPrecision.GlobalSourceFamily.witnesses_disjoint
#print axioms CoefficientTwoPrecision.GlobalSourceFamily.exists_family
