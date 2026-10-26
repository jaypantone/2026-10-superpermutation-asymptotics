import Quantitative.RepairedContourCounts
import Quantitative.CanonicalEventAvoidance
import Quantitative.GridAlphabet

/-!
# Constructing the actual repaired contour of each surviving candidate

The finite candidate specifies its active block, guard embedding and
selected labelled frame. Its canonical event set is converted to the
initial engine roles before grouping and compilation. The object below
retains the same cut, groups, trace and row list, together with all local
insertion, simplicity and counting conclusions of the proved builder.
-/

namespace CoefficientTwoPrecision.CandidateConstruction

open SuperpermutationUpperBound GuardCatalogue GridBackground CandidateSpace LabelledReconstruction
open ProximityCatalogue ProximitySurvivors CandidateEvents EventLabelTransport
open PrimaryCatalogue
open RepairGroups RepairProgram RepairAvoidance CyclicRepairSchedule FiniteRoles
open SourceAlphabet OriginTransport LiteralSchedule TargetTrace SourceFamilyAdapter
open SourceUniverse SourceAdvancement ActualCyclicMatching SortedFrameSupply

variable {m d A : Nat}

def initial (rowIndex : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (node : Labelled (m + guardNumber d A) d) : FiniteRoles.Role (d + 2) ≃ Fin (d + 3) :=
  ((PhysicalJointStates.reverseRoles (d + 2)).trans node.2).trans rowIndex

def program (groups : List (EventGroup (2 * (d + 3) + 1) ForbiddenPair)) : List MacroCatalogue.Macro :=
  compile (d + 3) (groupPhase (d + 2)) (groupChoice (d + 2)) (m + guardNumber d A) 0 groups

variable (hA : 0 < A) (old : Fin m → Nat) (ho : Function.Injective old)
variable (physical : Physical d A → Nat) (hl : Function.Injective physical)
variable (hcross : ∀ p i, physical p ≠ old i)

noncomputable def canonicalBackground (candidate : Candidate m d A) : Fin (m + guardNumber d A) → Nat :=
  background hA old ho physical hl hcross candidate.1 candidate.2.1

def activeEmbed (candidate : Candidate m d A) (row : Fin (d + 3)) : Nat :=
  physical (activeControl d A hA candidate.1 row)

variable [NeZero (m + guardNumber d A)]

structure Witness (controls oldWord : List Nat)
    (rowIndex : FiniteRoles.Role (d + 2) ≃ Fin (d + 3)) (candidate : Candidate m d A)
    (hMpos : 0 < m + guardNumber d A) where
  cut : ZMod (m + guardNumber d A)
  groups : List (EventGroup (2 * (d + 3) + 1) ForbiddenPair)
  grouped : (groups.flatMap EventGroup.events).Perm
    (liftedEvents (mapEvents (encodePair (initial rowIndex candidate.2.2))
      (CandidateEvents.events hA candidate)) cut)
  before : groups.Pairwise RepairGroups.Before
  bounds : ∀ G ∈ groups, 2 * (d + 3) + 1 < G.first ∧
    G.last + (2 * (d + 3) + 1) < m + guardNumber d A
  contour : SourceContour (controls ++ oldWord) (m + guardNumber d A + (d + 2) - 1)
  gap : Nat
  sweeps : List Nat
  finalGap : Nat
  trace : Trace hMpos
    (shiftedBackground (canonicalBackground hA old ho physical hl hcross candidate) (translationCut cut))
    (FiniteProgram.word (d + 2) (program (m := m) (A := A) groups))
    (engineLabels (activeEmbed hA physical candidate) (initial rowIndex candidate.2.2))
    (fun rank => candidate.2.2.1 rank.rev) gap sweeps finalGap
  rows_eq : contour.rows = scheduleRows 9 sweeps
    (renderedBase
      (shiftedBackground (canonicalBackground hA old ho physical hl hcross candidate) (translationCut cut))
      (engineLabels (activeEmbed hA physical candidate) (initial rowIndex candidate.2.2))
      (fun rank => candidate.2.2.1 rank.rev) gap)
  simple : contour.rows.Pairwise (fun first second => ¬ first.base.IsRotated second.base)
  envelope : ∀ row ∈ contour.rows,
    LiteralEnvelope.Envelope (canonicalBackground hA old ho physical hl hcross candidate)
      (engineLabels (activeEmbed hA physical candidate) (initial rowIndex candidate.2.2))
      (fun rank => candidate.2.2.1 rank.rev) row.base
  insertion : ∀ row ∈ contour.rows, InsertionAbove controls oldWord row.base
  charge : (contour.rows.map Row.charge).sum = 2 * (m + guardNumber d A) * (d + 2)
  gcd_le : portGcd contour.rows (m + guardNumber d A + (d + 2) - 1) ≤ d + 2
  row_error : |(contour.rows.length : ℚ) -
    (((m + guardNumber d A) * ((d + 2 - 1) * (m + guardNumber d A) +
      (d + 2) * (d + 2 + 1) + 1) : Nat) : ℚ)| ≤
    ((10 * (d + 2 + 1) ^ 2 * occurrenceBound d A * (m + guardNumber d A) : Nat) : ℚ)

theorem exists_witness
    (hm : 0 < m) (hd : 3 ≤ d)
    (hM : 2 * (d + 2) ≤ m + guardNumber d A)
    (hupper : m + guardNumber d A ≤ 2 * m)
    (hdiv : d + 3 ∣ m + guardNumber d A)
    (hsize : radius d < m + guardNumber d A)
    (hroom : (2 * (2 * (d + 3) + 1) + 1) * occurrenceBound d A < m + guardNumber d A)
    (controls oldWord : List Nat) (holdPos : 0 < oldWord.length)
    (hnd : (controls ++ oldWord).Nodup) (h9 : 9 ∉ controls ++ oldWord)
    (hword : (List.finRange m).map old = oldWord)
    (hold : ∀ a, a ∈ oldWord ↔ ∃ i, old i = a)
    (hcontrol : ∀ a, a ∈ controls ↔ ∃ p, physical p = a)
    (rowIndex : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ labelledFrames (m + guardNumber d A) d)
    (candidate : Candidate m d A) (hcandidate : candidate ∈ survivors m d A hA S) :
    Nonempty (Witness hA old ho physical hl hcross controls oldWord rowIndex candidate (by omega)) := by
  classical
  have hnode := ((mem_survivors hA S candidate).mp hcandidate).1
  have hframe := (Finset.mem_product.mp (hS hnode)).1
  obtain ⟨sumSlot, hsumSlot, hmono, hzero, hrobust, hrelation⟩ :=
    physicalFrame_properties candidate.2.2.1 hframe
  obtain ⟨hbg, hembed, hdisjoint, hsupport, hactive, hprojection⟩ :=
    GridAlphabet.background_data hA old ho physical hl hcross controls oldWord holdPos hnd
      hword hold hcontrol candidate.1 candidate.2.1
  let encoded := mapEvents (encodePair (initial rowIndex candidate.2.2)) (CandidateEvents.events hA candidate)
  have hcount : encoded.card ≤ occurrenceBound d A :=
    (mapEvents_card _ _).trans (CandidateEvents.events_card hm hupper (by omega) hA candidate)
  have hroomEncoded : (2 * (2 * (d + 3) + 1) + 1) * encoded.card < m + guardNumber d A :=
    (Nat.mul_le_mul_left _ hcount).trans_lt hroom
  have hsep : Separated encoded (2 * (d + 3) + 1) :=
    mapEvents_separated _ _ (CandidateEvents.events_separated hsize hA S candidate hcandidate)
  obtain ⟨cut, groups, hgrouped, hbefore, hbounds, C, gap, sweeps, finalGap,
      htrace, hrows, hclosed, hsimple, henvelope, hinsertion, hcharge, hgcd, herror⟩ :=
    RepairedContourCounts.construct_counted_repair (by omega : 5 ≤ d + 2) hM hdiv
      controls oldWord holdPos hnd h9
      (canonicalBackground hA old ho physical hl hcross candidate) (activeEmbed hA physical candidate)
      hbg hembed hdisjoint hsupport hactive hprojection
      (initial rowIndex candidate.2.2) candidate.2.2.1 hmono hrobust hzero
      (occurrenceBound d A) encoded hcount hroomEncoded hsep
      (fun pair => mobilePhase (d + 2) pair.1) (fun pair => mobilePhase_lt _ _)
      (fun pair => parkingChoice pair.2)
  exact ⟨{
    cut := cut
    groups := groups
    grouped := hgrouped
    before := hbefore
    bounds := hbounds
    contour := C
    gap := gap
    sweeps := sweeps
    finalGap := finalGap
    trace := htrace
    rows_eq := hrows
    simple := hsimple
    envelope := henvelope
    insertion := hinsertion
    charge := hcharge
    gcd_le := hgcd
    row_error := herror
  }⟩

end CoefficientTwoPrecision.CandidateConstruction

#print axioms CoefficientTwoPrecision.CandidateConstruction.exists_witness
