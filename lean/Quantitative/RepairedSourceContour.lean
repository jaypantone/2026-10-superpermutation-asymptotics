import Quantitative.LocalSourceContour
import Quantitative.CyclicRepairSchedule

/-!
# A local source contour from an actual separated cyclic event set

The finite event set is cut, grouped, and compiled by the proved repair
construction. This theorem discharges the program-count, role-return and
first/last-normal premises of the literal source builder. The canonical
cut is returned alongside the actual groups and trace, so subsequent
collision exclusion can use the same event and prefix coordinates.
-/

namespace CoefficientTwoPrecision.RepairedSourceContour

open LiteralSchedule TargetTrace MacroCatalogue FiniteRoles BatchSafety RobustMatching
open SourceAlphabet OriginTransport SourceFamilyAdapter SourceAdvancement SourceUniverse
open RepairIntervals RepairGroups RepairProgram CyclicRepairSchedule ActualCyclicMatching
open SuperpermutationUpperBound

variable {M k : Nat} {Control Label : Type} [NeZero M] [DecidableEq Label]

theorem construct_repair (hk : 4 ≤ k) (hM : 2 * k ≤ M) (hdiv : k + 1 ∣ M)
    (controls old : List Nat) (hold : 0 < old.length)
    (hA : (controls ++ old).Nodup) (hsatellite : 9 ∉ controls ++ old)
    (background : Fin M → Nat) (embed : Control → Nat)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (hdisjoint : ∀ c i, embed c ≠ background i)
    (hsupport : ∀ a, a ∈ controls ++ old ↔ (∃ i, background i = a) ∨ ∃ c, embed c = a)
    (hcontrols : ∀ c, embed c ∈ controls)
    (hprojection : CyclicEq old (((List.finRange M).map background).filter (fun a => decide (a ∉ controls))))
    (assignment : Role k ≃ Control) (q : Fin k → Fin M)
    (hmono : StrictMono q) (hrobust : Robust (fun i => cutValue (q i)))
    (hzero : q ⟨0, by omega⟩ = 0)
    (events : Finset (ZMod M × Label))
    (hroom : (2 * (2 * (k + 1) + 1) + 1) * events.card < M)
    (hseparated : Separated events (2 * (k + 1) + 1))
    (phase : Label → Nat) (hphase : ∀ label, phase label < k + 1) (choice : Label → Bool) :
    ∃ cut : ZMod M, ∃ groups : List (EventGroup (2 * (k + 1) + 1) Label),
      (groups.flatMap EventGroup.events).Perm (liftedEvents events cut) ∧
      groups.Pairwise Before ∧
      (∀ G ∈ groups, 2 * (k + 1) + 1 < G.first ∧ G.last + (2 * (k + 1) + 1) < M) ∧
      ∃ C : SourceContour (controls ++ old) (M + k - 1), ∃ gap sweeps finalGap,
        Trace (show 0 < M by omega) (shiftedBackground background (translationCut cut))
          (FiniteProgram.word k (compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups))
          (engineLabels embed assignment) (fun rank => q rank.rev) gap sweeps finalGap ∧
        C.rows = scheduleRows 9 sweeps
          (renderedBase (shiftedBackground background (translationCut cut)) (engineLabels embed assignment)
            (fun rank => q rank.rev) gap) ∧
        scheduleEnd sweeps (renderedBase (shiftedBackground background (translationCut cut))
          (engineLabels embed assignment) (fun rank => q rank.rev) gap) =
            renderedBase (shiftedBackground background (translationCut cut)) (engineLabels embed assignment)
              (fun rank => q rank.rev) gap ∧
        C.rows.Pairwise (fun first last => ¬ first.base.IsRotated last.base) ∧
        (∀ row ∈ C.rows, LiteralEnvelope.Envelope background (engineLabels embed assignment)
          (fun rank => q rank.rev) row.base) ∧
        (∀ row ∈ C.rows, InsertionAbove controls old row.base) ∧
        (C.rows.map Row.charge).sum = 2 * M * k ∧
        portGcd C.rows (M + k - 1) ≤ k := by
  classical
  obtain ⟨cut, groups, hgroups, hbefore, hbounds, hbatch, hnormal, hchanged, lastPre, hlast⟩ :=
    exists_repair_program events (k + 1) (by omega) hroom hseparated phase hphase choice
  let program := compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups
  have hnormalDiv : k + 1 ∣ normalCount program := by
    apply Nat.dvd_of_mod_eq_zero
    change normalCount (compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups) % (k + 1) = 0
    rw [hnormal, Nat.mod_eq_zero_of_dvd hdiv]
  obtain ⟨firstTail, hfirst⟩ := FiniteProgram.compile_starts_normal (k + 1) M (by omega) (by omega)
    (fun G => phase G.label) (fun G => choice G.label) groups
    (fun G _ => hphase G.label) (fun G hG => by have := (hbounds G hG).1; omega)
  obtain ⟨C, gap, sweeps, finalGap, htrace, hrows, hclosed, hsimple, henvelope, hinsertion, hcharge, hgcd⟩ :=
    LocalSourceContour.construct_program hk hM controls old hold hA hsatellite background embed
      hbackground hembed hdisjoint hsupport hcontrols hprojection assignment q hmono hrobust hzero
      (translationCut cut) program hbatch hnormalDiv firstTail lastPre hfirst hlast
  exact ⟨cut, groups, hgroups, hbefore, hbounds, C, gap, sweeps, finalGap,
    htrace, hrows, hclosed, hsimple, henvelope, hinsertion, hcharge, hgcd⟩

end CoefficientTwoPrecision.RepairedSourceContour

#print axioms CoefficientTwoPrecision.RepairedSourceContour.construct_repair
