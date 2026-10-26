import Quantitative.RepairRowCounts
import Quantitative.RepairedSourceContour

/-!
# Exact counts of the actual repaired source contour

The source builder returns one closed bounded trace and its literal row
list. Closure and the final normal batch recover the initial physical-zero
head needed by the perturbation theorem. Thus the row estimate below is
about the same contour that carries source validity, the connector grid,
insertion membership, and cyclic simplicity. There is no independent row
count assumption.
-/

namespace CoefficientTwoPrecision.RepairedContourCounts

open SuperpermutationUpperBound PositiveParking LiteralState StationaryCircle
open LiteralSchedule PositiveSchedule TargetTrace ClosedTrace MacroCatalogue FiniteProgram
open FiniteRoles BatchSafety RobustMatching SourceAlphabet OriginTransport
open SourceFamilyAdapter SourceAdvancement SourceUniverse ActualCyclicMatching
open RepairIntervals RepairGroups RepairProgram CyclicRepairSchedule

variable {M k : Nat} {Control Label : Type} [NeZero M] [DecidableEq Label]

/-- The final retained normal batch and actual closure determine the
initial head. This fact is derived from the compiler and trace, rather
than supplied as a choice of a second trace. -/
theorem closed_compiled_head (hk : 0 < k) (hM : k + 1 ≤ M) (hdiv : k + 1 ∣ M)
    (groups : List (EventGroup (2 * (k + 1) + 1) Label))
    (phase : Label → Nat) (hphase : ∀ label, phase label < k + 1) (choice : Label → Bool)
    (hbefore : groups.Pairwise Before)
    (hbounds : ∀ G ∈ groups, 2 * (k + 1) + 1 < G.first ∧ G.last + (2 * (k + 1) + 1) < M)
    (background : Fin M → Nat) (labels : Option Nat → Nat) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (show 0 < M by omega) background
      (FiniteProgram.word k (compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups))
      labels cuts gap sweeps finalGap)
    (hclosed : scheduleEnd sweeps (renderedBase background labels cuts gap) =
      renderedBase background labels cuts gap) :
    ((render background (residents labels) cuts).rotateLeft gap).head? =
      some (residents (k := k) labels ⟨k - 1, by omega⟩) := by
  let program := compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups
  have hfirst : ∀ G ∈ groups, k + 1 ≤ G.first := by
    intro G hG
    have := (hbounds G hG).1
    omega
  have hfit : ∀ G ∈ groups, groupEnd (k + 1) (fun H => phase H.label) G < M := by
    intro G hG
    obtain ⟨_, _, _, _, hend, _⟩ := rounded_repair_interval (k + 1) (phase G.label) G.first G.last
      (by omega) (hphase G.label) (hbounds G hG).1 G.first_le_last
    exact lt_of_le_of_lt hend (hbounds G hG).2
  obtain ⟨hbatch, hnormal, lastPre, hlast⟩ := constructed_program_counts (k + 1) M
    (fun G => phase G.label) (fun G => choice G.label) groups (by omega) (by omega)
    (fun G _ => hphase G.label) hfirst hfit hbefore
  have hnormalDiv : k + 1 ∣ normalCount program := by
    apply Nat.dvd_of_mod_eq_zero
    change normalCount (compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups) % (k + 1) = 0
    rw [hnormal, Nat.mod_eq_zero_of_dvd hdiv]
  have hlabels : executeLabels (FiniteProgram.word k program) labels = labels :=
    FiniteProgram.program_labels_return k program hnormalDiv labels
  have hcounts : ∀ target, (FiniteProgram.word k program).count target = M := by
    intro target
    exact (FiniteProgram.word_count k program target).trans hbatch
  have hcuts := executeCuts_closed (show 0 < M by omega) (FiniteProgram.word k program) cuts hcounts
  have hlastTarget : (FiniteProgram.word k program).getLast? =
      some (⟨k - 1, by omega⟩ : Fin k) := by
    change (FiniteProgram.word k
      (compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups)).getLast? = _
    rw [hlast]
    exact FiniteProgram.word_last_normal k hk lastPre
  have hlastHead := trace_last_head (show 0 < M by omega) background (FiniteProgram.word k program)
    labels cuts gap sweeps finalGap htrace ⟨k - 1, by omega⟩ hlastTarget
  rw [hlabels, hcuts] at hlastHead
  have hendpoint := trace_endpoint (show 0 < M by omega) background (FiniteProgram.word k program)
    labels cuts gap sweeps finalGap htrace
  have hbaseEq : renderedBase background labels cuts finalGap = renderedBase background labels cuts gap := by
    simpa only [hlabels, hcuts] using hendpoint.symm.trans hclosed
  have heq := congrArg (fun base : List Nat => base.dropLast.head?) hbaseEq
  simp only [renderedBase, List.dropLast_concat] at heq
  exact heq.symm.trans hlastHead

/-- Row error for the literal rows of the actual closed repaired trace.
The background may already have been translated by the safe cyclic cut. -/
theorem closed_row_error (hk : 5 ≤ k) (hM : k + 1 ≤ M) (hdiv : k + 1 ∣ M)
    (K : Nat) (groups : List (EventGroup (2 * (k + 1) + 1) Label))
    (phase : Label → Nat) (hphase : ∀ label, phase label < k + 1) (choice : Label → Bool)
    (hbefore : groups.Pairwise Before)
    (hbounds : ∀ G ∈ groups, 2 * (k + 1) + 1 < G.first ∧ G.last + (2 * (k + 1) + 1) < M)
    (hcount : (groups.flatMap EventGroup.events).length ≤ K)
    (q : Fin k → Fin M) (hmono : StrictMono q)
    (hrobust : Robust (fun i => cutValue (q i))) (hzero : q ⟨0, by omega⟩ = 0)
    (background : Fin M → Nat) (labels : Option Nat → Nat)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (show 0 < M by omega) background
      (FiniteProgram.word k (compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups))
      labels (fun rank => q rank.rev) gap sweeps finalGap)
    (hnd : (renderedBase background labels (fun rank => q rank.rev) gap).Nodup)
    (hlen : (renderedBase background labels (fun rank => q rank.rev) gap).length = M + k + 1)
    (hclosed : scheduleEnd sweeps (renderedBase background labels (fun rank => q rank.rev) gap) =
      renderedBase background labels (fun rank => q rank.rev) gap) :
    |((scheduleRows 9 sweeps (renderedBase background labels (fun rank => q rank.rev) gap)).length : ℚ) -
      ((M * ((k - 1) * M + k * (k + 1) + 1) : Nat) : ℚ)| ≤
      ((10 * (k + 1) ^ 2 * K * M : Nat) : ℚ) := by
  have hhead := closed_compiled_head (by omega : 0 < k) hM hdiv groups phase hphase choice
    hbefore hbounds background labels (fun rank => q rank.rev) gap sweeps finalGap htrace hclosed
  have hfirst : ∀ G ∈ groups, k + 1 ≤ G.first := by
    intro G hG
    have := (hbounds G hG).1
    omega
  have hfit : ∀ G ∈ groups, groupEnd (k + 1) (fun H => phase H.label) G ≤ M := by
    intro G hG
    obtain ⟨_, _, _, _, hend, _⟩ := rounded_repair_interval (k + 1) (phase G.label) G.first G.last
      (by omega) (hphase G.label) (hbounds G hG).1 G.first_le_last
    exact (lt_of_le_of_lt hend (hbounds G hG).2).le
  have ht : Trace (show 0 < M by omega) background
      (FiniteProgram.word k
        (compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups))
      labels (fun rank => q rank.rev + (0 : Fin M)) gap sweeps finalGap := by
    simpa only [add_zero] using htrace
  have hn : (renderedBase background labels (fun rank => q rank.rev + (0 : Fin M)) gap).Nodup := by
    simpa only [add_zero] using hnd
  have hl : (renderedBase background labels (fun rank => q rank.rev + (0 : Fin M)) gap).length =
      M + k + 1 := by simpa only [add_zero] using hlen
  have hh : ((render background (residents labels) (fun rank => q rank.rev + (0 : Fin M))).rotateLeft gap).head? =
      some (residents (k := k) labels ⟨k - 1, by omega⟩) := by
    simpa only [add_zero] using hhead
  have herror := RepairRowCounts.compiled_row_error (M := M) (k := k) (k + 1) M 0 groups
    (by omega) (by omega) hM phase hphase choice hfirst (fun _ _ => Nat.zero_le _) hfit hbefore
    q hmono hrobust hzero background labels 0 gap sweeps finalGap ht hn hl hh 9
  have hc := (changedBatches_bound (k + 1) phase groups (by omega) hphase hfirst).trans
    (Nat.mul_le_mul_left (2 * (2 * (k + 1) + 1)) hcount)
  have hb := RepairRowCounts.perturbation_budget (k + 1) M K
    (changedBatches (k + 1) phase groups) (by omega) hM hc
  have hbQ : ((changedBatches (k + 1) phase groups * RepairRowCounts.batchBound M k : Nat) : ℚ) ≤
      ((10 * (k + 1) ^ 2 * K * M : Nat) : ℚ) := by
    exact_mod_cast (show changedBatches (k + 1) phase groups * RepairRowCounts.batchBound M k ≤
      10 * (k + 1) ^ 2 * K * M by simpa only [Nat.add_sub_cancel] using hb)
  simpa only [Nat.sub_zero, RepairRowCounts.normalRows, add_zero] using herror.trans hbQ

/-- The actual source constructor, with its exact charge, connector bound,
all original row properties, and the proved perturbation estimate. The
same contour and same trace witness every field in the conclusion. -/
theorem construct_counted_repair (hk : 5 ≤ k) (hM : 2 * k ≤ M) (hdiv : k + 1 ∣ M)
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
    (K : Nat) (events : Finset (ZMod M × Label)) (hcount : events.card ≤ K)
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
        portGcd C.rows (M + k - 1) ≤ k ∧
        |(C.rows.length : ℚ) - ((M * ((k - 1) * M + k * (k + 1) + 1) : Nat) : ℚ)| ≤
          ((10 * (k + 1) ^ 2 * K * M : Nat) : ℚ) := by
  classical
  obtain ⟨cut, groups, hgroups, hbefore, hbounds, C, gap, sweeps, finalGap,
      htrace, hrows, hclosed, hsimple, henvelope, hinsertion, hcharge, hgcd⟩ :=
    RepairedSourceContour.construct_repair (by omega : 4 ≤ k) hM hdiv controls old hold hA hsatellite
      background embed hbackground hembed hdisjoint hsupport hcontrols hprojection assignment q hmono hrobust hzero
      events hroom hseparated phase hphase choice
  have hgroupCount : (groups.flatMap EventGroup.events).length ≤ K := by
    rw [hgroups.length_eq, lifted_length]
    exact hcount
  let localBackground := shiftedBackground background (translationCut cut)
  have hlocalInjective : Function.Injective localBackground :=
    shifted_injective background hbackground (translationCut cut)
  have hlocalDisjoint : ∀ c i, embed c ≠ localBackground i :=
    fun c i => hdisjoint c (i + translationCut cut)
  have hnd := SourceAlphabet.base_nodup localBackground embed hlocalInjective hembed hlocalDisjoint
    assignment (fun rank => q rank.rev) gap
  have hlen := SourceAlphabet.base_length localBackground embed hlocalInjective hembed hlocalDisjoint
    assignment (fun rank => q rank.rev) gap
  have herror := closed_row_error hk (by omega : k + 1 ≤ M) hdiv K groups phase hphase choice
    hbefore hbounds hgroupCount q hmono hrobust hzero localBackground (engineLabels embed assignment)
    gap sweeps finalGap htrace hnd hlen hclosed
  refine ⟨cut, groups, hgroups, hbefore, hbounds, C, gap, sweeps, finalGap,
    htrace, hrows, hclosed, hsimple, henvelope, hinsertion, hcharge, hgcd, ?_⟩
  simpa only [hrows] using herror

end CoefficientTwoPrecision.RepairedContourCounts

#print axioms CoefficientTwoPrecision.RepairedContourCounts.closed_compiled_head
#print axioms CoefficientTwoPrecision.RepairedContourCounts.closed_row_error

#print axioms CoefficientTwoPrecision.RepairedContourCounts.construct_counted_repair
