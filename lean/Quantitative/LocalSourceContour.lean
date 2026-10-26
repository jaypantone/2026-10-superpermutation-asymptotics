import Quantitative.FiniteProgram
import Quantitative.SourceAlphabet
import Quantitative.ConnectorGrid
import Quantitative.OriginTransport
import Quantitative.SourceGeometry
import Quantitative.GlobalSimplicity
import Quantitative.RobustReindex

/-!
# A concrete local source contour from the actual finite repair program

The input specifies alphabets, a robust frame, a finite role assignment,
and the syntactic program facts supplied by the repair compiler. The
bounded trace, literal closure, source validity, insertion membership,
source-class distinctness, envelope containment, monodromy bound and
connector grid are all constructed here on the same actual row list.

The safe-cut origin is retained. Construction uses the shifted background,
while the output envelope is expressed in the fixed canonical background.
-/

namespace CoefficientTwoPrecision.LocalSourceContour

open PositiveParking LiteralState StationaryCircle StationaryUpdate LiteralSchedule PositiveSchedule
open TargetTrace ClosedTrace MacroCatalogue FiniteRoles BatchSafety RobustMatching
open SourceAlphabet OriginTransport SourceFamilyAdapter SourceAdvancement SourceUniverse
open SuperpermutationUpperBound

variable {M k : Nat} {Control : Type} [NeZero M]

theorem construct_program (hk : 4 ≤ k) (hM : 2 * k ≤ M)
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
    (hzero : q ⟨0, by omega⟩ = 0) (origin : Fin M)
    (program : List Macro) (hbatch : batchCount program = M)
    (hrole : k + 1 ∣ normalCount program)
    (firstTail lastPre : List Macro) (hfirst : program = .normal :: firstTail)
    (hlast : program = lastPre ++ [.normal]) :
    ∃ C : SourceContour (controls ++ old) (M + k - 1), ∃ gap sweeps finalGap,
      Trace (show 0 < M by omega) (shiftedBackground background origin) (FiniteProgram.word k program)
        (engineLabels embed assignment) (fun rank => q rank.rev) gap sweeps finalGap ∧
      C.rows = scheduleRows 9 sweeps
        (renderedBase (shiftedBackground background origin) (engineLabels embed assignment)
          (fun rank => q rank.rev) gap) ∧
      scheduleEnd sweeps (renderedBase (shiftedBackground background origin) (engineLabels embed assignment)
        (fun rank => q rank.rev) gap) =
          renderedBase (shiftedBackground background origin) (engineLabels embed assignment)
            (fun rank => q rank.rev) gap ∧
      C.rows.Pairwise (fun first last => ¬ first.base.IsRotated last.base) ∧
      (∀ row ∈ C.rows, LiteralEnvelope.Envelope background (engineLabels embed assignment)
        (fun rank => q rank.rev) row.base) ∧
      (∀ row ∈ C.rows, InsertionAbove controls old row.base) ∧
      (C.rows.map Row.charge).sum = 2 * M * k ∧
      portGcd C.rows (M + k - 1) ≤ k := by
  classical
  let localBackground := shiftedBackground background origin
  let labels := engineLabels embed assignment
  let cuts : Fin k → Fin M := fun rank => q rank.rev
  let orders := FiniteProgram.batches k program
  let targetWord := FiniteProgram.word k program
  have hMtwo : 2 ≤ M := by omega
  have hMthree : 3 ≤ M := by omega
  have hkpos : 0 < k := by omega
  have hlocalInjective : Function.Injective localBackground := shifted_injective background hbackground origin
  have hlocalDisjoint : ∀ c i, embed c ≠ localBackground i := fun c i => hdisjoint c (i + origin)
  have hlocalSupport : ∀ a, a ∈ controls ++ old ↔
      (∃ i, localBackground i = a) ∨ ∃ c, embed c = a := by
    intro a
    rw [hsupport a]
    change _ ↔ (∃ i, shiftedBackground background origin i = a) ∨ _
    rw [shifted_range]
  have hresident : Function.Injective (residents (k := k) labels) :=
    SourceAlphabet.residents_injective embed hembed assignment
  have hcross : ∀ (j : Fin k) (i : Fin M), residents labels j ≠ localBackground i :=
    SourceAlphabet.residents_disjoint localBackground embed hlocalDisjoint assignment
  have hrobustCuts : Robust (fun j => cutValue (cuts j)) := by
    simpa only [cuts, Function.comp_def, Fin.revPerm_apply] using
      RobustReindex.robust_reindex Fin.revPerm (fun i => cutValue (q i)) hrobust
  have horders : ∀ order ∈ orders, order.Perm (List.finRange k) := FiniteProgram.batches_orders k program
  have hnumber : orders.length = M := (FiniteProgram.batches_length k program).trans hbatch
  have hcounts : ∀ target, targetWord.count target = M := by
    intro target
    exact (FiniteProgram.word_count k program target).trans hbatch
  have hlabels : executeLabels targetWord labels = labels :=
    FiniteProgram.program_labels_return k program hrole labels
  let lastTarget : Fin k := ⟨k - 1, by omega⟩
  have hlastTarget : targetWord.getLast? = some lastTarget := by
    dsimp only [targetWord]
    rw [hlast]
    exact FiniteProgram.word_last_normal k hkpos lastPre
  obtain ⟨gap, sweeps, finalGap, htrace, hclosed, htrail, henvelope⟩ :=
    closed_trace_envelope hMtwo localBackground labels cuts hlocalInjective hresident hcross hrobustCuts
      orders horders hcounts hlabels lastTarget hlastTarget program (FiniteProgram.word_map k program) 9
  let initial := renderedBase localBackground labels cuts gap
  let rows := scheduleRows 9 sweeps initial
  have hnd : initial.Nodup :=
    SourceAlphabet.base_nodup localBackground embed hlocalInjective hembed hlocalDisjoint assignment cuts gap
  have hlength : initial.length = M + k + 1 :=
    SourceAlphabet.base_length localBackground embed hlocalInjective hembed hlocalDisjoint assignment cuts gap
  have hstationary : (render localBackground (residents labels) cuts).length = M + k :=
    render_length localBackground (residents labels) cuts hlocalInjective hresident hcross
  have hbased : BasedOn (controls ++ old) 9 rows :=
    SourceAlphabet.schedule_basedOn hMtwo (controls ++ old) hA hsatellite localBackground embed
      hlocalInjective hembed hlocalDisjoint hlocalSupport assignment targetWord cuts gap sweeps finalGap htrace
  have hcutReturn := executeCuts_closed (show 0 < M by omega) targetWord cuts hcounts
  have hlastHead := trace_last_head (show 0 < M by omega) localBackground targetWord labels cuts
    gap sweeps finalGap htrace lastTarget hlastTarget
  rw [hlabels, hcutReturn] at hlastHead
  have hendpoint := trace_endpoint (show 0 < M by omega) localBackground targetWord labels cuts
    gap sweeps finalGap htrace
  have hbaseEq : renderedBase localBackground labels cuts finalGap = renderedBase localBackground labels cuts gap := by
    simpa only [hlabels, hcutReturn] using hendpoint.symm.trans hclosed
  have hhead : ((render localBackground (residents labels) cuts).rotateLeft gap).head? =
      some (residents labels lastTarget) := by
    have heq := congrArg (fun base : List Nat => base.dropLast.head?) hbaseEq
    simp only [renderedBase, List.dropLast_concat] at heq
    exact heq.symm.trans hlastHead
  have hfirstWord : targetWord = List.finRange k ++ FiniteProgram.word k firstTail := by
    dsimp only [targetWord]
    rw [hfirst, FiniteProgram.word_first_normal]
  obtain ⟨H, mobile, start, R, hHlength, hHnd, hRpos, hRbound, haverage, hrun⟩ :=
    InitialNormalRun.initial_normal_run hMtwo hkpos q hmono hrobust hzero localBackground labels
      targetWord (FiniteProgram.word k firstTail) hfirstWord gap sweeps finalGap htrace hnd hlength hhead 9
  have hport : M + k - 1 + 1 = M + k := by omega
  have havoid : TraceDisplacement.Avoids (k := k) labels (localBackground ⟨0, by omega⟩) :=
    ⟨hlocalDisjoint (assignment none) _, fun j => hcross j _⟩
  have hgcd : portGcd rows (M + k - 1) ≤ k :=
    ActualMonodromy.actual_portGcd_le hMtwo hkpos (M + k - 1) localBackground hlocalInjective
      ⟨0, by omega⟩ targetWord labels cuts gap sweeps finalGap htrace
      (by rw [hport]; exact hstationary) hnd havoid hcounts hclosed 9
  have hgrid := ConnectorGrid.grid_choice M k R (portGcd rows (M + k - 1)) hk hM haverage
    (portGcd_pos rows (M + k - 1)) hgcd
  let C : SourceContour (controls ++ old) (M + k - 1) :=
    SourceContour.of_run (controls ++ old) (M + k - 1) rows htrail hbased H mobile start R
      (R / portGcd rows (M + k - 1)) (by rw [hport]; exact hHlength) hrun hgrid.1 hgrid.2.1
      (by rw [hport]; exact hRbound.le) (by rw [hport]; exact hgrid.2.2)
  have hrowEq : C.rows = rows := rfl
  let backgroundTest : Nat → Bool := fun a => decide (∃ i, background i = a)
  have htestBackground : ∀ i, backgroundTest (localBackground i) = true := by
    intro i
    change decide (∃ j, background j = background (i + origin)) = true
    simp only [decide_eq_true_eq]
    exact ⟨i + origin, rfl⟩
  have htestControl : ∀ c, backgroundTest (embed c) = false := by
    intro c
    change decide (∃ i, background i = embed c) = false
    simp only [decide_eq_false_iff_not]
    rintro ⟨i, hi⟩
    exact hdisjoint c i hi.symm
  have hsimple : rows.Pairwise (fun first last => ¬ first.base.IsRotated last.base) :=
    GlobalSimplicity.scheduleRows_pairwise hMthree (by omega) backgroundTest localBackground embed
      hlocalInjective hembed htestBackground htestControl assignment cuts hrobustCuts orders horders hnumber
      gap sweeps finalGap htrace hlabels hclosed 9
  have hlocalProjection : CyclicEq old
      (((List.finRange M).map localBackground).filter (fun a => decide (a ∉ controls))) := by
    have hbgne : (List.finRange M).map background ≠ [] := by
      intro heq
      have hl := congrArg List.length heq
      simp only [List.length_map, List.length_finRange, List.length_nil] at hl
      omega
    have hfilteredne : (((List.finRange M).map background).filter (fun a => decide (a ∉ controls))) ≠ [] := by
      intro heq
      have hl := hprojection.length_eq
      rw [heq, List.length_nil] at hl
      omega
    have hrot := (CyclicEq.of_rot hbgne origin.val).filter (fun a => decide (a ∉ controls)) hfilteredne
    rw [← shifted_list background origin] at hrot
    exact hprojection.trans hrot
  have hwordLength : targetWord.length = M * k := by
    change orders.flatten.length = _
    rw [BatchTime.batches_length orders horders, hnumber]
  have hsweepsLength : sweeps.length = M * k :=
    (trace_length (show 0 < M by omega) localBackground targetWord labels cuts gap sweeps finalGap htrace).trans hwordLength
  have hcharge : (rows.map Row.charge).sum = 2 * M * k := by
    rw [RowValidity.scheduleRows_charge 9 sweeps initial
      (trace_suffixSchedule hMtwo localBackground targetWord labels cuts gap sweeps finalGap htrace)
      (by rw [hlength]; omega), hsweepsLength]
    ring
  refine ⟨C, gap, sweeps, finalGap, htrace, hrowEq, hclosed, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hrowEq] using hsimple
  · intro row hrow
    rw [hrowEq] at hrow
    exact envelope_canonical background origin labels cuts row.base (henvelope row hrow)
  · intro row hrow
    rw [hrowEq] at hrow
    exact SourceAlphabet.schedule_insertion hMtwo controls old hold hA localBackground embed hlocalInjective
      hembed hlocalDisjoint hlocalSupport hcontrols hlocalProjection assignment targetWord cuts gap sweeps finalGap
      htrace row hrow
  · simpa only [hrowEq] using hcharge
  · simpa only [hrowEq] using hgcd

end CoefficientTwoPrecision.LocalSourceContour

#print axioms CoefficientTwoPrecision.LocalSourceContour.construct_program
