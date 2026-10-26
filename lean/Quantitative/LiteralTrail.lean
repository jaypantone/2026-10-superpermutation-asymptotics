import Quantitative.LiteralSchedule
import SuperpermutationUpperBound.Transport.OrbitAssembly

/-!
# From actual local updates to a literal closed trail

`SuffixSchedule` says exactly that each chosen full sweep reaches a
three-symbol update suffix. It is a predicate on the concrete recursively
computed bases, not an axiom or an existence assertion. We prove that such
a schedule gives an actual compatible row trail, and that equality of the
final and initial literal bases closes it. The geometric normal/parking
schedules must still supply these explicit hypotheses.
-/

namespace CoefficientTwoPrecision.LiteralTrail

open JointStates LiteralState LiteralSchedule
open SuperpermutationUpperBound SuperpermutationUpperBound.Transport

variable {α : Type}

theorem fullIterate_shift (base : List α) (moves : Nat) :
    fullIterate (moves + 1) base = fullIterate moves (literalFullStep base) := by
  induction moves with
  | zero => rfl
  | succ moves ih =>
    change literalFullStep (fullIterate (moves + 1) base) =
      literalFullStep (fullIterate moves (literalFullStep base))
    rw [ih]

theorem updateRows_zero (satellite : α) (base : List α) :
    updateRows satellite 0 base = [shortRow base satellite] := by
  simp [updateRows, fullIterate]

theorem updateRows_succ (satellite : α) (base : List α) (moves : Nat) :
    updateRows satellite (moves + 1) base =
      fullRow base satellite :: updateRows satellite moves (literalFullStep base) := by
  simp only [updateRows, List.range_succ_eq_map, List.map_cons, List.map_map,
    List.cons_append, Function.comp_def, fullIterate_shift,
    show fullIterate 0 base = base from rfl]

theorem updateRows_first_base (satellite : α) (base : List α) (moves : Nat) :
    ∃ first rest, updateRows satellite moves base = first :: rest ∧ first.base = base := by
  cases moves with
  | zero => exact ⟨shortRow base satellite, [], updateRows_zero _ _, rfl⟩
  | succ moves => exact ⟨fullRow base satellite,
      updateRows satellite moves (literalFullStep base), updateRows_succ _ _ _, rfl⟩

/-- One valid update gives an actual row path ending at any row with the
correct final base. The final row's visible length does not affect its head. -/
theorem updateRows_runsTo (satellite : α) (stationary : List α) (mobile : α)
    (moves : Nat) (hlen : 1 ≤ stationary.length)
    (hsuffix : ∃ pre resident crossed token,
      fullIterate moves (stationary ++ [mobile]) = pre ++ [resident, crossed, token])
    (last : Row α) (hlast : last.base = updateEnd moves (stationary ++ [mobile])) :
    PathRunsTo (updateRows satellite moves (stationary ++ [mobile])) last := by
  induction moves generalizing stationary mobile with
  | zero =>
    rw [updateRows_zero]
    obtain ⟨pre, resident, crossed, token, hbase⟩ := hsuffix
    change stationary ++ [mobile] = pre ++ [resident, crossed, token] at hbase
    change (shortRow (stationary ++ [mobile]) satellite).Compatible last ∧ True
    refine ⟨?_, True.intro⟩
    rw [hbase]
    have hc := shortRow_compatible pre resident crossed token satellite last.visible
    unfold Row.Compatible Row.head at hc ⊢
    simpa only [hlast, updateEnd, fullIterate, hbase] using hc
  | succ moves ih =>
    rw [updateRows_succ, literalFullStep_mobile_last]
    have hrotlen : (stationary.rotateLeft 1).length = stationary.length := by
      rw [LiteralState.rotateLeft_eq_rotate, List.length_rotate]
    have hsuffix' : ∃ pre resident crossed token,
        fullIterate moves (stationary.rotateLeft 1 ++ [mobile]) =
          pre ++ [resident, crossed, token] := by
      simpa only [fullIterate_shift, literalFullStep_mobile_last] using hsuffix
    have hlast' : last.base = updateEnd moves (stationary.rotateLeft 1 ++ [mobile]) := by
      simpa only [updateEnd, fullIterate_shift, literalFullStep_mobile_last] using hlast
    have htail := ih (stationary.rotateLeft 1) mobile (by omega) hsuffix' hlast'
    obtain ⟨first, rest, hrows, hfirst⟩ :=
      updateRows_first_base satellite (stationary.rotateLeft 1 ++ [mobile]) moves
    rw [hrows] at htail ⊢
    change (fullRow (stationary ++ [mobile]) satellite).Compatible first ∧
      RowTrailCompatible first (rest ++ [last])
    refine ⟨?_, htail⟩
    have hc := fullRow_compatible stationary mobile satellite first.visible hlen
    unfold Row.Compatible Row.head at hc ⊢
    simpa only [literalFullStep_mobile_last, hfirst] using hc

/-- A concrete recursive condition on the suffix reached at every update. -/
def SuffixSchedule : List Nat → List α → Prop
  | [], _ => True
  | moves :: rest, base =>
      (∃ stationary mobile, base = stationary ++ [mobile] ∧ 1 ≤ stationary.length) ∧
      (∃ pre resident crossed token, fullIterate moves base = pre ++ [resident, crossed, token]) ∧
      SuffixSchedule rest (updateEnd moves base)

theorem scheduleRows_first_base (satellite : α) (sweeps : List Nat) (base : List α)
    (hne : sweeps ≠ []) :
    ∃ first rest, scheduleRows satellite sweeps base = first :: rest ∧ first.base = base := by
  cases sweeps with
  | nil => exact False.elim (hne rfl)
  | cons moves sweeps =>
    obtain ⟨first, rest, hrows, hbase⟩ := updateRows_first_base satellite base moves
    exact ⟨first, rest ++ scheduleRows satellite sweeps (updateEnd moves base),
      by simp only [scheduleRows, hrows, List.cons_append], hbase⟩

theorem scheduleRows_runsTo (satellite : α) (sweeps : List Nat) (base : List α)
    (hne : sweeps ≠ []) (hvalid : SuffixSchedule sweeps base)
    (last : Row α) (hlast : last.base = scheduleEnd sweeps base) :
    PathRunsTo (scheduleRows satellite sweeps base) last := by
  induction sweeps generalizing base with
  | nil => exact False.elim (hne rfl)
  | cons moves sweeps ih =>
    obtain ⟨⟨stationary, mobile, hbase, hlen⟩, hsuffix, hrest⟩ := hvalid
    cases sweeps with
    | nil =>
      simp only [scheduleRows, List.append_nil]
      rw [hbase]
      apply updateRows_runsTo satellite stationary mobile moves hlen
      · simpa only [hbase] using hsuffix
      · simpa only [scheduleEnd, hbase] using hlast
    | cons next tail =>
      obtain ⟨first, rest, hrows, hfirst⟩ := scheduleRows_first_base satellite (next :: tail)
        (updateEnd moves base) (by simp)
      have hfirstPath : PathRunsTo (updateRows satellite moves base) first := by
        rw [hbase]
        apply updateRows_runsTo satellite stationary mobile moves hlen
        · simpa only [hbase] using hsuffix
        · simpa only [hbase] using hfirst
      have hrestPath := ih (updateEnd moves base) (by simp) hrest hlast
      rw [hrows] at hrestPath
      change PathRunsTo (updateRows satellite moves base ++
        scheduleRows satellite (next :: tail) (updateEnd moves base)) last
      rw [hrows]
      exact pathRunsTo_append hfirstPath hrestPath

/-- Exact literal endpoint equality closes the constructed occurrence list. -/
theorem scheduleRows_closed (satellite : α) (sweeps : List Nat) (base : List α)
    (hne : sweeps ≠ []) (hvalid : SuffixSchedule sweeps base)
    (hclosed : scheduleEnd sweeps base = base) :
    ClosedTrail (scheduleRows satellite sweeps base) := by
  obtain ⟨first, rest, hrows, hfirst⟩ := scheduleRows_first_base satellite sweeps base hne
  have hpath := scheduleRows_runsTo satellite sweeps base hne hvalid first (hfirst.trans hclosed.symm)
  rw [hrows] at hpath ⊢
  exact closedTrail_of_pathRunsTo hpath

end CoefficientTwoPrecision.LiteralTrail

#print axioms CoefficientTwoPrecision.LiteralTrail.updateRows_runsTo
#print axioms CoefficientTwoPrecision.LiteralTrail.scheduleRows_runsTo
#print axioms CoefficientTwoPrecision.LiteralTrail.scheduleRows_closed
