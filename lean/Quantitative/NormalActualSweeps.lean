import Quantitative.NormalSweepLocal
import Quantitative.NormalTraceHeads
import Quantitative.TraceLocalSimplicity

/-!
# Exact sweep lengths in the actual normal trace

This module identifies every entry of the constructed sweep list. It uses
the actual prefix trace to obtain its resident head and target suffix,
reindexes the literal renderer into physical order, and applies the exact
local sweep calculation. The only initial row hypotheses are its ordinary
nodup and length properties and its specified resident head.
-/

namespace CoefficientTwoPrecision.NormalActualSweeps

open PositiveParking LiteralState StationaryCircle LiteralSchedule PositiveSchedule
open TargetTrace TraceSteps TraceLocalSimplicity RobustMatching BatchSafety
open PhasedControlOrder NormalCuts NormalPrefixes NormalTraceHeads ActualCyclicMatching

variable {M k : Nat} {α : Type} [NeZero M]

def normalCost (q : Fin k → Fin M) (rank : Fin k) : Nat :=
  if h : rank.val = 0 then (q rank.rev).val + k + 1
  else M + k + (q rank.rev).val - (q (⟨rank.val - 1, by omega⟩ : Fin k).rev).val

theorem actual_sweep [DecidableEq α] (hM : 2 ≤ M) (hk : 0 < k)
    (q : Fin k → Fin M) (hmono : StrictMono q)
    (hrobust : Robust (fun i => cutValue (q i))) (hzero : q ⟨0, hk⟩ = 0)
    (background : Fin M → α) (total : Nat) (labels : Option Nat → α)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background (repeatWord total (List.finRange k))
      labels (fun rank => q rank.rev) gap sweeps finalGap)
    (hnodup : (renderedBase background labels (fun rank => q rank.rev) gap).Nodup)
    (hlen : (renderedBase background labels (fun rank => q rank.rev) gap).length = M + k + 1)
    (hhead : ((render background (residents labels) (fun rank => q rank.rev)).rotateLeft gap).head? =
      some (residents (k := k) labels ⟨k - 1, by omega⟩))
    (n : Nat) (hn : n < total * k) :
    movesAt sweeps n = normalCost q ⟨n % k, Nat.mod_lt n hk⟩ := by
  let word := repeatWord total (List.finRange k)
  let initial := renderedBase background labels (fun rank => q rank.rev) gap
  let currentLabels := executeLabels (word.take n) labels
  let currentCuts := executeCuts (show 0 < M by omega) (word.take n) (fun rank => q rank.rev)
  let physicalResident : Fin k → α := fun i => residents currentLabels i.rev
  let current := phased hM q hrobust ⟨0, hk⟩ hzero (normalPhase (n % k))
  let translation := translationCut ((n / k : Nat) : ZMod M)
  have hnword : n < word.length := by
    simpa only [word, length_repeatWord, List.length_finRange] using hn
  have hphysical : (fun i => currentCuts i.rev) = fun i => current i + translation :=
    normal_cuts_physical hM hk total n hn q hrobust ⟨0, hk⟩ hzero
  have hcurrentMono : StrictMono current :=
    phased_strictMono hM q hmono hrobust ⟨0, hk⟩ hzero _
  have hphysicalInj : Function.Injective (fun i : Fin k => currentCuts i.rev) := by
    rw [hphysical]
    intro i j hij
    exact hcurrentMono.injective (add_right_cancel hij)
  have hcutsInj : Function.Injective currentCuts := by
    intro i j hij
    have hrev : i.rev = j.rev := hphysicalInj (by simpa only [Fin.rev_rev] using hij)
    exact Fin.rev_injective hrev
  have hrender := RendererReindex.render_reindex background (residents currentLabels)
    currentCuts hcutsInj Fin.revPerm
  change render background physicalResident (fun i => currentCuts i.rev) =
    render background (residents currentLabels) currentCuts at hrender
  rw [hphysical] at hrender
  obtain ⟨middleGap, pre, hbase, hmoves, hsuffix⟩ :=
    trace_step (show 0 < M by omega) background word labels (fun rank => q rank.rev)
      gap sweeps finalGap n htrace hnword
  change baseAt sweeps initial n =
    (render background (residents currentLabels) currentCuts).rotateLeft middleGap ++
      [currentLabels none] at hbase
  change movesAt sweeps n < (render background (residents currentLabels) currentCuts).length at hmoves
  rw [← hrender] at hbase hmoves
  have hperm := baseAt_perm hM background word labels (fun rank => q rank.rev) gap sweeps finalGap n htrace
  have hndBase := hperm.nodup_iff.mpr hnodup
  have hbaseLength := hperm.length_eq.trans hlen
  change (baseAt sweeps initial n).Nodup at hndBase
  change (baseAt sweeps initial n).length = M + k + 1 at hbaseLength
  rw [hbase] at hndBase hbaseLength
  have hnd : (render background physicalResident (fun i => current i + translation)).Nodup := by
    have h := (List.nodup_append.mp hndBase).1
    rw [LiteralState.rotateLeft_eq_rotate] at h
    exact List.nodup_rotate.mp h
  have hlength : (render background physicalResident (fun i => current i + translation)).length = M + k := by
    simp only [List.length_append, List.length_singleton,
      LiteralState.rotateLeft_eq_rotate, List.length_rotate] at hbaseLength
    omega
  rw [hlength] at hmoves
  have hcurrentHead := normal_base_head (show 0 < M by omega) hk background total labels
    (fun rank => q rank.rev) gap sweeps finalGap n htrace hn.le hhead
  change (baseAt sweeps initial n).dropLast.head? =
    some (residents currentLabels (precedingRank hk n)) at hcurrentHead
  rw [hbase, List.dropLast_concat] at hcurrentHead
  have htargetOpt := normal_target_at_index hk total n hn
  change word[n]? = _ at htargetOpt
  rw [List.getElem?_eq_getElem hnword] at htargetOpt
  have htarget := Option.some.inj htargetOpt
  change fullIterate (movesAt sweeps n) (baseAt sweeps initial n) =
    pre ++ [residents currentLabels word[n], background (currentCuts word[n]), currentLabels none] at hsuffix
  rw [hbase, htarget] at hsuffix
  have htargetCut := congrFun hphysical (⟨n % k, Nat.mod_lt n hk⟩ : Fin k).rev
  simp only [Fin.rev_rev] at htargetCut
  rw [htargetCut] at hsuffix
  have hsuffixPhysical : fullIterate (movesAt sweeps n)
      ((render background physicalResident (fun i => current i + translation)).rotateLeft middleGap ++
        [currentLabels none]) =
      pre ++ [physicalResident (⟨n % k, Nat.mod_lt n hk⟩ : Fin k).rev,
        background (current (⟨n % k, Nat.mod_lt n hk⟩ : Fin k).rev + translation), currentLabels none] := by
    simpa only [physicalResident, Fin.rev_rev] using hsuffix
  by_cases hboundary : n % k = 0
  · have hcurrent : current = q := by
      funext i
      apply Fin.ext
      simp [current, phased, normalPhase, hboundary, phaseNat]
    have hzeroRev : (⟨0, hk⟩ : Fin k).rev = ⟨k - 1, by omega⟩ := by
      apply Fin.ext
      simp [Fin.val_rev]
    have hfirstHead : ((render background physicalResident (fun i => q i + translation)).rotateLeft middleGap).head? =
        some (physicalResident ⟨0, hk⟩) := by
      simpa only [hcurrent, precedingRank, hboundary, ↓reduceIte, physicalResident, hzeroRev] using hcurrentHead
    have hfirstSuffix : fullIterate (movesAt sweeps n)
        ((render background physicalResident (fun i => q i + translation)).rotateLeft middleGap ++ [currentLabels none]) =
        pre ++ [physicalResident (⟨0, hk⟩ : Fin k).rev,
          background (q (⟨0, hk⟩ : Fin k).rev + translation), currentLabels none] := by
      simpa only [hcurrent, hboundary] using hsuffixPhysical
    have h := NormalSweepLocal.first_sweep hM hk q hmono hrobust hzero background
      physicalResident translation (by simpa only [hcurrent] using hnd)
      (by simpa only [hcurrent] using hlength) (currentLabels none) middleGap (movesAt sweeps n) pre
      hmoves hfirstHead hfirstSuffix
    simpa only [normalCost, Fin.val_mk, hboundary, dite_true] using h
  · have hpreviousHead :
        ((render background physicalResident (fun i => current i + translation)).rotateLeft middleGap).head? =
          some (physicalResident (⟨n % k - 1, by have := Nat.mod_lt n hk; omega⟩ : Fin k).rev) := by
      simpa only [precedingRank, if_neg hboundary, physicalResident, Fin.rev_rev] using hcurrentHead
    have h := NormalSweepLocal.later_sweep hM hk q hmono hrobust hzero
      (n % k) (Nat.mod_lt n hk) (by omega) background physicalResident translation hnd hlength
      (currentLabels none) middleGap (movesAt sweeps n) pre hmoves hpreviousHead hsuffixPhysical
    simp only [normalCost, Fin.val_mk, dif_neg hboundary]
    omega

end CoefficientTwoPrecision.NormalActualSweeps

#print axioms CoefficientTwoPrecision.NormalActualSweeps.actual_sweep
