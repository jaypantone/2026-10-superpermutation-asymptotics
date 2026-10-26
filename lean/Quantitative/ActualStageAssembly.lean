import Quantitative.SparseStageIteration
import Quantitative.DenseStageIteration

/-!
# Actual sparse stages, empty padding, and the actual dense tail

The only construction hypothesis is the sparse WidthBlockFamily supplier.
All Stage objects and the terminal numerical trace in this theorem are
constructed here or in the imported iteration modules.
-/

namespace CoefficientTwoPrecision.ActualStageAssembly

open StageState SparseStageIteration

private theorem schedule_endpoints (n r : ℕ) (hr : 6 ≤ r)
    (hn : transferConstant * r ^ 61 ≤ n) :
    sparseEnd n r (sourceWidth r) ≤ tailStart n ∧
      tailStart n + 3 * denseBlocks n = n - 3 := by
  have hs := source_schedule_valid n r hr hn
  have hroom := (construction_threshold_conditions r n hr hn).2.2
  have h := schedule_bounds n r (sourceWidth r) hr hs.1 hs.2.1
    (sourceWidth_dvd r) hroom
  exact ⟨h.2.2.1, h.2.2.2.2.1⟩

/-- Construct the actual final Stage and prove the complete normalized
cost bound. SparseFamilyConstruction supplies the geometric premise. -/
theorem final_stage (n r : ℕ) (hr : 6 ≤ r)
    (hn : transferConstant * r ^ 61 ≤ n) (supplier : SparseFamilySupplier r) :
    ∃ F : BuiltStage (n - 3),
      (n : ℚ) * F.X + (n : ℚ) * F.zmass + 2 * (n : ℚ) * F.p ≤ 2 + 74 / (r : ℚ) := by
  let D := sourceData n r hr hn supplier
  let J := sparseBlocks n r (sourceWidth r)
  let S := SparseStageIteration.stages n r hr hn supplier J
  obtain ⟨hsp, hsX, hsz⟩ := stage_values n r hr hn supplier J le_rfl
  have hsp' : S.p = pending D.density J := hsp
  have hsX' : S.X = accumulatedCost D.density D.totalRate J := hsX
  have hsz' : S.zmass = accumulatedCost D.density D.circleRate J := hsz
  obtain ⟨hend, hlast⟩ := schedule_endpoints n r hr hn
  obtain ⟨P0, hpp, hpX, hpz⟩ := empty_to S (tailStart n - sparseEnd n r (sourceWidth r))
  have hpad : sparseStart n r (sourceWidth r) J +
      (tailStart n - sparseEnd n r (sourceWidth r)) = tailStart n := by
    change sparseEnd n r (sourceWidth r) +
      (tailStart n - sparseEnd n r (sourceWidth r)) = tailStart n
    omega
  let P := P0.reindex hpad
  have hp : P.p = pending D.density J := by
    simpa only [P, BuiltStage.reindex_p] using hpp.trans hsp'
  have hX : P.X = accumulatedCost D.density D.totalRate J := by
    simpa only [P, BuiltStage.reindex_X] using hpX.trans hsX'
  have hz : P.zmass = accumulatedCost D.density D.circleRate J := by
    simpa only [P, BuiltStage.reindex_zmass] using hpz.trans hsz'
  have hb : 49 ≤ tailStart n := (source_schedule_valid n r hr hn).2.2.2.2.1
  let T := DenseStageIteration.trace n P hb (pending D.density J) hp
  let F := (DenseStageIteration.stages P hb (denseBlocks n)).reindex hlast
  have hbound := scheduled_numerical_bound n r hr hn D T
  refine ⟨F, ?_⟩
  have heq : (n : ℚ) * F.X + (n : ℚ) * F.zmass + 2 * (n : ℚ) * F.p =
      (n : ℚ) * accumulatedCost D.density D.totalRate J + (n : ℚ) * T.X (denseBlocks n) +
        ((n : ℚ) * (accumulatedCost D.density D.circleRate J + T.z (denseBlocks n)) +
          2 * (n : ℚ) * T.p (denseBlocks n)) := by
    simp only [F, BuiltStage.reindex_X, BuiltStage.reindex_zmass, BuiltStage.reindex_p,
      T, DenseStageIteration.trace]
    rw [hX, hz]
    ring
  rw [heq]
  exact hbound

end CoefficientTwoPrecision.ActualStageAssembly

#print axioms CoefficientTwoPrecision.ActualStageAssembly.final_stage
