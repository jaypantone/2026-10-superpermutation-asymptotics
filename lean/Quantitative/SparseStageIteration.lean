import Quantitative.StageState
import Quantitative.NumericalAssembly

/-!
# Actual sparse stages, conditional only on the sparse-family supplier

The geometric interface is `SparseFamilySupplier`. It returns an actual
`WidthBlockFamily`, with the uniform integer counts and four estimates used
in the transfer. In particular it supplies the original Level, safety,
coverage, and remaining-chart certificates, not an assumed Stage recurrence.

From this input we construct the Stage at every scheduled sparse boundary.
The numerical data are extracted from the chosen actual families, and their
recurrences follow from the actual Stage constructor.
SparseFamilyConstruction proves the supplier for the prescribed parameters.
-/

namespace CoefficientTwoPrecision.SparseStageIteration

open SuperpermutationUpperBound SuperpermutationUpperBound43586371
open StageState SourceUniverse

/-- The exact geometric input needed at one scheduled source size. -/
structure SparseBlockCertificate (r : ℕ) {m : ℕ} (S : BuiltStage m) where
  family : Block S (sourceWidth r)
  theta : ℚ
  epsilon : ℚ
  density_eq : (family.sourceRows : ℚ) / (risingCount m (sourceWidth r) : ℚ) =
    (sourceRho r * (sourceWidth r : ℚ) / (m : ℚ)) * (1 + theta)
  cost_eq : ((family.sourceCharge : ℚ) + (family.advancedCircles : ℚ)) /
      (risingCount m (sourceWidth r) : ℚ) =
    ((2 * ((r : ℚ) - 1) / ((r : ℚ) - 2)) *
      (sourceRho r * (sourceWidth r : ℚ)) / (m : ℚ) ^ 2) * (1 + epsilon)
  errors : |theta| ≤ (errorNumerator r (sourceWidth r) : ℚ) / (m : ℚ) ∧
    |epsilon| ≤ (errorNumerator r (sourceWidth r) : ℚ) / (m : ℚ)
  circle_ratio : (family.advancedCircles : ℚ) ≤
    ((r : ℚ) - 1) * (family.sourceCharge : ℚ) / (m : ℚ)

/-- The source-family interface used by the assembly theorem.
Its existence is proved in SparseFamilyConstruction. -/
def SparseFamilySupplier (r : ℕ) : Prop :=
  ∀ (m : ℕ) (S : BuiltStage m), r ∣ m →
    4 * errorNumerator r (sourceWidth r) ≤ m → Nonempty (SparseBlockCertificate r S)

section Schedule

variable (n r : ℕ) (hr : 6 ≤ r) (hn : transferConstant * r ^ 61 ≤ n)
  (supplier : SparseFamilySupplier r)

include hr hn in
private theorem initial_size : 9 ≤ scheduleStart n r := by
  obtain ⟨_, _, hJ, _, _, hs⟩ := source_schedule_valid n r hr hn
  have hhalf := (hs 0 hJ).2.2.1
  simp only [sparseStart, Nat.zero_mul, Nat.add_zero] at hhalf
  have hsize := (construction_threshold_conditions r n hr hn).2.1
  have hrpow : 1 ≤ r ^ 2 := Nat.one_le_pow 2 r (by omega)
  nlinarith only [hhalf, hsize, hrpow]

include hr hn in
private theorem initial_stage_exist :
    ∃ S : BuiltStage (sparseStart n r (sourceWidth r) 0),
      S.p = 1 ∧ S.X = 0 ∧ S.zmass = 0 := by
  obtain ⟨S, hp, hX, hz⟩ :=
    StageState.initial (scheduleStart n r) (initial_size n r hr hn)
  let T := S.reindex (show scheduleStart n r = sparseStart n r (sourceWidth r) 0 by
    simp only [sparseStart, Nat.zero_mul, Nat.add_zero])
  refine ⟨T, ?_, ?_, ?_⟩
  · simpa only [T, BuiltStage.reindex_p] using hp
  · simpa only [T, BuiltStage.reindex_X] using hX
  · simpa only [T, BuiltStage.reindex_zmass] using hz

noncomputable def startStage : BuiltStage (sparseStart n r (sourceWidth r) 0) :=
  Classical.choose (initial_stage_exist n r hr hn)

private theorem startStage_values :
    (startStage n r hr hn).p = 1 ∧ (startStage n r hr hn).X = 0 ∧
      (startStage n r hr hn).zmass = 0 :=
  Classical.choose_spec (initial_stage_exist n r hr hn)

noncomputable def selectBlock (i : ℕ) (hi : i < sparseBlocks n r (sourceWidth r))
    (S : BuiltStage (sparseStart n r (sourceWidth r) i)) : SparseBlockCertificate r S :=
  Classical.choice (supplier _ S
    ((source_schedule_valid n r hr hn).2.2.2.2.2 i hi).1
    ((source_schedule_valid n r hr hn).2.2.2.2.2 i hi).2.1)

private theorem next_size (i : ℕ) :
    sparseStart n r (sourceWidth r) i + sourceWidth r =
      sparseStart n r (sourceWidth r) (i + 1) := by
  simp only [sparseStart, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

/-- Each active step applies the supplied actual family. Empty extensions
past the prescribed last step merely make this sequence total on Nat. -/
noncomputable def stages : (i : ℕ) → BuiltStage (sparseStart n r (sourceWidth r) i)
  | 0 => startStage n r hr hn
  | i + 1 =>
    let S := stages i
    if hi : i < sparseBlocks n r (sourceWidth r) then
      (advance S (source_schedule_valid n r hr hn).2.1
        (selectBlock n r hr hn supplier i hi S).family).reindex (next_size n r i)
    else
      (Classical.choose (empty_to S (sourceWidth r))).reindex (next_size n r i)

noncomputable def blockAt (i : ℕ) (hi : i < sparseBlocks n r (sourceWidth r)) :
    SparseBlockCertificate r (stages n r hr hn supplier i) :=
  selectBlock n r hr hn supplier i hi (stages n r hr hn supplier i)

/-- The numerical records are read from the selected actual block families. -/
noncomputable def sourceData : SparseNumericalData n r where
  rows i := if hi : i < sparseBlocks n r (sourceWidth r) then
    (blockAt n r hr hn supplier i hi).family.sourceRows else 0
  charge i := if hi : i < sparseBlocks n r (sourceWidth r) then
    (blockAt n r hr hn supplier i hi).family.sourceCharge else 0
  circles i := if hi : i < sparseBlocks n r (sourceWidth r) then
    (blockAt n r hr hn supplier i hi).family.advancedCircles else 0
  theta i := if hi : i < sparseBlocks n r (sourceWidth r) then
    (blockAt n r hr hn supplier i hi).theta else 0
  epsilon i := if hi : i < sparseBlocks n r (sourceWidth r) then
    (blockAt n r hr hn supplier i hi).epsilon else 0
  rows_le i hi := by
    simp only [dite_eq_left hi]
    have h := (blockAt n r hr hn supplier i hi).family.sourceBound
    simpa only [scheduledDenominator, List.length_append, freshExtra_length,
      List.length_singleton, (stages n r hr hn supplier i).size,
      Nat.sub_add_cancel (show 1 ≤ sourceWidth r from
        (source_schedule_valid n r hr hn).2.1)] using h
  density_eq i hi := by
    simp only [dite_eq_left hi, scheduledDenominator]
    exact (blockAt n r hr hn supplier i hi).density_eq
  cost_eq i hi := by
    simp only [dite_eq_left hi, scheduledDenominator]
    exact (blockAt n r hr hn supplier i hi).cost_eq
  errors i hi := by
    simp only [dite_eq_left hi]
    exact (blockAt n r hr hn supplier i hi).errors
  circle_ratio i hi := by
    simp only [dite_eq_left hi]
    exact (blockAt n r hr hn supplier i hi).circle_ratio

theorem step_values (i : ℕ) (hi : i < sparseBlocks n r (sourceWidth r)) :
    (stages n r hr hn supplier (i + 1)).p =
      (stages n r hr hn supplier i).p * (1 - (sourceData n r hr hn supplier).density i) ∧
    (stages n r hr hn supplier (i + 1)).X =
      (stages n r hr hn supplier i).X + (stages n r hr hn supplier i).p *
        (sourceData n r hr hn supplier).totalRate i ∧
    (stages n r hr hn supplier (i + 1)).zmass =
      (stages n r hr hn supplier i).zmass + (stages n r hr hn supplier i).p *
        (sourceData n r hr hn supplier).circleRate i := by
  simp only [stages, dite_eq_left hi, BuiltStage.reindex_p, BuiltStage.reindex_X,
    BuiltStage.reindex_zmass, advance_p, advance_X, advance_zmass,
    sourceData, SparseNumericalData.density, SparseNumericalData.totalRate,
    SparseNumericalData.circleRate, scheduledDenominator, blockAt]
  trivial

/-- These are identities for the counts of actual constructed Stages. -/
theorem stage_values (j : ℕ) (hj : j ≤ sparseBlocks n r (sourceWidth r)) :
    (stages n r hr hn supplier j).p = pending (sourceData n r hr hn supplier).density j ∧
    (stages n r hr hn supplier j).X = accumulatedCost
      (sourceData n r hr hn supplier).density (sourceData n r hr hn supplier).totalRate j ∧
    (stages n r hr hn supplier j).zmass = accumulatedCost
      (sourceData n r hr hn supplier).density (sourceData n r hr hn supplier).circleRate j := by
  induction j with
  | zero => exact startStage_values n r hr hn
  | succ j ih =>
    obtain ⟨hp, hX, hz⟩ := ih (by omega)
    obtain ⟨hps, hXs, hzs⟩ := step_values n r hr hn supplier j (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [hps, hp]
      rfl
    · rw [hXs, hX, hp]
      rfl
    · rw [hzs, hz, hp]
      rfl

end Schedule

end CoefficientTwoPrecision.SparseStageIteration

#print axioms CoefficientTwoPrecision.SparseStageIteration.sourceData
#print axioms CoefficientTwoPrecision.SparseStageIteration.stage_values
