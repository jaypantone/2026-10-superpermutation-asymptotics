import Quantitative.SparseStageIteration
import Quantitative.CanonicalSourceFamily
import Quantitative.ActualCountEstimates

/-!
# Turning the actual canonical contours into a sparse Stage block

The letters and the next fresh symbol are those already used by the
Stage constructor. The canonical relabeling construction supplies all
permutations of the old alphabet. Its exact integer counts are the
counts bounded by the contour estimates.
-/

namespace CoefficientTwoPrecision.StageSourceCertificate

open SuperpermutationUpperBound SuperpermutationUpperBound43586371
open StageState SourceUniverse SourceFamilyAdapter SourceAdvancement SparseStageIteration
open CandidateFactorization SourceCountErrors

def controls {m : Nat} (S : BuiltStage m) (W : Nat) : List Nat :=
  freshExtra m (W - 1) ++ [S.z]

def next (m W : Nat) : Nat := m + (W - 1) + 3

theorem alphabet_data {m : Nat} (S : BuiltStage m) (W : Nat) (hW : 0 < W) :
    (controls S W).length = W ∧
      (controls S W ++ S.A0).Nodup ∧
      9 ∉ controls S W ++ S.A0 ∧ 10 ∉ controls S W ++ S.A0 ∧
      next m W ∉ controls S W ++ S.A0 ∧ next m W ≠ 9 := by
  have hL := letOK_fresh S.labels S.size (W - 1)
  have hnd := hL.nodup
  have h9 := hL.nine
  have h10 := hL.ten
  have he : controls S W ++ S.A0 = freshExtra m (W - 1) ++ S.z :: S.A0 := by
    simp only [controls, List.append_assoc, List.singleton_append]
  rw [← he] at hnd h9 h10
  refine ⟨?_, (List.nodup_cons.mp hnd).2,
    (fun h => h9 (List.mem_cons_of_mem _ h)), (fun h => h10 (List.mem_cons_of_mem _ h)),
    (List.nodup_cons.mp hnd).1, ?_⟩
  · simp only [controls, List.length_append, freshExtra_length, List.length_singleton]
    omega
  · intro hn
    exact h9 (List.mem_cons.mpr (Or.inl hn.symm))

theorem from_contours {m : Nat} (r : Nat) (hr : 6 ≤ r) (S : BuiltStage m)
    (hm : 4 * errorNumerator r (sourceWidth r) ≤ m)
    (F : List (SourceContour (controls S (sourceWidth r) ++ S.A0) (m + sourceWidth r - 2)))
    (hinsertion : ∀ row ∈ sourceRows F, InsertionAbove (controls S (sourceWidth r)) S.A0 row.base)
    (hdistinct : (sourceRows F).Pairwise (fun row other => ¬ CyclicEq row.base other.base))
    (hretention : |(F.length : ℚ) / candidateCount r m - 1| ≤
      deletionNumerator r (sourceWidth r) / m)
    (hperturb : ∀ C ∈ F,
      |(C.rows.length : ℚ) - (((r : ℚ) - 2) * (backgroundSize r m : ℚ) ^ 2 +
        ((r : ℚ) * ((r : ℚ) - 1) + 1) * backgroundSize r m)| ≤
      10 * (r : ℚ) ^ 2 * (52 * r ^ 4 * sourceWidth r ^ 2 : Nat) * backgroundSize r m)
    (hcharge : ∀ C ∈ F,
      (C.rows.map Row.charge).sum = 2 * (r - 1) * backgroundSize r m)
    (hg : ∀ C ∈ F, portGcd C.rows (m + sourceWidth r - 2) ≤ r - 1) :
    Nonempty (SparseBlockCertificate r S) := by
  have hW := ConstructionSize.width_positive r hr
  have hm0 := (ConstructionSize.threshold_conditions r m hr hm).1
  obtain ⟨hwidth, hnd, h9, h10, hnext, hnext9⟩ := alphabet_data S (sourceWidth r) hW
  have hsize : (controls S (sourceWidth r) ++ S.A0).length = m + sourceWidth r - 2 + 2 := by
    rw [List.length_append, hwidth, S.size]
    have hlarge := ConstructionSize.width_linear r hr
    omega
  have hthree : 3 ≤ m + sourceWidth r - 2 + 2 := by
    have hlarge := ConstructionSize.width_linear r hr
    omega
  have hold : 0 < S.A0.length := by rwa [S.size]
  have hold9 : 9 ∉ S.A0 := fun h => h9 (List.mem_append_right _ h)
  let K : Block S (sourceWidth r) := CanonicalSourceFamily.widthBlock
    S.A0 (controls S (sourceWidth r)) (next m (sourceWidth r)) (m + sourceWidth r - 2)
    hold hnd hold9 hsize hthree hnext hnext9 h10 F hinsertion hdistinct
  have hcounts := CanonicalSourceFamily.widthBlock_counts
    S.A0 (controls S (sourceWidth r)) (next m (sourceWidth r)) (m + sourceWidth r - 2)
    hold hnd hold9 hsize hthree hnext hnext9 h10 F hinsertion hdistinct
  change K.sourceRows = _ ∧ K.sourceCharge = _ ∧ K.advancedCircles = _ at hcounts
  have hc : K.advancedCircles = (circles F).length := hcounts.2.2.trans (circles_length F).symm
  obtain ⟨theta, epsilon, hdensity, hcost, htheta, hepsilon, hratio⟩ :=
    ActualCountEstimates.estimates F r m (52 * r ^ 4 * sourceWidth r ^ 2) hr hm
      (Nat.le_refl _) hretention hperturb hcharge hg
  refine ⟨{
    family := K
    theta := theta
    epsilon := epsilon
    density_eq := ?_
    cost_eq := ?_
    errors := ⟨htheta, hepsilon⟩
    circle_ratio := ?_ }⟩
  · simpa only [hcounts.1] using hdensity
  · rw [hcounts.2.1, hc]
    convert hcost using 1 <;> ring
  · simpa only [hcounts.2.1, hc] using hratio

end CoefficientTwoPrecision.StageSourceCertificate

#print axioms CoefficientTwoPrecision.StageSourceCertificate.alphabet_data
#print axioms CoefficientTwoPrecision.StageSourceCertificate.from_contours
