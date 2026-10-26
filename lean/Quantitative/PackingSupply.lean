import Quantitative.PhysicalEnvelope
import Quantitative.ConstructionParameters

/-!
# An actual separated labelled family of the prescribed floor size

The robust-frame supply loses at most half its ordered tuples at the stated
threshold. Labels are attached before the greedy selection. The exact size
is the floor of eta times M^d, with eta defined by the construction parameters.
-/

namespace CoefficientTwoPrecision.PackingSupply

open LabelledReconstruction SortedFrameSupply EnvelopeDegree

def desiredSize (M d : Nat) : Nat :=
  ((d + 3).factorial * M ^ d) / (2 * d.factorial * (64 * (d + 3) ^ 8 + 1))

theorem desiredSize_eq_floor (M d : Nat) :
    desiredSize M d = ⌊sourceEta (d + 3) * (M : ℚ) ^ d⌋₊ := by
  have hform : sourceEta (d + 3) * (M : ℚ) ^ d =
      (((d + 3).factorial * M ^ d : Nat) : ℚ) /
        ((2 * d.factorial * (64 * (d + 3) ^ 8 + 1) : Nat) : ℚ) := by
    simp only [sourceEta, sourceDegree, Nat.add_sub_cancel, Nat.cast_mul,
      Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    ring
  rw [hform, ← Int.floor_toNat, Rat.floor_natCast_div_natCast]
  simp only [desiredSize, ← Int.natCast_ediv, Int.toNat_natCast]

theorem half_supply {M d : Nat} [NeZero M] (hd : 3 ≤ d)
    (hsize : 38 * (d + 3) ^ 4 ≤ M) :
    M ^ d ≤ 2 * (physicalFrames M d).card * d.factorial := by
  have hpow : M * M ^ (d - 1) = M ^ d := by
    rw [← pow_succ']
    congr 1
    omega
  have hbase : 36 * (d + 2) ^ 4 ≤ M := by
    have hp := Nat.pow_le_pow_left (show d + 2 ≤ d + 3 by omega) 4
    nlinarith
  have hbad : 2 * (18 * (d + 2) ^ 4 * M ^ (d - 1)) ≤ M ^ d := by
    have h := Nat.mul_le_mul_right (M ^ (d - 1)) hbase
    rw [hpow] at h
    nlinarith
  have h := physicalFrames_card_lower (NeZero.pos M) hd
  nlinarith

theorem size_budget {M d : Nat} [NeZero M] (hd : 3 ≤ d)
    (hsize : 38 * (d + 3) ^ 4 ≤ M) :
    (64 * (d + 3) ^ 8 + 1) * desiredSize M d ≤ (labelledFrames M d).card := by
  have hhalf := half_supply hd hsize
  have hdivision := Nat.mul_div_le ((d + 3).factorial * M ^ d)
    (2 * d.factorial * (64 * (d + 3) ^ 8 + 1))
  have hscaled := Nat.mul_le_mul_left (d + 3).factorial hhalf
  have hcombined : (2 * d.factorial) * ((64 * (d + 3) ^ 8 + 1) * desiredSize M d) ≤
      (2 * d.factorial) * (labelledFrames M d).card := by
    rw [labelledFrames_card]
    dsimp only [desiredSize]
    nlinarith [hdivision, hscaled]
  exact Nat.le_of_mul_le_mul_left hcombined (by positivity)

theorem exists_separated {M d : Nat} [NeZero M] {α : Type} [DecidableEq α]
    (hd : 3 ≤ d) (hM : 2 ≤ M) (hsize : 38 * (d + 3) ^ 4 ≤ M)
    (backgroundTest : α → Bool) (background : Fin M → α)
    (embed : FiniteRoles.Role (d + 2) → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false) :
    ∃ S : Finset (Labelled M d), S ⊆ labelledFrames M d ∧
      S.card = ⌊sourceEta (d + 3) * (M : ℚ) ^ d⌋₊ ∧
      ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
        ¬ Meets background embed (PhysicalJointStates.action (d + 2))
          (PhysicalJointStates.phase (d + 2)) source target := by
  classical
  let R := Meets background embed (PhysicalJointStates.action (d + 2))
    (PhysicalJointStates.phase (d + 2))
  have hdegree : ∀ source ∈ labelledFrames M d,
      ((labelledFrames M d).filter (R source)).card ≤ 64 * (d + 3) ^ 8 + 1 := by
    intro source hs
    exact (degree_64 hM (by omega) (JointReconstruction.joint_index_card d)
      backgroundTest background embed hbackground hembed htb htc
      (PhysicalJointStates.action (d + 2)) (PhysicalJointStates.phase (d + 2)) source hs).trans
      (Nat.le_succ _)
  obtain ⟨S, hS, hcard, hsep⟩ := FinitePacking.exists_separated_of_mul_le R
    (fun h => meets_symm _ _ _ _ h) (meets_refl _ _ _ _) (64 * (d + 3) ^ 8 + 1)
    (by omega) (labelledFrames M d) hdegree (desiredSize M d) (size_budget hd hsize)
  exact ⟨S, hS, hcard.trans (desiredSize_eq_floor M d), hsep⟩

end CoefficientTwoPrecision.PackingSupply

#print axioms CoefficientTwoPrecision.PackingSupply.desiredSize_eq_floor
#print axioms CoefficientTwoPrecision.PackingSupply.exists_separated
