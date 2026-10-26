import Quantitative.ActiveGrid
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact number of foreign blocks meeting an active block

For each control of an active block, take the other blocks through that
control. The at-most-one-intersection theorem says these r sets are
disjoint. Each contains A-1 blocks, so the union contains r*(A-1) blocks.
-/

namespace CoefficientTwoPrecision.ActiveIncidence

open ActiveGrid

def neighbours (r A : Nat) (hr : 0 < r) (hA : 0 < A) (b : Block r A) :
    Finset (Block r A) :=
  (activeBlock r A hr hA b).biUnion (fun p => (blocksThrough r A hr hA p).erase b)

theorem mem_neighbours (r A : Nat) (hr : 0 < r) (hA : 0 < A)
    (b c : Block r A) :
    c ∈ neighbours r A hr hA b ↔
      c ≠ b ∧ (activeBlock r A hr hA b ∩ activeBlock r A hr hA c).Nonempty := by
  constructor
  · intro hc
    obtain ⟨p, hp, hpc⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨hne, hthrough⟩ := Finset.mem_erase.mp hpc
    exact ⟨hne, p, Finset.mem_inter.mpr ⟨hp, (Finset.mem_filter.mp hthrough).2⟩⟩
  · rintro ⟨hne, p, hp⟩
    obtain ⟨hpb, hpc⟩ := Finset.mem_inter.mp hp
    exact Finset.mem_biUnion.mpr ⟨p, hpb,
      Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩⟩⟩

theorem incident_families_disjoint (r A : Nat) (hr : 0 < r) (hA : 0 < A)
    (b : Block r A) :
    (activeBlock r A hr hA b : Set (Control r A)).PairwiseDisjoint
      (fun p => (blocksThrough r A hr hA p).erase b) := by
  intro p hp q hq hpq
  apply Finset.disjoint_left.mpr
  intro c hpc hqc
  obtain ⟨hcb, hpc⟩ := Finset.mem_erase.mp hpc
  obtain ⟨_, hqc⟩ := Finset.mem_erase.mp hqc
  have hp' : p ∈ activeBlock r A hr hA b ∩ activeBlock r A hr hA c :=
    Finset.mem_inter.mpr ⟨hp, (Finset.mem_filter.mp hpc).2⟩
  have hq' : q ∈ activeBlock r A hr hA b ∩ activeBlock r A hr hA c :=
    Finset.mem_inter.mpr ⟨hq, (Finset.mem_filter.mp hqc).2⟩
  have hcard := activeBlock_inter_card r A hr hA b c hcb.symm
  exact hpq (Finset.card_le_one.mp hcard p hp' q hq')

theorem neighbours_card (r A : Nat) (hr : 0 < r) (hA : 0 < A)
    (b : Block r A) : (neighbours r A hr hA b).card = r * (A - 1) := by
  rw [neighbours, Finset.card_biUnion (incident_families_disjoint r A hr hA b)]
  have hcount (p : Control r A) (hp : p ∈ activeBlock r A hr hA b) :
      ((blocksThrough r A hr hA p).erase b).card = A - 1 := by
    rw [Finset.card_erase_of_mem ?_, blocksThrough_card]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
  calc
    (∑ p ∈ activeBlock r A hr hA b, ((blocksThrough r A hr hA p).erase b).card)
        = ∑ _p ∈ activeBlock r A hr hA b, (A - 1) := Finset.sum_congr rfl hcount
    _ = r * (A - 1) := by simp only [Finset.sum_const, activeBlock_card, Nat.nsmul_eq_mul]

theorem neighbours_le (r A : Nat) (hr : 0 < r) (hA : 0 < A)
    (b : Block r A) : (neighbours r A hr hA b).card ≤ r * A := by
  rw [neighbours_card]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

end CoefficientTwoPrecision.ActiveIncidence

#print axioms CoefficientTwoPrecision.ActiveIncidence.neighbours_card
