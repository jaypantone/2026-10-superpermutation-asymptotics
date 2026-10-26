import Quantitative.LabelledReconstruction
import Quantitative.JointStates
import Quantitative.RobustMatching

/-!
# A polynomial reconstruction count over the joint-state catalogue

The two phase functions and two role actions are chosen together, one joint
index per row. The union retains labelled tuples and counts coincident
envelopes as separate vertices whenever their initial labels differ.
-/

namespace CoefficientTwoPrecision.JointReconstruction

open FiniteRoles LabelledReconstruction

variable {M d : Nat} [NeZero M] {I : Type} [Fintype I]

noncomputable def catalogue (q : Fin (d + 2) → ZMod M)
    (initial : Equiv.Perm (Role (d + 2)))
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool) :
    Finset (Labelled M d) := by
  classical
  exact Finset.univ.biUnion (fun pair : I × I =>
    LabelledReconstruction.all q
      (fun i => (RobustMatching.bit (phase pair.1 i) : ZMod M))
      (fun i => (RobustMatching.bit (phase pair.2 i) : ZMod M))
      ((action pair.1).trans initial) (action pair.2))

theorem catalogue_card (hd : 2 ≤ d) (q : Fin (d + 2) → ZMod M)
    (initial : Equiv.Perm (Role (d + 2)))
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool) :
    (catalogue q initial action phase).card ≤
      Fintype.card I ^ 2 * ((d + 2) * (d + 1) ^ 2 * (2 * d) * 2) := by
  classical
  have h := FiniteFibers.bad_union_count (Finset.univ : Finset (I × I))
    (fun pair => LabelledReconstruction.all q
      (fun i => (RobustMatching.bit (phase pair.1 i) : ZMod M))
      (fun i => (RobustMatching.bit (phase pair.2 i) : ZMod M))
      ((action pair.1).trans initial) (action pair.2))
    ((d + 2) * (d + 1) ^ 2 * (2 * d) * 2)
    (fun pair _ => LabelledReconstruction.all_card hd _ _ _ _ _)
  simpa only [catalogue, Finset.card_univ, Fintype.card_prod, pow_two] using h

theorem catalogue_card_64 (hd : 2 ≤ d) (hI : Fintype.card I ≤ 4 * (d + 3) ^ 2)
    (q : Fin (d + 2) → ZMod M) (initial : Equiv.Perm (Role (d + 2)))
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool) :
    (catalogue q initial action phase).card ≤ 64 * (d + 3) ^ 8 := by
  have hpos : (d + 2) * (d + 1) ^ 2 * (2 * d) * 2 ≤ 4 * (d + 3) ^ 4 := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul (show d + 2 ≤ d + 3 by omega)
      (Nat.pow_le_pow_left (show d + 1 ≤ d + 3 by omega) 2))
      (Nat.mul_le_mul_left 2 (show d ≤ d + 3 by omega))
    calc
      (d + 2) * (d + 1) ^ 2 * (2 * d) * 2 ≤
          ((d + 3) * (d + 3) ^ 2 * (2 * (d + 3))) * 2 := Nat.mul_le_mul_right 2 h
      _ = 4 * (d + 3) ^ 4 := by ring
  calc
    (catalogue q initial action phase).card ≤
        Fintype.card I ^ 2 * ((d + 2) * (d + 1) ^ 2 * (2 * d) * 2) :=
      catalogue_card hd q initial action phase
    _ ≤ (4 * (d + 3) ^ 2) ^ 2 * (4 * (d + 3) ^ 4) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hI 2) hpos
    _ = 64 * (d + 3) ^ 8 := by ring

theorem joint_index_card (d : Nat) :
    Fintype.card (JointStates.Index (d + 2)) ≤ 4 * (d + 3) ^ 2 := by
  simp only [JointStates.Index, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  nlinarith

theorem mem_catalogue (q : Fin (d + 2) → ZMod M)
    (initial : Equiv.Perm (Role (d + 2)))
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    (first second : I) (target : Labelled M d)
    (h : target ∈ LabelledReconstruction.all q
      (fun i => (RobustMatching.bit (phase first i) : ZMod M))
      (fun i => (RobustMatching.bit (phase second i) : ZMod M))
      ((action first).trans initial) (action second)) :
    target ∈ catalogue q initial action phase := by
  classical
  exact Finset.mem_biUnion.mpr ⟨(first, second), Finset.mem_univ _, h⟩

end CoefficientTwoPrecision.JointReconstruction

#print axioms CoefficientTwoPrecision.JointReconstruction.catalogue_card_64
#print axioms CoefficientTwoPrecision.JointReconstruction.joint_index_card
