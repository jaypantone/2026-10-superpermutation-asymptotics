import Quantitative.AffineReconstruction
import Mathlib.Data.ZMod.Basic

/-!
# Reconstructing actual anchored cuts and their common translation

A positional match specifies all but one of the translated target cuts.
The affine relation determines the remaining cut with bounded multiplicity.
The anchored cut then determines the translation, so no additional factor
of the modulus is lost. These are counts of actual residue tuples.
-/

namespace CoefficientTwoPrecision.AnchoredReconstruction

open AffineReconstruction

variable {M k : Nat} [NeZero M]

def residue (x : ZMod M) : Fin M := ⟨x.val, ZMod.val_lt x⟩

def targets (anchor : Fin k) (a : Fin k → Int)
    (observed : Fin k → ZMod M) (missing : Fin k) :
    Finset ((Fin k → ZMod M) × ZMod M) :=
  Finset.univ.filter (fun p => p.1 anchor = 0 ∧
    (∑ i, (a i : ZMod M) * p.1 i) = 0 ∧
    ∀ i, i ≠ missing → p.1 i + p.2 = observed i)

theorem targets_card (anchor : Fin k) (a : Fin k → Int)
    (hasum : ∑ i, a i = 0) (observed : Fin k → ZMod M)
    (missing : Fin k) (ha : a missing ≠ 0) :
    (targets anchor a observed missing).card ≤ (a missing).natAbs := by
  classical
  let encode (p : (Fin k → ZMod M) × ZMod M) : Fin k → Fin M :=
    fun i => residue (p.1 i + p.2)
  have hcastsum : (∑ i, (a i : ZMod M)) = 0 := by
    rw [← Int.cast_sum, hasum, Int.cast_zero]
  have hmap : Set.MapsTo encode
      (targets anchor a observed missing : Set ((Fin k → ZMod M) × ZMod M))
      (completions M k a (fun i => residue (observed i)) missing :
        Set (Fin k → Fin M)) := by
    intro p hp
    obtain ⟨_, hrel, hmatches⟩ := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro i hi
      change residue (p.1 i + p.2) = residue (observed i)
      rw [hmatches i hi]
    · have htranslated : (∑ i, (a i : ZMod M) * (p.1 i + p.2)) = 0 := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hcastsum, hrel]
        simp
      apply (ZMod.intCast_eq_intCast_iff _ _ M).mp
      push_cast
      simpa only [encode, residue, ZMod.natCast_val, ZMod.cast_id] using htranslated
  have hinj : (targets anchor a observed missing :
      Set ((Fin k → ZMod M) × ZMod M)).InjOn encode := by
    intro p hp q hq heq
    have hp0 := (Finset.mem_filter.mp hp).2.1
    have hq0 := (Finset.mem_filter.mp hq).2.1
    have hcoord (i : Fin k) : p.1 i + p.2 = q.1 i + q.2 := by
      apply ZMod.val_injective
      exact congrArg Fin.val (congrFun heq i)
    have ht : p.2 = q.2 := by simpa only [hp0, hq0, zero_add] using hcoord anchor
    apply Prod.ext
    · funext i
      exact add_right_cancel (by simpa only [ht] using hcoord i)
    · exact ht
  exact (Finset.card_le_card_of_injOn encode hmap hinj).trans
    (completions_card M k (NeZero.pos M) a (fun i => residue (observed i)) missing ha)

/-- The coefficients attached to the sorted physical slots sum to zero
when the sum point is distinct from the anchored zero cut. -/
theorem frameWeight_sum (d : Nat) (sumSlot : Fin (d + 2)) (hs : sumSlot ≠ 0) :
    (∑ i, frameWeight d sumSlot i) = 0 := by
  have hterm (i : Fin (d + 2)) : frameWeight d sumSlot i =
      -1 + (if i = 0 then (d : Int) else 0) +
        (if i = sumSlot then 2 else 0) := by
    simp only [frameWeight]
    split_ifs <;> simp_all <;> ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

theorem all_missing_targets_card (d : Nat) (hd : 2 ≤ d)
    (sumSlot : Fin (d + 2)) (hs : sumSlot ≠ 0)
    (observed : Fin (d + 2) → ZMod M) :
    (∑ missing, (targets 0 (frameWeight d sumSlot) observed missing).card) ≤ 2 * d := by
  calc
    ∑ missing, (targets 0 (frameWeight d sumSlot) observed missing).card ≤
        ∑ missing, (frameWeight d sumSlot missing).natAbs := by
      apply Finset.sum_le_sum
      intro missing _
      exact targets_card 0 _ (frameWeight_sum d sumSlot hs) observed missing
        (frameWeight_nonzero d hd sumSlot missing)
    _ = 2 * d := frameWeight_abs_sum d hd sumSlot

end CoefficientTwoPrecision.AnchoredReconstruction

#print axioms CoefficientTwoPrecision.AnchoredReconstruction.targets_card
#print axioms CoefficientTwoPrecision.AnchoredReconstruction.all_missing_targets_card
