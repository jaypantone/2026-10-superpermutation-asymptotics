import Quantitative.ActualCyclicMatching
import Quantitative.PositionalCatalogue

/-!
# Every actual frame intersection gives a counted positional witness

The witness retains the actual common-label matching. Equality of its
background cuts determines the translated target coordinates, which then
belong to the finite affine reconstruction catalogue. No distribution
assumption or arbitrary matching of physical positions is used.
-/

namespace CoefficientTwoPrecision.PositionalExtraction

open FiniteRoles RobustMatching BatchSafety ActualCyclicMatching

theorem actual_reconstruction {M d : Nat} [NeZero M] {Control α : Type} [DecidableEq α]
    (hM : 2 ≤ M) (backgroundTest : α → Bool)
    (background : Fin M → α) (embed : Control → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false)
    (first second : Role (d + 2) ≃ Control)
    (q q' : Fin (d + 2) → Fin M) (hmono : StrictMono q) (hmono' : StrictMono q')
    (hr : Robust (fun i => cutValue (q i))) (hr' : Robust (fun i => cutValue (q' i)))
    (hz : q 0 = 0) (hz' : q' 0 = 0)
    (sumIndex : Fin (d + 1))
    (hrelation : (∑ i, (AffineReconstruction.frameWeight d sumIndex.succ i : ZMod M) *
      cutValue (q' i)) = 0)
    (t t' : ZMod M) (phase phase' : Fin (d + 2) → Bool)
    (cuts cuts' : Fin (d + 2) → Fin M) (gap gap' : Nat)
    (hrep : Represents (fun i => cutValue (q i)) t phase cuts)
    (hrep' : Represents (fun i => cutValue (q' i)) t' phase' cuts')
    (hcyclic : (ActualMatching.base background embed first cuts gap).IsRotated
      (ActualMatching.base background embed second cuts' gap')) :
    ∃ omitted other : Fin (d + 2), ∃ offset : Fin (d + 1),
      ((fun i => cutValue (q' i)), t' - t) ∈ PositionalCatalogue.candidates
        (fun i => cutValue (q i)) (fun i => (bit (phase i) : ZMod M))
        (fun i => (bit (phase' i) : ZMod M)) omitted offset sumIndex other ∧
      ∀ i : Fin (d + 1),
        Matches first second (omitted.succAbove (i + offset)) (other.succAbove i) := by
  have hcross (c : Control) (i : Fin M) : embed c ≠ background i := by
    intro heq
    have h := congrArg backgroundTest heq
    simp only [htb, htc] at h
    cases h
  obtain ⟨omitted, other, offset, hmatches⟩ := actual_retained_matching hM
    (show 0 < d + 1 by omega) background embed hembed hcross first second
    q q' hmono hmono' hr hr' hz hz' t t' phase phase' cuts cuts' gap gap'
    hrep hrep' hcyclic
  refine ⟨omitted, other, offset, ?_, hmatches⟩
  apply PositionalCatalogue.candidates_mem
  · simp only [hz', cutValue, Fin.val_zero, Nat.cast_zero]
  · exact hrelation
  · intro i
    have hc := congrArg cutValue (ActualMatching.matched_cuts_eq backgroundTest
      background embed hbackground hembed htb htc first second cuts cuts' gap gap'
      hcyclic (omitted.succAbove (i + offset)) (other.succAbove i) (hmatches i))
    rw [hrep, hrep'] at hc
    dsimp only [RobustSafety.perturbed] at hc
    linear_combination -hc

end CoefficientTwoPrecision.PositionalExtraction

#print axioms CoefficientTwoPrecision.PositionalExtraction.actual_reconstruction
