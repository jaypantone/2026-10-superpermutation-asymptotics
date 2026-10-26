import Quantitative.PackingSupply
import Quantitative.RobustReindex

/-!
# The separated family excludes intersections of actual schedule rows

The input row condition is the literal envelope already proved for every
normal, parking and cleanup source row. Thus the finite selection applies
to the original descending target engine, including the cyclic seam.
-/

namespace CoefficientTwoPrecision.LiteralPacking

open LabelledReconstruction SortedFrameSupply

def InEnvelope {M d : Nat} {α : Type} (background : Fin M → α)
    (embed : FiniteRoles.Role (d + 2) → α) (frame : Labelled M d) (source : List α) : Prop :=
  LiteralEnvelope.Envelope background
    (fun p => embed (FiniteRoles.lift ((PhysicalJointStates.reverseRoles (d + 2)).trans frame.2) p))
    (fun i => frame.1 i.rev) source

theorem exists_literal_separated {M d : Nat} [NeZero M] {α : Type} [DecidableEq α]
    (hd : 3 ≤ d) (hM : 2 ≤ M) (hsize : 38 * (d + 3) ^ 4 ≤ M)
    (backgroundTest : α → Bool) (background : Fin M → α)
    (embed : FiniteRoles.Role (d + 2) → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false) :
    ∃ S : Finset (Labelled M d), S ⊆ labelledFrames M d ∧
      S.card = ⌊sourceEta (d + 3) * (M : ℚ) ^ d⌋₊ ∧
      ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
        ∀ first second : List α, InEnvelope background embed source first →
          InEnvelope background embed target second → ¬ first.IsRotated second := by
  classical
  obtain ⟨S, hS, hcard, hsep⟩ := PackingSupply.exists_separated hd hM hsize
    backgroundTest background embed hbackground hembed htb htc
  refine ⟨S, hS, hcard, ?_⟩
  intro source hs target ht hne first second hfirst hsecond hcyclic
  obtain ⟨_, _, _, _, hr, _⟩ := physicalFrame_properties source.1
    (Finset.mem_product.mp (hS hs)).1
  obtain ⟨_, _, _, _, hr', _⟩ := physicalFrame_properties target.1
    (Finset.mem_product.mp (hS ht)).1
  obtain ⟨index, translation, gap, hleft⟩ :=
    PhysicalEnvelope.literal_mem background embed source.2 source.1 hr first hfirst
  obtain ⟨index', translation', gap', hright⟩ :=
    PhysicalEnvelope.literal_mem background embed target.2 target.1 hr' second hsecond
  apply hsep source hs target ht hne
  refine ⟨index, index', translation, translation', gap, gap', ?_⟩
  simpa only [hleft, hright] using hcyclic

end CoefficientTwoPrecision.LiteralPacking

#print axioms CoefficientTwoPrecision.LiteralPacking.exists_literal_separated
