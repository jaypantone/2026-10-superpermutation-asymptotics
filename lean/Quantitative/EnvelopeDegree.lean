import Quantitative.PositionalExtraction
import Quantitative.JointReconstruction
import Quantitative.SortedFrameSupply
import Quantitative.FinitePacking

/-!
# The actual inclusive envelope degree for labelled sorted frames

An envelope consists of literal bases reconstructed from one joint index,
one common translation, and a mobile insertion gap. Intersections are
cyclic equality of those actual bases. Every intersecting labelled target
belongs to the finite reconstruction catalogue, including the source itself.
-/

namespace CoefficientTwoPrecision.EnvelopeDegree

open FiniteRoles RobustMatching BatchSafety ActualCyclicMatching LabelledReconstruction

variable {M d : Nat} [NeZero M] {I α : Type} [Fintype I] [DecidableEq α]

def phaseCuts (q : Fin (d + 2) → Fin M) (t : ZMod M) (phase : Fin (d + 2) → Bool) :
    Fin (d + 2) → Fin M := fun i => translationCut (cutValue (q i) + t + (bit (phase i) : ZMod M))

theorem phaseCuts_represents (q : Fin (d + 2) → Fin M) (t : ZMod M)
    (phase : Fin (d + 2) → Bool) :
    Represents (fun i => cutValue (q i)) t phase (phaseCuts q t phase) := by
  intro i
  exact translationCut_value _

def row (background : Fin M → α) (embed : Role (d + 2) → α)
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    (frame : Labelled M d) (index : I) (translation : ZMod M) (gap : Nat) : List α :=
  ActualMatching.base background embed ((action index).trans frame.2)
    (phaseCuts frame.1 translation (phase index)) gap

def Meets (background : Fin M → α) (embed : Role (d + 2) → α)
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    (source target : Labelled M d) : Prop :=
  ∃ first second : I, ∃ t t' : ZMod M, ∃ gap gap' : Nat,
    (row background embed action phase source first t gap).IsRotated
      (row background embed action phase target second t' gap')

noncomputable def neighbours (background : Fin M → α) (embed : Role (d + 2) → α)
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    (source : Labelled M d) : Finset (Labelled M d) := by
  classical
  exact (SortedFrameSupply.labelledFrames M d).filter (Meets background embed action phase source)

theorem meets_symm (background : Fin M → α) (embed : Role (d + 2) → α)
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    {source target : Labelled M d} (h : Meets background embed action phase source target) :
    Meets background embed action phase target source := by
  obtain ⟨first, second, t, t', gap, gap', h⟩ := h
  exact ⟨second, first, t', t, gap', gap, h.symm⟩

theorem meets_refl [Nonempty I] (background : Fin M → α) (embed : Role (d + 2) → α)
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    (source : Labelled M d) : Meets background embed action phase source source := by
  classical
  let index : I := Classical.choice inferInstance
  exact ⟨index, index, 0, 0, 0, 0, List.IsRotated.refl _⟩

theorem intersection_mem (hM : 2 ≤ M) (backgroundTest : α → Bool)
    (background : Fin M → α) (embed : Role (d + 2) → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false)
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    (source target : Labelled M d)
    (hsource : source ∈ SortedFrameSupply.labelledFrames M d)
    (htarget : target ∈ SortedFrameSupply.labelledFrames M d)
    (hmeet : Meets background embed action phase source target) :
    target ∈ JointReconstruction.catalogue (fun i => cutValue (source.1 i))
      source.2 action phase := by
  classical
  obtain ⟨_, _, hm, hz, hr, _⟩ := SortedFrameSupply.physicalFrame_properties source.1
    (Finset.mem_product.mp hsource).1
  obtain ⟨sumSlot, hs, hm', hz', hr', hrel⟩ := SortedFrameSupply.physicalFrame_properties target.1
    (Finset.mem_product.mp htarget).1
  obtain ⟨sumIndex, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hs
  obtain ⟨first, second, t, t', gap, gap', hcyclic⟩ := hmeet
  obtain ⟨omitted, other, offset, hpos, hlabels⟩ :=
    PositionalExtraction.actual_reconstruction hM backgroundTest background embed
      hbackground hembed htb htc ((action first).trans source.2) ((action second).trans target.2)
      source.1 target.1 hm hm' hr hr' hz hz' sumIndex hrel t t'
      (phase first) (phase second) _ _ gap gap'
      (phaseCuts_represents source.1 t (phase first))
      (phaseCuts_represents target.1 t' (phase second)) hcyclic
  have h := LabelledReconstruction.mem_all
    (fun i => cutValue (source.1 i))
    (fun i => (bit (phase first i) : ZMod M)) (fun i => (bit (phase second i) : ZMod M))
    (fun i => cutValue (target.1 i)) ((action first).trans source.2)
    (action second) target.2 (t' - t) omitted other offset sumIndex hpos hlabels
  have hdecode : (fun i => AnchoredReconstruction.residue (cutValue (target.1 i))) = target.1 := by
    funext i
    apply Fin.ext
    simp only [AnchoredReconstruction.residue, cutValue, ZMod.val_natCast,
      Nat.mod_eq_of_lt (target.1 i).isLt]
  rw [hdecode] at h
  exact JointReconstruction.mem_catalogue _ source.2 action phase first second target h

theorem degree_64 (hM : 2 ≤ M) (hd : 2 ≤ d)
    (hI : Fintype.card I ≤ 4 * (d + 3) ^ 2) (backgroundTest : α → Bool)
    (background : Fin M → α) (embed : Role (d + 2) → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false)
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    (source : Labelled M d) (hsource : source ∈ SortedFrameSupply.labelledFrames M d) :
    (neighbours background embed action phase source).card ≤ 64 * (d + 3) ^ 8 := by
  classical
  apply (Finset.card_le_card ?_).trans
    (JointReconstruction.catalogue_card_64 hd hI (fun i => cutValue (source.1 i)) source.2 action phase)
  intro target ht
  obtain ⟨htarget, hmeet⟩ := Finset.mem_filter.mp ht
  exact intersection_mem hM backgroundTest background embed hbackground hembed htb htc
    action phase source target hsource htarget hmeet

end CoefficientTwoPrecision.EnvelopeDegree

#print axioms CoefficientTwoPrecision.EnvelopeDegree.intersection_mem
#print axioms CoefficientTwoPrecision.EnvelopeDegree.degree_64
