import Quantitative.LiteralPacking

/-!
# One selected frame family for every background and active block

Selection takes place once on an alphabet with separate background and
control symbols. Injective relabeling transfers its separation to every
actual guard background. In particular the selected frames are independent
of the guard cuts, as required when counting guard-variable deletions.
-/

namespace CoefficientTwoPrecision.UniformPacking

open LabelledReconstruction SortedFrameSupply EnvelopeDegree FiniteRoles

theorem render_map {M k : Nat} {α β : Type} (f : α → β)
    (background : Fin M → α) (resident : Fin k → α) (cuts : Fin k → Fin M) :
    (StationaryCircle.render background resident cuts).map f =
      StationaryCircle.render (f ∘ background) (f ∘ resident) cuts := by
  simp only [StationaryCircle.render, StationaryCircle.block, List.map_flatMap,
    List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def]
  rfl

theorem row_map {M d : Nat} [NeZero M] {I α β : Type} [Fintype I]
    (f : α → β) (background : Fin M → α) (embed : Role (d + 2) → α)
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    (frame : Labelled M d) (index : I) (translation : ZMod M) (gap : Nat) :
    (row background embed action phase frame index translation gap).map f =
      row (f ∘ background) (f ∘ embed) action phase frame index translation gap := by
  simp only [row, ActualMatching.base, LiteralState.rotateLeft_eq_rotate, List.map_append,
    List.map_rotate, List.map_cons, List.map_nil, render_map, ActualMatching.resident,
    Function.comp_def]
  rfl

theorem isRotated_of_map {α β : Type} (f : α → β) (hf : Function.Injective f)
    {first second : List α} (h : (first.map f).IsRotated (second.map f)) :
    first.IsRotated second := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  apply List.map_injective_iff.mpr hf
  simpa only [List.map_rotate] using hn

theorem joint_injective {M k : Nat} {α : Type}
    (background : Fin M → α) (embed : Role k → α)
    (hb : Function.Injective background) (he : Function.Injective embed)
    (hcross : ∀ i c, background i ≠ embed c) :
    Function.Injective (Sum.elim background embed) := by
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (hb h)
    | inr c => exact False.elim (hcross i c h)
  | inr c =>
    cases y with
    | inl i => exact False.elim (hcross i c h.symm)
    | inr c' => exact congrArg Sum.inr (he h)

theorem exists_uniform_separated {M d : Nat} [NeZero M]
    (hd : 3 ≤ d) (hM : 2 ≤ M) (hsize : 38 * (d + 3) ^ 4 ≤ M) :
    ∃ S : Finset (Labelled M d), S ⊆ labelledFrames M d ∧
      S.card = ⌊sourceEta (d + 3) * (M : ℚ) ^ d⌋₊ ∧
      ∀ {α : Type} (background : Fin M → α) (embed : Role (d + 2) → α),
        Function.Injective background → Function.Injective embed →
        (∀ i c, background i ≠ embed c) →
        ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
          ¬ Meets background embed (PhysicalJointStates.action (d + 2))
            (PhysicalJointStates.phase (d + 2)) source target := by
  classical
  let Alphabet := Sum (Fin M) (Role (d + 2))
  let test : Alphabet → Bool := Sum.elim (fun _ => true) (fun _ => false)
  obtain ⟨S, hS, hcard, hsep⟩ := PackingSupply.exists_separated hd hM hsize test
    (Sum.inl : Fin M → Alphabet) (Sum.inr : Role (d + 2) → Alphabet)
    Sum.inl_injective Sum.inr_injective (fun _ => rfl) (fun _ => rfl)
  refine ⟨S, hS, hcard, ?_⟩
  intro α background embed hb he hcross source hs target ht hne hmeet
  apply hsep source hs target ht hne
  obtain ⟨first, second, t, t', gap, gap', h⟩ := hmeet
  refine ⟨first, second, t, t', gap, gap', ?_⟩
  apply isRotated_of_map (Sum.elim background embed) (joint_injective background embed hb he hcross)
  simpa only [row_map, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using h

theorem exists_uniform_literal_separated {M d : Nat} [NeZero M]
    (hd : 3 ≤ d) (hM : 2 ≤ M) (hsize : 38 * (d + 3) ^ 4 ≤ M) :
    ∃ S : Finset (Labelled M d), S ⊆ labelledFrames M d ∧
      S.card = ⌊sourceEta (d + 3) * (M : ℚ) ^ d⌋₊ ∧
      ∀ {α : Type} (background : Fin M → α) (embed : Role (d + 2) → α),
        Function.Injective background → Function.Injective embed →
        (∀ i c, background i ≠ embed c) →
        ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
          ∀ first second : List α, LiteralPacking.InEnvelope background embed source first →
            LiteralPacking.InEnvelope background embed target second → ¬ first.IsRotated second := by
  classical
  obtain ⟨S, hS, hcard, hsep⟩ := exists_uniform_separated hd hM hsize
  refine ⟨S, hS, hcard, ?_⟩
  intro α background embed hb he hcross source hs target ht hne first second hf hg hc
  obtain ⟨_, _, _, _, hr, _⟩ := physicalFrame_properties source.1
    (Finset.mem_product.mp (hS hs)).1
  obtain ⟨_, _, _, _, hr', _⟩ := physicalFrame_properties target.1
    (Finset.mem_product.mp (hS ht)).1
  obtain ⟨index, translation, gap, hfirst⟩ :=
    PhysicalEnvelope.literal_mem background embed source.2 source.1 hr first hf
  obtain ⟨index', translation', gap', hsecond⟩ :=
    PhysicalEnvelope.literal_mem background embed target.2 target.1 hr' second hg
  apply hsep background embed hb he hcross source hs target ht hne
  refine ⟨index, index', translation, translation', gap, gap', ?_⟩
  simpa only [hfirst, hsecond] using hc

end CoefficientTwoPrecision.UniformPacking

#print axioms CoefficientTwoPrecision.UniformPacking.exists_uniform_separated
#print axioms CoefficientTwoPrecision.UniformPacking.exists_uniform_literal_separated
