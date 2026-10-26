import Quantitative.StationaryCircle

/-!
# Relabelling the stationary indices preserves the literal renderer

With distinct cuts, at most one control occupies each background cut.
Consequently its position in the finite enumeration of stationary indices
does not affect the rendered word. This permits the descending normal-order
ranks and increasing physical cut indices to be used in the same proof.
-/

namespace CoefficientTwoPrecision.RendererReindex

open StationaryCircle

theorem block_reindex {M k : Nat} {α : Type}
    (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hinj : Function.Injective cuts)
    (order : Equiv.Perm (Fin k)) (cut : Fin M) :
    block background (resident ∘ order) (cuts ∘ order) cut =
      block background resident cuts cut := by
  classical
  by_cases hoccupied : ∃ j, cuts j = cut
  · obtain ⟨j, rfl⟩ := hoccupied
    have hcut : (cuts ∘ order) (order.symm j) = cuts j := by simp
    have hc : controlsAt (cuts ∘ order) (cuts j) = [order.symm j] := by
      rw [← hcut]
      exact controlsAt_target _ (hinj.comp order.injective) _
    simp only [block, hc, controlsAt_target cuts hinj j, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Function.comp_apply, order.apply_symm_apply]
  · have he : ∀ j, cuts j ≠ cut := fun j hj => hoccupied ⟨j, hj⟩
    have he' : ∀ j, (cuts ∘ order) j ≠ cut := fun j => he (order j)
    simp only [block, controlsAt_empty cuts cut he, controlsAt_empty (cuts ∘ order) cut he',
      List.map_nil]

theorem render_reindex {M k : Nat} {α : Type}
    (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hinj : Function.Injective cuts)
    (order : Equiv.Perm (Fin k)) :
    render background (resident ∘ order) (cuts ∘ order) =
      render background resident cuts := by
  unfold render
  have h : block background (resident ∘ order) (cuts ∘ order) =
      block background resident cuts := funext (block_reindex background resident cuts hinj order)
  rw [h]

end CoefficientTwoPrecision.RendererReindex

#print axioms CoefficientTwoPrecision.RendererReindex.render_reindex
