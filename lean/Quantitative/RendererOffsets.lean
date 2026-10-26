import Quantitative.ControlOrder

/-!
# Literal positions of residents in the increasing-cut renderer

If the physical cuts are strictly increasing, the resident of slot i is
at literal index q_i+i. Its following background symbol ends the target
suffix at offset q_i+i+2. These are exact list positions and supply the
full-sweep lengths for the descending physical normal order.
-/

namespace CoefficientTwoPrecision.RendererOffsets

open LiteralState StationaryCircle StationaryUpdate ControlOrder

variable {M k : Nat} {α : Type}

theorem finRange_split_length {N : Nat} (target : Fin N) (before after : List (Fin N))
    (hsplit : List.finRange N = before ++ target :: after) : before.length = target.val := by
  have hlength := congrArg List.length hsplit
  simp only [List.length_finRange, List.length_append, List.length_cons] at hlength
  have hlt : before.length < N := by omega
  have hget : (List.finRange N)[before.length]? = some target := by
    rw [hsplit]
    simp
  rw [List.getElem?_eq_getElem (by simpa only [List.length_finRange] using hlt)] at hget
  have hval := congrArg Fin.val (Option.some.inj hget)
  simpa using hval

theorem flatMap_block_length (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (order : List (Fin M)) :
    (order.flatMap (block background resident cuts)).length =
      order.length + (order.flatMap (controlsAt cuts)).length := by
  induction order with
  | nil => rfl
  | cons cut order ih =>
    have hblock : (block background resident cuts cut).length = (controlsAt cuts cut).length + 1 := by
      simp only [block, List.length_append, List.length_map, List.length_singleton]
    rw [List.flatMap_cons, List.length_append, hblock, ih, List.length_cons,
      List.flatMap_cons, List.length_append]
    omega

/-- The renderer is split at the actual target and its background symbol,
and the prefix length is computed exactly. -/
theorem target_split_length (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : StrictMono cuts) (target : Fin k) :
    ∃ before after : List α,
      render background resident cuts = before ++ [resident target, background (cuts target)] ++ after ∧
      before.length = (cuts target).val + target.val := by
  obtain ⟨before, after, hsplit, _⟩ := List.eq_append_cons_of_mem (List.mem_finRange (cuts target))
  have hbefore := finRange_split_length (cuts target) before after hsplit
  have hslots := slotOrder_eq cuts hcuts
  unfold slotOrder at hslots
  rw [hsplit, List.flatMap_append, List.flatMap_cons,
    controlsAt_target cuts hcuts.injective target] at hslots
  simp only [List.singleton_append] at hslots
  have hslotLength := finRange_split_length target (before.flatMap (controlsAt cuts))
    (after.flatMap (controlsAt cuts)) hslots.symm
  refine ⟨before.flatMap (block background resident cuts), after.flatMap (block background resident cuts), ?_, ?_⟩
  · unfold render
    rw [hsplit, List.flatMap_append, List.flatMap_cons, target_block background resident cuts hcuts.injective target]
    simp only [List.append_assoc]
  · rw [flatMap_block_length, hbefore, hslotLength]

theorem resident_offset (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : StrictMono cuts) (target : Fin k) :
    ((render background resident cuts).rotateLeft ((cuts target).val + target.val)).head? =
      some (resident target) := by
  obtain ⟨before, after, hsplit, hlength⟩ := target_split_length background resident cuts hcuts target
  rw [← hlength, hsplit, List.append_assoc, LiteralState.rotateLeft_eq_rotate,
    List.rotate_append_length_eq]
  rfl

theorem target_suffix_offset (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : StrictMono cuts) (target : Fin k) :
    ∃ pre : List α,
      (render background resident cuts).rotateLeft ((cuts target).val + target.val + 2) =
        pre ++ [resident target, background (cuts target)] := by
  obtain ⟨before, after, hsplit, hlength⟩ := target_split_length background resident cuts hcuts target
  refine ⟨after ++ before, ?_⟩
  rw [← hlength, hsplit, rotate_to_suffix]

end CoefficientTwoPrecision.RendererOffsets

#print axioms CoefficientTwoPrecision.RendererOffsets.target_split_length
#print axioms CoefficientTwoPrecision.RendererOffsets.target_suffix_offset
