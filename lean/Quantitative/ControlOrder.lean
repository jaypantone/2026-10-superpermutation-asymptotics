import Quantitative.StationaryUpdate
import Quantitative.CutExtraction
import Mathlib.Data.List.Sort

/-!
# The actual control order in a rendered stationary circle

For increasing cuts, flattening the residents in background-cut order gives
the original increasing slot order. Filtering an actual base to any subset
of its stationary controls therefore gives that same order up to rotation.
This is the literal ordering input to the cyclic reconstruction matching.
-/

namespace CoefficientTwoPrecision.ControlOrder

open StationaryCircle StationaryUpdate LiteralState

variable {M k : Nat} {α : Type}

def slotOrder (cuts : Fin k → Fin M) : List (Fin k) :=
  (List.finRange M).flatMap (controlsAt cuts)

theorem slotOrder_pairwise (cuts : Fin k → Fin M) (hcuts : StrictMono cuts) :
    (slotOrder cuts).Pairwise (· < ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro cut _
    exact (List.pairwise_lt_finRange k).filter _
  · apply (List.pairwise_lt_finRange M).imp
    intro first second hlt i hi j hj
    have hi' := (mem_controlsAt cuts first i).mp hi
    have hj' := (mem_controlsAt cuts second j).mp hj
    apply hcuts.lt_iff_lt.mp
    rw [hi', hj']
    exact hlt

theorem slotOrder_eq (cuts : Fin k → Fin M) (hcuts : StrictMono cuts) :
    slotOrder cuts = List.finRange k := by
  have hpair := slotOrder_pairwise cuts hcuts
  have hnd : (slotOrder cuts).Nodup := hpair.imp (fun h => ne_of_lt h)
  have hperm : (slotOrder cuts).Perm (List.finRange k) := by
    apply (List.perm_ext_iff_of_nodup hnd (List.nodup_finRange k)).mpr
    intro j
    constructor
    · intro _
      exact List.mem_finRange j
    · intro _
      exact List.mem_flatMap.mpr ⟨cuts j, List.mem_finRange _,
        (mem_controlsAt cuts (cuts j) j).mpr rfl⟩
  exact List.Perm.eq_of_pairwise' (hpair.imp (fun h => le_of_lt h))
    (List.pairwise_le_finRange k) hperm

theorem render_control_projection (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : StrictMono cuts) (keep : α → Bool)
    (hbackground : ∀ i, keep (background i) = false) :
    (render background resident cuts).filter keep =
      ((List.finRange k).map resident).filter keep := by
  have hb (cut : Fin M) : (block background resident cuts cut).filter keep =
      ((controlsAt cuts cut).map resident).filter keep := by
    simp only [block, List.filter_append, List.filter_cons, hbackground, Bool.false_eq_true,
      ↓reduceIte, List.filter_nil, List.append_nil]
  calc
    (render background resident cuts).filter keep =
        ((List.finRange M).flatMap (fun cut => (controlsAt cuts cut).map resident)).filter keep := by
      simp only [render, List.filter_flatMap, hb]
    _ = ((slotOrder cuts).map resident).filter keep := by
      rw [slotOrder, List.map_flatMap]
    _ = ((List.finRange k).map resident).filter keep := by rw [slotOrder_eq cuts hcuts]

theorem base_control_order [DecidableEq α]
    (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : StrictMono cuts) (mobile : α) (gap : Nat)
    (keep : α → Bool) (hbackground : ∀ i, keep (background i) = false)
    (hmobile : keep mobile = false) :
    (((List.finRange k).map resident).filter keep).IsRotated
      (((render background resident cuts).rotateLeft gap ++ [mobile]).filter keep) := by
  have h := CutExtraction.filter_rotate (render background resident cuts) keep gap
  rw [render_control_projection background resident cuts hcuts keep hbackground] at h
  simpa only [rotateLeft_eq_rotate, List.filter_append, List.filter_cons, hmobile,
    Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil] using h

end CoefficientTwoPrecision.ControlOrder

#print axioms CoefficientTwoPrecision.ControlOrder.slotOrder_eq
#print axioms CoefficientTwoPrecision.ControlOrder.base_control_order
