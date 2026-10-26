import Quantitative.RendererOffsets
import Quantitative.SourceUniverse

/-!
# Exact full-sweep length from literal resident and target offsets

Two rotations of a nodup stationary circle ending in the same background
symbol coincide. This converts the actual target suffix into a modular
equation for the number of full moves. A proper sweep has a unique value
given by the forward difference of its start and target offsets.
-/

namespace CoefficientTwoPrecision.SweepOffsets

open LiteralState StationaryCircle StationaryUpdate RendererOffsets

variable {M k : Nat} {α : Type}

theorem suffix_rotation_mod (stationary : List α) (hnd : stationary.Nodup)
    (first last : Nat) (before after : List α) (symbol : α)
    (hfirst : stationary.rotateLeft first = before ++ [symbol])
    (hlast : stationary.rotateLeft last = after ++ [symbol]) :
    first % stationary.length = last % stationary.length := by
  have hne : stationary ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hfirst
    rw [LiteralState.rotateLeft_eq_rotate, List.length_rotate, hnil] at hlength
    simp at hlength
  have hfirstRot : stationary.IsRotated (stationary.rotateLeft first) :=
    ⟨first, (LiteralState.rotateLeft_eq_rotate stationary first).symm⟩
  have hlastRot : stationary.IsRotated (stationary.rotateLeft last) :=
    ⟨last, (LiteralState.rotateLeft_eq_rotate stationary last).symm⟩
  have hndFirst : (before ++ [symbol]).Nodup := by
    rw [← hfirst]
    exact hfirstRot.nodup_iff.mp hnd
  have hfresh : symbol ∉ before := by
    intro hmem
    exact (List.nodup_append.mp hndFirst).2.2 _ hmem _ (by simp) rfl
  have hcompare := hfirstRot.symm.trans hlastRot
  rw [hfirst, hlast] at hcompare
  have hprefix := SourceUniverse.append_last_eq_of_isRotated hfresh hcompare
  have heq : stationary.rotate first = stationary.rotate last := by
    rw [← LiteralState.rotateLeft_eq_rotate, ← LiteralState.rotateLeft_eq_rotate, hfirst, hlast, hprefix]
  exact hnd.rotate_congr hne first last heq

theorem sweep_offset_equation (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : StrictMono cuts)
    (hnd : (render background resident cuts).Nodup)
    (previous target : Fin k) (mobile : α) (gap moves : Nat) (pre : List α)
    (hhead : ((render background resident cuts).rotateLeft gap).head? = some (resident previous))
    (hsuffix : fullIterate moves ((render background resident cuts).rotateLeft gap ++ [mobile]) =
      pre ++ [resident target, background (cuts target), mobile]) :
    ((cuts previous).val + previous.val + moves) % (render background resident cuts).length =
      ((cuts target).val + target.val + 2) % (render background resident cuts).length := by
  have hne : render background resident cuts ≠ [] := by
    intro hnil
    simp [hnil] at hhead
  have hstart := rotateLeft_eq_of_head_eq (render background resident cuts) hnd hne gap
    ((cuts previous).val + previous.val)
    (hhead.trans (resident_offset background resident cuts hcuts previous).symm)
  have hactual : (render background resident cuts).rotateLeft
      ((cuts previous).val + previous.val + moves) = pre ++ [resident target, background (cuts target)] := by
    rw [fullIterate_formula, hstart, rotateLeft_add] at hsuffix
    exact List.append_cancel_right (by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hsuffix)
  obtain ⟨desiredPre, hdesired⟩ := target_suffix_offset background resident cuts hcuts target
  apply suffix_rotation_mod (render background resident cuts) hnd _ _
    (pre ++ [resident target]) (desiredPre ++ [resident target]) (background (cuts target))
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hactual
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hdesired

theorem forward_difference (length start target moves : Nat)
    (hstart : start < length) (htarget : target < length) (hmoves : moves < length)
    (hmod : (start + moves) % length = target) :
    moves = if start ≤ target then target - start else length + target - start := by
  by_cases hsum : start + moves < length
  · rw [Nat.mod_eq_of_lt hsum] at hmod
    have hle : start ≤ target := by omega
    rw [if_pos hle]
    omega
  · have hsub : start + moves - length < length := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsub] at hmod
    have hlt : ¬ start ≤ target := by omega
    rw [if_neg hlt]
    omega

/-- Exact proper sweep length for any increasing physical cut vector. -/
theorem sweep_length (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : StrictMono cuts)
    (hnd : (render background resident cuts).Nodup)
    (previous target : Fin k) (mobile : α) (gap moves : Nat) (pre : List α)
    (hstart : (cuts previous).val + previous.val < (render background resident cuts).length)
    (htarget : (cuts target).val + target.val + 2 < (render background resident cuts).length)
    (hmoves : moves < (render background resident cuts).length)
    (hhead : ((render background resident cuts).rotateLeft gap).head? = some (resident previous))
    (hsuffix : fullIterate moves ((render background resident cuts).rotateLeft gap ++ [mobile]) =
      pre ++ [resident target, background (cuts target), mobile]) :
    moves = if (cuts previous).val + previous.val ≤ (cuts target).val + target.val + 2
      then (cuts target).val + target.val + 2 - ((cuts previous).val + previous.val)
      else (render background resident cuts).length + (cuts target).val + target.val + 2 -
        ((cuts previous).val + previous.val) := by
  have h := sweep_offset_equation background resident cuts hcuts hnd previous target mobile gap moves pre hhead hsuffix
  rw [Nat.mod_eq_of_lt htarget] at h
  simpa only [Nat.add_assoc] using forward_difference _ _ _ _ hstart htarget hmoves h

end CoefficientTwoPrecision.SweepOffsets

#print axioms CoefficientTwoPrecision.SweepOffsets.sweep_offset_equation
#print axioms CoefficientTwoPrecision.SweepOffsets.sweep_length
