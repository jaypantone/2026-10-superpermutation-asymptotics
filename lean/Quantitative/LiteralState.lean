import Quantitative.JointStates
import Mathlib.Data.List.Rotate

/-!
# Literal full and short moves

The short move is implemented as a total list operation and evaluated on
every list ending in the resident, crossed background symbol, and mobile.
The resulting equality exhibits the actual new resident and mobile. The
full-move iteration retains one stationary circle and only rotates its
representative. A nodup stationary circle has a unique representative with
a specified first resident, which is the endpoint reconstruction fact
needed after the cleanup batch.

These lemmas do not yet construct the stationary circle from modular cuts
or prove that every scheduled target has the required suffix. Those are
explicitly separate geometric obligations.
-/

namespace CoefficientTwoPrecision.LiteralState

open PositiveParking
open JointStates
open scoped List

/-- The short map moves the last symbol to the front, and exchanges the
preceding two symbols. On lists shorter than three this total definition
is only a convention; the theorems below use the required three-symbol suffix. -/
def shortStep {α : Type} (base : List α) : List α :=
  base.getLast?.toList ++ base.take (base.length - 3) ++
    base.dropLast.getLast?.toList ++ base.dropLast.dropLast.getLast?.toList

theorem shortStep_suffix {α : Type} (pre : List α) (resident crossed mobile : α) :
    shortStep (pre ++ [resident, crossed, mobile]) =
      mobile :: (pre ++ [crossed, resident]) := by
  have hlast : pre ++ [resident, crossed, mobile] =
      ((pre ++ [resident]) ++ [crossed]) ++ [mobile] := by
    simp [List.append_assoc]
  rw [hlast]
  simp [shortStep, List.append_assoc]

/-- The literal short map uses exactly the two new role labels supplied
by the star-transposition update. -/
theorem shortStep_roles {α : Type} (pre : List α) (crossed : α)
    (labels : Option Nat → α) (target : Nat) :
    shortStep (pre ++ [labels (some target), crossed, labels none]) =
      updateLabels target labels (some target) ::
        (pre ++ [crossed, updateLabels target labels none]) := by
  simpa only [updateLabels, star_target, star_mobile] using
    shortStep_suffix pre (labels (some target)) crossed (labels none)

/-- No symbol is added, lost, or duplicated by a short move with the
specified suffix. -/
theorem shortStep_perm {α : Type} (pre : List α) (resident crossed mobile : α) :
    (shortStep (pre ++ [resident, crossed, mobile])).Perm
      (pre ++ [resident, crossed, mobile]) := by
  rw [shortStep_suffix]
  calc
    mobile :: (pre ++ [crossed, resident]) ~
        (pre ++ [crossed, resident]) ++ [mobile] := by
      simpa using
        (List.perm_append_comm :
          [mobile] ++ (pre ++ [crossed, resident]) ~
            (pre ++ [crossed, resident]) ++ [mobile])
    _ ~ pre ++ [resident, crossed, mobile] := by
      simpa [List.append_assoc] using
        List.Perm.append_left pre (List.Perm.swap resident crossed [mobile])

theorem shortStep_nodup {α : Type} (pre : List α) (resident crossed mobile : α)
    (h : (pre ++ [resident, crossed, mobile]).Nodup) :
    (shortStep (pre ++ [resident, crossed, mobile])).Nodup :=
  (shortStep_perm pre resident crossed mobile).nodup_iff.mpr h

/-- Deleting the two control symbols preserves the remaining literal
background order in this suffix presentation. -/
theorem shortStep_background {α : Type} (pre : List α) (resident crossed mobile : α)
    (keep : α → Bool) (hr : keep resident = false) (hm : keep mobile = false) :
    (shortStep (pre ++ [resident, crossed, mobile])).filter keep =
      (pre ++ [resident, crossed, mobile]).filter keep := by
  rw [shortStep_suffix]
  simp [List.filter_append, List.filter_cons, hr, hm]

/-- After a short update, the new mobile is the old resident and the first
stationary symbol is the old mobile, now resident at the updated target. -/
theorem shortStep_post_update_data {α : Type} (pre : List α)
    (resident crossed mobile : α) :
    (shortStep (pre ++ [resident, crossed, mobile])).getLast? = some resident ∧
      (shortStep (pre ++ [resident, crossed, mobile])).dropLast =
        mobile :: (pre ++ [crossed]) := by
  rw [shortStep_suffix]
  have hform : mobile :: (pre ++ [crossed, resident]) =
      (mobile :: (pre ++ [crossed])) ++ [resident] := by
    simp [List.append_assoc]
  rw [hform]
  constructor
  · exact List.getLast?_concat
  · exact List.dropLast_concat

/-- Compatibility between Lean's literal rotation operation and Mathlib's
list rotation. Both use reduction modulo the list length. -/
theorem rotateLeft_eq_rotate {α : Type} (l : List α) (n : Nat) :
    l.rotateLeft n = l.rotate n := by
  by_cases h : l.length ≤ 1
  · cases l with
    | nil => simp
    | cons a rest =>
      cases rest with
      | nil => simp [List.rotateLeft]
      | cons b rest => simp at h
  · simp only [List.rotateLeft, h, ↓reduceIte]
    exact List.rotate_eq_drop_append_take_mod.symm

theorem rotateLeft_add {α : Type} (stationary : List α) (i j : Nat) :
    (stationary.rotateLeft i).rotateLeft j = stationary.rotateLeft (i + j) := by
  simp only [rotateLeft_eq_rotate, List.rotate_rotate]

def fullIterate {α : Type} : Nat → List α → List α
  | 0, base => base
  | n + 1, base => literalFullStep (fullIterate n base)

/-- All actual intermediate full rows use the same stationary circle
and mobile; only the insertion gap changes. -/
theorem fullIterate_formula {α : Type} (stationary : List α) (mobile : α) (n : Nat) :
    fullIterate n (stationary ++ [mobile]) = stationary.rotateLeft n ++ [mobile] := by
  induction n with
  | zero => simp [fullIterate]
  | succ n ih =>
    rw [fullIterate, ih, literalFullStep_mobile_last, rotateLeft_add]

/-- Distinct gap indices below one stationary circuit give distinct
literal bases. The geometric simplicity proof additionally compares cyclic bases. -/
theorem fullIterate_injective_before_circuit {α : Type} (stationary : List α)
    (mobile : α) (hnodup : stationary.Nodup) (i j : Nat)
    (hi : i < stationary.length) (hj : j < stationary.length)
    (heq : fullIterate i (stationary ++ [mobile]) =
      fullIterate j (stationary ++ [mobile])) : i = j := by
  rw [fullIterate_formula, fullIterate_formula] at heq
  have hrot : stationary.rotateLeft i = stationary.rotateLeft j :=
    List.append_cancel_right heq
  rw [rotateLeft_eq_rotate, rotateLeft_eq_rotate] at hrot
  have hne : stationary ≠ [] := by
    intro h
    simp [h] at hi
  have hmod := hnodup.rotate_congr hne i j hrot
  simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hmod

/-- A nodup stationary circle has at most one rotated representative
whose first symbol is a specified resident. -/
theorem rotateLeft_eq_of_head_eq {α : Type} (stationary : List α)
    (hnodup : stationary.Nodup) (hne : stationary ≠ []) (i j : Nat)
    (hhead : (stationary.rotateLeft i).head? = (stationary.rotateLeft j).head?) :
    stationary.rotateLeft i = stationary.rotateLeft j := by
  rw [rotateLeft_eq_rotate, rotateLeft_eq_rotate] at hhead ⊢
  have hlen : 0 < stationary.length := List.length_pos_iff.mpr hne
  have hi : i % stationary.length < stationary.length := Nat.mod_lt i hlen
  have hj : j % stationary.length < stationary.length := Nat.mod_lt j hlen
  have hheads : (stationary.rotate (i % stationary.length)).head? =
      (stationary.rotate (j % stationary.length)).head? := by
    simpa only [List.rotate_mod] using hhead
  rw [List.head?_rotate hi, List.head?_rotate hj] at hheads
  have hmod : i % stationary.length = j % stationary.length :=
    (List.Nodup.getElem?_inj hi hnodup).mp hheads
  exact hnodup.rotate_congr_iff.mpr (Or.inl hmod)

/-- Equal stationary circles, mobile labels, and final resident labels
determine equal literal post-update bases. This is the endpoint condition
used after a normal cleanup batch. -/
theorem post_update_base_unique {α : Type} (stationary : List α)
    (hnodup : stationary.Nodup) (hne : stationary ≠ [])
    (mobile resident : α) (i j : Nat)
    (hi : (stationary.rotateLeft i).head? = some resident)
    (hj : (stationary.rotateLeft j).head? = some resident) :
    stationary.rotateLeft i ++ [mobile] = stationary.rotateLeft j ++ [mobile] := by
  rw [rotateLeft_eq_of_head_eq stationary hnodup hne i j (hi.trans hj.symm)]

end CoefficientTwoPrecision.LiteralState

#print axioms CoefficientTwoPrecision.LiteralState.shortStep_roles
#print axioms CoefficientTwoPrecision.LiteralState.shortStep_background
#print axioms CoefficientTwoPrecision.LiteralState.fullIterate_formula
#print axioms CoefficientTwoPrecision.LiteralState.fullIterate_injective_before_circuit
#print axioms CoefficientTwoPrecision.LiteralState.post_update_base_unique
