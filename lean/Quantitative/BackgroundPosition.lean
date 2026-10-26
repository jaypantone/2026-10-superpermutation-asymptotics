import Quantitative.RowValidity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Literal displacement of a fixed background symbol

Positions are read modulo the stationary length h, while a literal base
has h+1 symbols. A full move subtracts one. A short move adds one unless
the fixed background symbol is the crossed symbol; that exceptional
symbol keeps its position. These are identities for the actual list
operations, obtained from their explicit suffix formulas.
-/

namespace CoefficientTwoPrecision.BackgroundPosition

open LiteralState LiteralSchedule RowValidity

variable {α : Type} [DecidableEq α]

def position (h : Nat) (symbol : α) (base : List α) : ZMod h := (base.idxOf symbol : Nat)

theorem rotate_one_position (h : Nat) (stationary : List α) (symbol : α)
    (hlen : stationary.length = h) (hnd : stationary.Nodup) (hmem : symbol ∈ stationary) :
    position h symbol (stationary.rotateLeft 1) = position h symbol stationary - 1 := by
  cases stationary with
  | nil => simp at hmem
  | cons first rest =>
    rw [LiteralState.rotateLeft_eq_rotate, List.rotate_cons_succ, List.rotate_zero]
    by_cases heq : first = symbol
    · subst first
      have hnot : symbol ∉ rest := (List.nodup_cons.mp hnd).1
      unfold position
      rw [List.idxOf_append_of_notMem hnot, List.idxOf_cons_self, List.idxOf_cons_self, Nat.add_zero]
      have hcast : (rest.length : ZMod h) + 1 = 0 := by
        have hc := congrArg (fun n : Nat => (n : ZMod h)) hlen
        simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, ZMod.natCast_self] using hc
      linear_combination hcast
    · have htail : symbol ∈ rest := (List.mem_cons.mp hmem).resolve_left (Ne.symm heq)
      unfold position
      rw [List.idxOf_append_of_mem htail, List.idxOf_cons_ne rest heq, Nat.cast_succ]
      ring

theorem rotate_position (h : Nat) (stationary : List α) (symbol : α)
    (hlen : stationary.length = h) (hnd : stationary.Nodup) (hmem : symbol ∈ stationary) (moves : Nat) :
    position h symbol (stationary.rotateLeft moves) = position h symbol stationary - moves := by
  induction moves with
  | zero => simp [LiteralState.rotateLeft_eq_rotate]
  | succ moves ih =>
    rw [← rotateLeft_add]
    have hnd' : (stationary.rotateLeft moves).Nodup := by
      rw [LiteralState.rotateLeft_eq_rotate]
      exact (List.rotate_perm stationary moves).nodup_iff.mpr hnd
    have hmem' : symbol ∈ stationary.rotateLeft moves := by
      rw [LiteralState.rotateLeft_eq_rotate, List.mem_rotate]
      exact hmem
    rw [rotate_one_position h _ symbol
      (by simpa only [LiteralState.rotateLeft_eq_rotate, List.length_rotate] using hlen) hnd' hmem', ih,
      Nat.cast_succ]
    ring

theorem full_position (h : Nat) (stationary : List α) (mobile symbol : α)
    (hlen : stationary.length = h) (hnd : stationary.Nodup) (hmem : symbol ∈ stationary) (moves : Nat) :
    position h symbol (fullIterate moves (stationary ++ [mobile])) =
      position h symbol (stationary ++ [mobile]) - moves := by
  rw [fullIterate_formula]
  have hmem' : symbol ∈ stationary.rotateLeft moves := by
    rw [LiteralState.rotateLeft_eq_rotate, List.mem_rotate]
    exact hmem
  unfold position
  rw [List.idxOf_append_of_mem hmem', List.idxOf_append_of_mem hmem]
  exact rotate_position h stationary symbol hlen hnd hmem moves

theorem short_position (h : Nat) (pre : List α) (resident crossed mobile symbol : α)
    (hnd : (pre ++ [resident, crossed, mobile]).Nodup)
    (hmem : symbol ∈ pre ++ [resident, crossed, mobile])
    (hresident : resident ≠ symbol) (hmobile : mobile ≠ symbol) :
    position h symbol (shortStep (pre ++ [resident, crossed, mobile])) =
      position h symbol (pre ++ [resident, crossed, mobile]) + 1 -
        (if crossed = symbol then 1 else 0) := by
  rw [shortStep_suffix]
  by_cases hcrossed : crossed = symbol
  · subst crossed
    have hnot : symbol ∉ pre := by
      intro hpre
      exact (List.nodup_append.mp hnd).2.2 symbol hpre symbol (by simp) rfl
    unfold position
    rw [List.idxOf_cons_ne _ hmobile, List.idxOf_append_of_notMem hnot,
      List.idxOf_append_of_notMem hnot]
    simp only [List.idxOf_cons_self, List.idxOf_cons_ne _ hresident, Nat.cast_succ,
      Nat.cast_add, Nat.cast_zero, add_zero, ite_true]
    ring
  · have hpre : symbol ∈ pre := by
      rcases List.mem_append.mp hmem with hpre | htail
      · exact hpre
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at htail
        rcases htail with heq | heq | heq
        · exact False.elim (hresident heq.symm)
        · exact False.elim (hcrossed heq.symm)
        · exact False.elim (hmobile heq.symm)
    unfold position
    rw [List.idxOf_cons_ne _ hmobile, List.idxOf_append_of_mem hpre,
      List.idxOf_append_of_mem hpre]
    simp only [if_neg hcrossed, Nat.cast_succ, sub_zero]

/-- The full sweep and its following actual short operation have this
combined displacement. -/
theorem update_position (h : Nat) (stationary : List α) (mobile symbol : α)
    (hlen : stationary.length = h) (hnd : (stationary ++ [mobile]).Nodup)
    (hmem : symbol ∈ stationary) (moves : Nat) (pre : List α) (resident crossed : α)
    (hresident : resident ≠ symbol) (hmobile : mobile ≠ symbol)
    (hsuffix : fullIterate moves (stationary ++ [mobile]) = pre ++ [resident, crossed, mobile]) :
    position h symbol (updateEnd moves (stationary ++ [mobile])) =
      position h symbol (stationary ++ [mobile]) - moves + 1 -
        (if crossed = symbol then 1 else 0) := by
  have hperm := fullIterate_perm stationary mobile moves
  have hnd' := hperm.nodup_iff.mpr hnd
  have hmem' : symbol ∈ fullIterate moves (stationary ++ [mobile]) :=
    hperm.mem_iff.mpr (List.mem_append_left _ hmem)
  rw [hsuffix] at hnd' hmem'
  have hshort := short_position h pre resident crossed mobile symbol hnd' hmem' hresident hmobile
  have hfull := full_position h stationary mobile symbol hlen (List.nodup_append.mp hnd).1 hmem moves
  rw [hsuffix] at hfull
  rw [updateEnd, hsuffix, hshort, hfull]

end CoefficientTwoPrecision.BackgroundPosition

#print axioms CoefficientTwoPrecision.BackgroundPosition.full_position
#print axioms CoefficientTwoPrecision.BackgroundPosition.short_position
#print axioms CoefficientTwoPrecision.BackgroundPosition.update_position
