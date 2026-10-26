import Quantitative.BackgroundPosition
import Quantitative.CrossingInventory

/-!
# Summing literal background displacement along the actual trace

The same recursively constructed sweep list determines the literal
endpoint, emitted rows, and exceptional crossings. The position identity
therefore combines without an identification of unrelated witnesses.
-/

namespace CoefficientTwoPrecision.TraceDisplacement

open PositiveParking LiteralState StationaryCircle StationaryUpdate LiteralSchedule
open PositiveSchedule TargetTrace RowValidity BackgroundPosition CrossingInventory

variable {M k : Nat} {α : Type} [DecidableEq α]

def Avoids (labels : Option Nat → α) (symbol : α) : Prop :=
  labels none ≠ symbol ∧ ∀ j : Fin k, residents labels j ≠ symbol

theorem avoids_update (target : Fin k) (labels : Option Nat → α) (symbol : α)
    (h : Avoids (k := k) labels symbol) : Avoids (k := k) (updateLabels target.val labels) symbol := by
  constructor
  · exact h.2 target
  · intro j
    by_cases hj : j = target
    · subst j
      simpa only [residents, updateLabels, star_target] using h.1
    · have hv : j.val ≠ target.val := fun heq => hj (Fin.ext heq)
      simpa only [residents, updateLabels, star_other target.val j.val hv] using h.2 j

theorem trace_position (hM : 2 ≤ M) (h : Nat)
    (background : Fin M → α) (hbackground : Function.Injective background) (tracked : Fin M)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background word labels cuts gap sweeps finalGap)
    (hlen : (render background (residents labels) cuts).length = h)
    (hnd : (renderedBase background labels cuts gap).Nodup)
    (havoid : Avoids (k := k) labels (background tracked)) :
    position h (background tracked) (scheduleEnd sweeps (renderedBase background labels cuts gap)) =
      position h (background tracked) (renderedBase background labels cuts gap) - sweeps.sum +
        sweeps.length - ((crossings (show 0 < M by omega) word cuts).map Prod.snd).count tracked := by
  induction word generalizing labels cuts gap sweeps with
  | nil =>
    obtain ⟨rfl, _⟩ := htrace
    simp [scheduleEnd, crossings]
  | cons target word ih =>
    obtain ⟨moves, rest, nextGap, pre, rfl, _, hpre, hnext, hrest⟩ := htrace
    have hmem : background tracked ∈ (render background (residents labels) cuts).rotateLeft gap := by
      rw [LiteralState.rotateLeft_eq_rotate, List.mem_rotate]
      exact (mem_render background (residents labels) cuts (background tracked)).mpr (Or.inl ⟨tracked, rfl⟩)
    have hfirst := update_position h ((render background (residents labels) cuts).rotateLeft gap)
      (labels none) (background tracked)
      (by simpa only [LiteralState.rotateLeft_eq_rotate, List.length_rotate] using hlen)
      hnd hmem moves pre (residents labels target) (background (cuts target)) (havoid.2 target) havoid.1 hpre
    have hperm := updateEnd_perm (renderedBase background labels cuts gap) moves
      ⟨(render background (residents labels) cuts).rotateLeft gap, labels none, rfl⟩
      ⟨pre, residents labels target, background (cuts target), labels none, hpre⟩
    have hnextNodup := hperm.nodup_iff.mpr hnd
    rw [hnext] at hnextNodup
    have hnextLength :
        (render background (residents (updateLabels target.val labels))
          (advanceCuts (show 0 < M by omega) target cuts)).length = h := by
      have hp := hperm.length_eq
      rw [hnext] at hp
      simp only [renderedBase, List.length_append, List.length_singleton,
        LiteralState.rotateLeft_eq_rotate, List.length_rotate, hlen] at hp
      omega
    have htail := ih (updateLabels target.val labels) (advanceCuts (show 0 < M by omega) target cuts)
      nextGap rest hrest hnextLength hnextNodup (avoids_update target labels _ havoid)
    change position h (background tracked)
      (scheduleEnd rest (updateEnd moves (renderedBase background labels cuts gap))) = _
    rw [hnext, htail]
    change position h (background tracked) (updateEnd moves (renderedBase background labels cuts gap)) = _ at hfirst
    rw [hnext] at hfirst
    rw [hfirst]
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_succ, crossings,
      List.map_cons, renderedBase]
    by_cases heq : cuts target = tracked
    · rw [heq]
      simp only [ite_true, List.count_cons_self, Nat.cast_add, Nat.cast_one]
      ring
    · have hne : background (cuts target) ≠ background tracked := fun heq' => heq (hbackground heq')
      rw [if_neg hne, List.count_cons_of_ne heq]
      ring

/-- Literal closure and the exact crossing inventory force the residue
of the signed row excess; no return-map assumption is supplied. -/
theorem closed_trace_excess [NeZero M] (hM : 2 ≤ M) (h : Nat)
    (background : Fin M → α) (hbackground : Function.Injective background) (tracked : Fin M)
    (word : List (Fin k)) (labels : Option Nat → α) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background word labels cuts gap sweeps finalGap)
    (hlen : (render background (residents labels) cuts).length = h)
    (hnd : (renderedBase background labels cuts gap).Nodup)
    (havoid : Avoids (k := k) labels (background tracked))
    (hcounts : ∀ target, word.count target = M)
    (hclosed : scheduleEnd sweeps (renderedBase background labels cuts gap) =
      renderedBase background labels cuts gap) :
    (sweeps.length : ZMod h) - sweeps.sum = k := by
  have hp := trace_position hM h background hbackground tracked word labels cuts gap sweeps finalGap
    htrace hlen hnd havoid
  rw [hclosed, complete_background_count word cuts hcounts tracked] at hp
  linear_combination -hp

end CoefficientTwoPrecision.TraceDisplacement

#print axioms CoefficientTwoPrecision.TraceDisplacement.trace_position
#print axioms CoefficientTwoPrecision.TraceDisplacement.closed_trace_excess
