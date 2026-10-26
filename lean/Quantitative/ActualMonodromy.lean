import Quantitative.TraceDisplacement
import Quantitative.SourceAdvancement
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Basic

/-!
# The actual source monodromy has at most k components

The signed displacement of the emitted rows is their actual total charge
minus their actual number. The literal background-position calculation
shows that this displacement is k modulo the stationary length. Hence
the gcd used by the checked source advancement is exactly gcd(h+1,k).
-/

namespace CoefficientTwoPrecision.ActualMonodromy

open LiteralSchedule PositiveSchedule TargetTrace RowValidity TraceDisplacement
open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SourceAdvancement

variable {M k : Nat}

theorem gcd_eq_of_residue (h k : Nat) (d : Int) (hresidue : (d : ZMod h) = k) :
    Nat.gcd h d.natAbs = Nat.gcd h k := by
  have hmod : d % (h : Int) = (k : Int) % (h : Int) :=
    (ZMod.intCast_eq_intCast_iff' d (k : Int) h).mp (by simpa only [Int.cast_natCast] using hresidue)
  have hg : Int.gcd (h : Int) d = Int.gcd (h : Int) (k : Int) := by
    calc
      Int.gcd (h : Int) d = Int.gcd d (h : Int) := Int.gcd_comm _ _
      _ = Int.gcd (d % (h : Int)) (h : Int) := (Int.gcd_emod _ _).symm
      _ = Int.gcd ((k : Int) % (h : Int)) (h : Int) := by rw [hmod]
      _ = Int.gcd (k : Int) (h : Int) := Int.gcd_emod _ _
      _ = Int.gcd (h : Int) (k : Int) := Int.gcd_comm _ _
  simpa only [Int.gcd_def, Int.natAbs_natCast] using hg

theorem trace_rows_signed_excess {α : Type} (hM : 2 ≤ M)
    (background : Fin M → α) (word : List (Fin k)) (labels : Option Nat → α)
    (cuts : Fin k → Fin M) (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background word labels cuts gap sweeps finalGap) (satellite : α) :
    ((scheduleRows satellite sweeps (renderedBase background labels cuts gap)).map delta).sum =
      (sweeps.length : Int) - sweeps.sum := by
  have hsize := render_length_ge_background background (residents labels) cuts
  have hbaseLength : 2 ≤ (renderedBase background labels cuts gap).length := by
    simp only [renderedBase, List.length_append, List.length_singleton,
      LiteralState.rotateLeft_eq_rotate, List.length_rotate]
    omega
  rw [sum_delta, scheduleRows_charge satellite sweeps _
    (trace_suffixSchedule hM background word labels cuts gap sweeps finalGap htrace) hbaseLength,
    scheduleRows_length]
  push_cast
  ring

/-- The modulus in SourceAdvancement is h+1. It is the stationary list
length, one less than the base length. -/
theorem actual_portGcd [NeZero M] (hM : 2 ≤ M) (h : Nat)
    (background : Fin M → Nat) (hbackground : Function.Injective background) (tracked : Fin M)
    (word : List (Fin k)) (labels : Option Nat → Nat) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background word labels cuts gap sweeps finalGap)
    (hlen : (StationaryCircle.render background (residents labels) cuts).length = h + 1)
    (hnd : (renderedBase background labels cuts gap).Nodup)
    (havoid : Avoids (k := k) labels (background tracked))
    (hcounts : ∀ target, word.count target = M)
    (hclosed : scheduleEnd sweeps (renderedBase background labels cuts gap) =
      renderedBase background labels cuts gap) (satellite : Nat) :
    portGcd (scheduleRows satellite sweeps (renderedBase background labels cuts gap)) h =
      Nat.gcd (h + 1) k := by
  have hresidue := closed_trace_excess hM (h + 1) background hbackground tracked word labels cuts gap
    sweeps finalGap htrace hlen hnd havoid hcounts hclosed
  unfold portGcd
  apply gcd_eq_of_residue
  rw [trace_rows_signed_excess hM background word labels cuts gap sweeps finalGap htrace satellite]
  simpa only [Int.cast_sub, Int.cast_natCast] using hresidue

theorem actual_portGcd_le [NeZero M] (hM : 2 ≤ M) (hk : 0 < k) (h : Nat)
    (background : Fin M → Nat) (hbackground : Function.Injective background) (tracked : Fin M)
    (word : List (Fin k)) (labels : Option Nat → Nat) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background word labels cuts gap sweeps finalGap)
    (hlen : (StationaryCircle.render background (residents labels) cuts).length = h + 1)
    (hnd : (renderedBase background labels cuts gap).Nodup)
    (havoid : Avoids (k := k) labels (background tracked))
    (hcounts : ∀ target, word.count target = M)
    (hclosed : scheduleEnd sweeps (renderedBase background labels cuts gap) =
      renderedBase background labels cuts gap) (satellite : Nat) :
    portGcd (scheduleRows satellite sweeps (renderedBase background labels cuts gap)) h ≤ k := by
  rw [actual_portGcd hM h background hbackground tracked word labels cuts gap sweeps finalGap
    htrace hlen hnd havoid hcounts hclosed satellite]
  exact Nat.le_of_dvd hk (Nat.gcd_dvd_right _ _)

end CoefficientTwoPrecision.ActualMonodromy

#print axioms CoefficientTwoPrecision.ActualMonodromy.actual_portGcd
#print axioms CoefficientTwoPrecision.ActualMonodromy.actual_portGcd_le
