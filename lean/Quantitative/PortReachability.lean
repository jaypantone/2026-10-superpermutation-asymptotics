import Quantitative.SafeConnectors
import Mathlib.Data.Int.GCD

/-!
# Reaching the prescribed source port within one port orbit

The period formula alone does not show that each permitted residue is
visited. The Bezout argument below constructs a hit and then reduces its
iteration index modulo the proved minimal period. This includes negative
and zero signed displacements.
-/

namespace CoefficientTwoPrecision.PortReachability

open SuperpermutationUpperBound.Transport

/-- Every port in the same gcd residue class is reached within one minimal
orbit of the actual signed port translation. -/
theorem exists_bounded_hit (h : Nat) (d : Int) (p q : Fin (h + 1))
    (hres : (Nat.gcd (h + 1) d.natAbs : Int) ∣ (q.val : Int) - p.val) :
    ∃ k < (h + 1) / Nat.gcd (h + 1) d.natAbs,
      (shiftPort h d)^[k] p = q := by
  let n : Int := ((h + 1 : Nat) : Int)
  let g := Nat.gcd (h + 1) d.natAbs
  have hn : 0 < n := by dsimp [n]; omega
  have hbez : (g : Int) = n * Int.gcdA n d + d * Int.gcdB n d := by
    simpa only [g, n, Int.gcd_def, Int.natAbs_natCast] using Int.gcd_eq_gcd_ab n d
  obtain ⟨c, hc⟩ := hres
  let t : Int := c * Int.gcdB n d
  let k0 : Nat := (t % n).toNat
  have hk0 : (k0 : Int) = t % n := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hcoeff : (q.val : Int) - p.val = n * (c * Int.gcdA n d) + d * t := by
    rw [hc]
    change (g : Int) * c = _
    rw [hbez]
    dsimp only [t]
    ring
  have hdiff : t - (k0 : Int) = n * (t / n) := by
    rw [hk0]
    have hd := Int.emod_add_mul_ediv t n
    omega
  have hmod : Int.ModEq n ((p.val : Int) + (k0 : Int) * d) q.val := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨c * Int.gcdA n d + (t / n) * d, ?_⟩
    calc
      (q.val : Int) - ((p.val : Int) + (k0 : Int) * d)
          = ((q.val : Int) - p.val) - (k0 : Int) * d := by ring
      _ = n * (c * Int.gcdA n d) + d * (t - (k0 : Int)) := by rw [hcoeff]; ring
      _ = n * (c * Int.gcdA n d + (t / n) * d) := by rw [hdiff]; ring
  have hhit : (shiftPort h d)^[k0] p = q := by
    rw [shiftPort_iterate]
    apply Fin.ext
    apply Int.ofNat_inj.mp
    rw [shiftPort_val]
    have hq : (q.val : Int) % n = q.val := Int.emod_eq_of_lt (by omega) (by
      have := q.isLt
      dsimp [n]
      omega)
    change ((p.val : Int) + (k0 : Int) * d) % n = q.val
    exact (show ((p.val : Int) + (k0 : Int) * d) % n = (q.val : Int) % n from hmod).trans hq
  have hperiod : 0 < Function.minimalPeriod (shiftPort h d) p :=
    Function.minimalPeriod_pos_of_mem_periodicPts
      ((shiftPortPerm h d).injective.mem_periodicPts p)
  refine ⟨k0 % Function.minimalPeriod (shiftPort h d) p, ?_, ?_⟩
  · rw [← shiftPort_minimalPeriod h d p]
    exact Nat.mod_lt _ hperiod
  · rw [Function.iterate_mod_minimalPeriod_eq]
    exact hhit

end CoefficientTwoPrecision.PortReachability

#print axioms CoefficientTwoPrecision.PortReachability.exists_bounded_hit
