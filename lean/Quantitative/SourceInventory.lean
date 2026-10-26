import Quantitative.SourceAdvancement

/-!
# Actual transport inventory for the canonical source components

Coverage of every port together with the exact total list length proves
that the canonical port orbits partition the ports. This retains every
occurrence and does not require the literal row values to be distinct.
-/

namespace CoefficientTwoPrecision.SourceInventory

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371
open CoefficientTwoPrecision.SourceAdvancement CoefficientTwoPrecision.PortReachability

def seedPort (source : List (Row Nat)) (h : Nat) (e : Fin (portGcd source h)) : Fin (h + 1) :=
  ⟨e.val, lt_of_lt_of_le e.isLt (portGcd_le source h)⟩

def canonicalLabels (source : List (Row Nat)) (h : Nat) : List (Fin (h + 1)) :=
  (List.finRange (portGcd source h)).flatMap (fun e =>
    orbitLabels (shiftPort h (source.map delta).sum) (seedPort source h e) (orbitLaps source h))

theorem canonicalLabels_length (source : List (Row Nat)) (h : Nat) :
    (canonicalLabels source h).length = h + 1 := by
  simp only [canonicalLabels, List.length_flatMap, orbitLabels_length]
  rw [List.map_const', List.sum_replicate_nat, List.length_finRange]
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)

theorem canonicalLabels_covers (source : List (Row Nat)) (h : Nat) (q : Fin (h + 1)) :
    q ∈ canonicalLabels source h := by
  let e : Fin (portGcd source h) := ⟨q.val % portGcd source h,
    Nat.mod_lt _ (portGcd_pos source h)⟩
  have hres : (portGcd source h : Int) ∣ (q.val : Int) - (seedPort source h e).val := by
    have hm : Int.ModEq (portGcd source h : Int)
        ((q.val % portGcd source h : Nat) : Int) q.val :=
      Int.natCast_modEq_iff.mpr (Nat.mod_modEq q.val (portGcd source h))
    exact hm.dvd
  obtain ⟨k, hk, hhit⟩ := exists_bounded_hit h (source.map delta).sum (seedPort source h e) q hres
  refine List.mem_flatMap.mpr ⟨e, List.mem_finRange e, ?_⟩
  rw [orbitLabels_eq_map_iterate]
  exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, hhit⟩

/-- Canonical port orbits are a true occurrence partition of all old ports. -/
theorem canonicalLabels_perm (source : List (Row Nat)) (h : Nat) :
    (canonicalLabels source h).Perm (List.finRange (h + 1)) := by
  apply List.Perm.symm
  apply perm_of_nodup_subset_length (nodup_finRange _)
    (fun q _ => canonicalLabels_covers source h q)
  rw [List.length_finRange, canonicalLabels_length]

theorem orbitPorts_eq_labels (source : List (Row Nat)) (h k : Nat)
    (hn : 3 ≤ h + 2) (hlen : ∀ r ∈ source, r.base.length = h + 2)
    (hkind : ∀ r ∈ source,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (e : Fin (h + 1)) :
    orbitPorts source k e.val =
      (orbitLabels (shiftPort h (source.map delta).sum) e k).map Fin.val := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    rw [orbitPorts, orbitLabels, List.map_cons,
      completionExit_eq_shift source h hn hlen hkind e, ih]

theorem orbitPorts_partition (source : List (Row Nat)) (h : Nat)
    (hn : 3 ≤ h + 2) (hlen : ∀ r ∈ source, r.base.length = h + 2)
    (hkind : ∀ r ∈ source,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((List.range (portGcd source h)).flatMap
      (orbitPorts source (orbitLaps source h))).Perm (List.range (h + 1)) := by
  have hp := (canonicalLabels_perm source h).map Fin.val
  rw [map_val_finRange] at hp
  have he : ((List.range (portGcd source h)).flatMap
      (orbitPorts source (orbitLaps source h))) = (canonicalLabels source h).map Fin.val := by
    rw [← map_val_finRange (portGcd source h), List.flatMap_map]
    simp only [canonicalLabels, List.map_flatMap]
    rw [List.flatMap_def, List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro e he
    exact orbitPorts_eq_labels source h (orbitLaps source h) hn hlen hkind (seedPort source h e)
  rw [he]
  exact hp

/-- The chosen advanced components contain exactly the actual transported
row occurrences, with their full and short multiplicities. -/
theorem advancedComponents_inventory (source : List (Row Nat)) (z h : Nat)
    (hn : 3 ≤ h + 2) (hlen : ∀ r ∈ source, r.base.length = h + 2)
    (hkind : ∀ r ∈ source,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    (advancedComponents source z h).flatten.Perm (Transport.packingRows source z) := by
  have hp := (orbitPorts_partition source h hn hlen hkind).flatMap_right
    (fun p => transportWalk source z p)
  have hr := range_transportWalk_perm source z (h + 1) hn
    (fun r hr => by simpa only [Nat.add_assoc] using hlen r hr)
  have he : (advancedComponents source z h).flatten =
      ((List.range (portGcd source h)).flatMap
        (orbitPorts source (orbitLaps source h))).flatMap (fun p => transportWalk source z p) := by
    simp only [advancedComponents, ← List.flatMap_def, transportWalk_rep, List.flatMap_assoc]
  rw [he]
  exact hp.trans (by simpa only [List.flatMap_def] using hr)

theorem orbitLaps_pos (source : List (Row Nat)) (h : Nat) : 0 < orbitLaps source h := by
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts
    ((shiftPortPerm h (source.map delta).sum).injective.mem_periodicPts ⟨0, by omega⟩)
  change 0 < Function.minimalPeriod (shiftPort h (source.map delta).sum) ⟨0, by omega⟩ at hp
  rwa [shiftPort_minimalPeriod] at hp

theorem orbitLaps_winding (source : List (Row Nat)) (h : Nat) :
    ((h + 1 : Nat) : Int) ∣ (orbitLaps source h : Int) * signedExcess source := by
  have hp := (shiftPort_period_iff h (-(signedExcess source)) ⟨0, by omega⟩ _).mp
    (Function.isPeriodicPt_minimalPeriod _ _)
  rw [shiftPort_minimalPeriod] at hp
  simpa only [orbitLaps, portGcd, signedExcess_eq_neg_sum_delta, Int.neg_neg,
    Int.natAbs_neg, mul_neg, Int.dvd_neg] using hp

/-- Each actual component is closed and has divisible advanced signed excess. -/
theorem advancedComponents_closed (source : List (Row Nat)) (z h : Nat)
    (hc : ClosedTrail source) (hn : 3 ≤ h + 2)
    (hlen : ∀ r ∈ source, r.base.length = h + 2)
    (hkind : ∀ r ∈ source,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ∀ W ∈ advancedComponents source z h,
      ClosedTrail W ∧ ((h + 2 : Nat) : Int) ∣ signedExcess W := by
  intro W hW
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hW
  have he' : e < h + 1 := lt_of_lt_of_le (List.mem_range.mp he) (portGcd_le source h)
  have hh := transported_rep_closed hc (orbitLaps_pos source h) z (h + 1) hn
    (fun r hr => by simpa only [Nat.add_assoc] using hlen r hr) hkind
    (orbitLaps_winding source h) e he'
  simpa only [Nat.add_assoc] using hh

/-- The canonical component list is a Level on the actual enlarged alphabet. -/
theorem advancedLevel (source : List (Row Nat)) (A : List Nat) (z h : Nat)
    (hc : ClosedTrail source) (hA : A.length = h + 2) (hn : 3 ≤ h + 2)
    (hb : BasedOn A 9 source) (hz : z ∉ A) (hz9 : z ≠ 9) :
    Level (z :: A) (h + 2) (advancedComponents source z h) := by
  have hlen : ∀ r ∈ source, r.base.length = h + 2 :=
    fun r hr => (hb r hr).2.1.length_eq.trans hA
  have hkind : ∀ r ∈ source,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2 :=
    fun r hr => (hb r hr).2.2.2
  have hclosed := advancedComponents_closed source z h hc hn hlen hkind
  have hp := advancedComponents_inventory source z h hn hlen hkind
  refine ⟨fun W hW => (hclosed W hW).1, fun W hW => (hclosed W hW).2, ?_⟩
  intro W hW r hr
  have hm : r ∈ Transport.packingRows source z :=
    hp.mem_iff.mp (List.mem_flatten.mpr ⟨W, hW, hr⟩)
  exact hb.transport hz hz9 r hm

theorem advancedCounts (source : List (Row Nat)) (A : List Nat) (z h : Nat)
    (hA : A.length = h + 2) (hn : 3 ≤ h + 2)
    (hb : BasedOn A 9 source) (hz : z ∉ A) (hz9 : z ≠ 9) :
    (advancedComponents source z h).flatten.length = (h + 2) * source.length ∧
      ((advancedComponents source z h).flatten.map Row.charge).sum =
        (h + 2) * (source.map Row.charge).sum := by
  have hp := advancedComponents_inventory source z h hn
    (fun r hr => (hb r hr).2.1.length_eq.trans hA) (fun r hr => (hb r hr).2.2.2)
  have hc := Transport.packingRows_counts source z A.length (hb.ready hz hz9)
  rw [hA] at hc
  exact ⟨hp.length_eq.trans hc.1, ((hp.map Row.charge).sum_eq).trans hc.2.1⟩

end CoefficientTwoPrecision.SourceInventory

#print axioms CoefficientTwoPrecision.SourceInventory.advancedComponents_inventory
#print axioms CoefficientTwoPrecision.SourceInventory.advancedLevel
#print axioms CoefficientTwoPrecision.SourceInventory.advancedCounts
