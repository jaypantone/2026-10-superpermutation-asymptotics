import Quantitative.NeighbourGeometry
import Quantitative.ActiveSlotEvents
import Quantitative.IntervalRoots

/-!
# The actual primary-event catalogue and its time multiplicity

An event records a neighbouring foreign block, a nonshared foreign mobile,
a coefficient assignment, a current stationary slot, and one bounded
right side. Its remaining foreign stationary controls use the actual
guard indices constructed in NeighbourGeometry. Event occurrences are
the finite pairs of a catalogue entry and a time satisfying its congruence.
Summing coefficient magnitudes, rather than replacing every coefficient
by its maximum, preserves the required polynomial degree.
-/

namespace CoefficientTwoPrecision.PrimaryCatalogue

open GuardCatalogue NeighbourGeometry StationaryRelations ActiveSlotEvents

variable {d A : Nat}

abbrev Tail (d A : Nat) := Assignment d × Fin (d + 2) ×
  Fin (2 * primaryOffsetBound d (guardNumber d A) + 1)

abbrev Event (d A : Nat) (hA : 0 < A) (active : Active d A) :=
  Σ foreign : Neighbour d A hA active, Mobile hA active foreign × Tail d A

noncomputable def coefficient (hA : 0 < A) (active : Active d A) (event : Event d A hA active) : Int :=
  weight event.2.2.1 (sharedIndex hA active event.1 event.2.1)

def slot (hA : 0 < A) (active : Active d A) (event : Event d A hA active) : Fin (d + 2) :=
  event.2.2.2.1

def rhs (hA : 0 < A) (active : Active d A) (event : Event d A hA active) : Int :=
  (event.2.2.2.2.val : Int) - primaryOffsetBound d (guardNumber d A)

noncomputable def guardSum {m : Nat} (hA : 0 < A) (active : Active d A)
    (event : Event d A hA active) (x : Fin (guardNumber d A) → Fin m) : Int :=
  ∑ i : {i : Fin (d + 2) // i ≠ sharedIndex hA active event.1 event.2.1},
    weight event.2.2.1 i.val * (x (guardIndex hA active event.1 event.2.1 i)).val

theorem coefficient_nonzero (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A)
    (event : Event d A hA active) : coefficient hA active event ≠ 0 :=
  weight_nonzero hd _ _

noncomputable def times (m : Nat) (hA : 0 < A) (active : Active d A)
    (x : Fin (guardNumber d A) → Fin m)
    (q : Fin (d + 2) → Fin (m + guardNumber d A)) (event : Event d A hA active) :
    Finset (Fin (m + guardNumber d A)) := by
  classical
  exact Finset.univ.filter (fun t => Int.ModEq (m : Int)
    (coefficient hA active event * ((q (slot hA active event)).val + (t.val : Int)) +
      guardSum hA active event x) (rhs hA active event))

theorem times_card (m : Nat) (hm : 0 < m) (hsize : m + guardNumber d A ≤ 2 * m)
    (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A)
    (x : Fin (guardNumber d A) → Fin m)
    (q : Fin (d + 2) → Fin (m + guardNumber d A)) (event : Event d A hA active) :
    (times m hA active x q event).card ≤ 2 * (coefficient hA active event).natAbs := by
  classical
  let a := coefficient hA active event
  let c := guardSum hA active event x
  let q0 : Int := (q (slot hA active event)).val
  let b := rhs hA active event - c - a * q0
  let T := Finset.univ.filter (fun t : Fin (m + guardNumber d A) =>
    Int.ModEq (m : Int) (a * t.val) b)
  have hsub : times m hA active x q event ⊆ T := by
    intro t ht
    have h := (Finset.mem_filter.mp ht).2
    have hs := h.sub_right (a * q0 + c)
    have hleft : a * (q0 + t.val) + c - (a * q0 + c) = a * t.val := by ring
    have hright : rhs hA active event - (a * q0 + c) = b := by dsimp [b]; ring
    change Int.ModEq (m : Int) (a * (q0 + t.val) + c - (a * q0 + c))
      (rhs hA active event - (a * q0 + c)) at hs
    rw [hleft, hright] at hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
  exact (Finset.card_le_card hsub).trans
    (IntervalRoots.fin_root_count m (m + guardNumber d A) hm hsize a b
      (coefficient_nonzero hd hA active event))

def typeCount (d A : Nat) : Nat :=
  ((d + 3) * (A - 1)) * (d + 2) ^ 3 * (d + 1) *
    (2 * primaryOffsetBound d (guardNumber d A) + 1)

theorem event_card (hA : 0 < A) (active : Active d A) :
    Fintype.card (Event d A hA active) = typeCount d A := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, mobile_card, Tail, Fintype.card_prod, Fintype.card_fin,
    assignment_card]
  simp only [Finset.sum_const, Finset.card_univ, neighbour_card, Nat.nsmul_eq_mul, typeCount]
  ring

private theorem tail_weight_sum (hd : 2 ≤ d) (shared : Fin (d + 2)) :
    (∑ tail : Tail d A, 2 * (weight tail.1 shared).natAbs) =
      (d + 2) * (2 * primaryOffsetBound d (guardNumber d A) + 1) * (4 * d * (d + 1)) := by
  rw [Fintype.sum_prod_type]
  change (∑ a : Assignment d, ∑ rest : Fin (d + 2) ×
    Fin (2 * primaryOffsetBound d (guardNumber d A) + 1), 2 * (weight a shared).natAbs) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Nat.nsmul_eq_mul]
  calc
    (∑ a : Assignment d, ((d + 2) * (2 * primaryOffsetBound d (guardNumber d A) + 1)) *
        (2 * (weight a shared).natAbs)) =
        ((d + 2) * (2 * primaryOffsetBound d (guardNumber d A) + 1) * 2) *
          (∑ a : Assignment d, (weight a shared).natAbs) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [fixed_label_abs_sum hd shared]; ring

def occurrenceBound (d A : Nat) : Nat :=
  4 * ((d + 3) * (A - 1)) * (d + 2) ^ 2 * d * (d + 1) *
    (2 * primaryOffsetBound d (guardNumber d A) + 1)

theorem coefficient_sum (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A) :
    (∑ event : Event d A hA active, 2 * (coefficient hA active event).natAbs) =
      occurrenceBound d A := by
  classical
  have htail (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign) :
      (∑ tail : Tail d A, 2 * (coefficient hA active ⟨foreign, mobile, tail⟩).natAbs) =
        (d + 2) * (2 * primaryOffsetBound d (guardNumber d A) + 1) * (4 * d * (d + 1)) :=
    tail_weight_sum hd (sharedIndex hA active foreign mobile)
  have hforeign (foreign : Neighbour d A hA active) :
      (∑ pair : Mobile hA active foreign × Tail d A,
        2 * (coefficient hA active ⟨foreign, pair⟩).natAbs) =
        (d + 2) * ((d + 2) * (2 * primaryOffsetBound d (guardNumber d A) + 1) *
          (4 * d * (d + 1))) := by
    rw [Fintype.sum_prod_type]
    simp_rw [htail foreign]
    simp only [Finset.sum_const, Finset.card_univ, mobile_card, Nat.nsmul_eq_mul]
  rw [Fintype.sum_sigma]
  simp_rw [hforeign]
  simp only [Finset.sum_const, Finset.card_univ, neighbour_card, Nat.nsmul_eq_mul,
    occurrenceBound]
  ring

noncomputable def occurrences (m : Nat) (hA : 0 < A) (active : Active d A)
    (x : Fin (guardNumber d A) → Fin m)
    (q : Fin (d + 2) → Fin (m + guardNumber d A)) :
    Finset (Σ _event : Event d A hA active, Fin (m + guardNumber d A)) := by
  classical
  exact Finset.univ.sigma (times m hA active x q)

theorem occurrences_card (m : Nat) (hm : 0 < m) (hsize : m + guardNumber d A ≤ 2 * m)
    (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A)
    (x : Fin (guardNumber d A) → Fin m)
    (q : Fin (d + 2) → Fin (m + guardNumber d A)) :
    (occurrences m hA active x q).card ≤ occurrenceBound d A := by
  classical
  rw [occurrences, Finset.card_sigma]
  calc
    (∑ event, (times m hA active x q event).card)
        ≤ ∑ event : Event d A hA active, 2 * (coefficient hA active event).natAbs := by
      apply Finset.sum_le_sum
      intro event _
      exact times_card m hm hsize hd hA active x q event
    _ = occurrenceBound d A := coefficient_sum hd hA active

end CoefficientTwoPrecision.PrimaryCatalogue

#print axioms CoefficientTwoPrecision.PrimaryCatalogue.event_card
#print axioms CoefficientTwoPrecision.PrimaryCatalogue.coefficient_sum
#print axioms CoefficientTwoPrecision.PrimaryCatalogue.occurrences_card
