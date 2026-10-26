import Quantitative.ActiveIncidence
import Quantitative.GuardEvents
import Quantitative.EmbeddedLinearCount
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.CardEmbedding

/-!
# The actual guard-only foreign-event catalogue

The guards are precisely the controls outside the chosen active grid
block. A foreign block and its omitted mobile row specify an actual set
of stationary physical controls. If all of them are guards, each finite
coefficient assignment and bounded right side defines a forbidden set of
guard-cut tuples. We count all tuples before restricting to injective
guard-cut assignments, so no equidistribution premise is needed.
-/

namespace CoefficientTwoPrecision.GuardCatalogue

open ActiveGrid StationaryRelations GuardEvents

abbrev Physical (d A : Nat) := Control (d + 3) A
abbrev Active (d A : Nat) := Block (d + 3) A

def guardNumber (d A : Nat) : Nat := (d + 3) * ((d + 3) * A) - (d + 3)

abbrev Guard (d A : Nat) (hA : 0 < A) (active : Active d A) :=
  {p : Physical d A // p ∉ activeBlock (d + 3) A (by omega) hA active}

theorem guard_card (d A : Nat) (hA : 0 < A) (active : Active d A) :
    Fintype.card (Guard d A hA active) = guardNumber d A := by
  rw [Fintype.card_subtype_compl]
  rw [Fintype.card_coe, activeBlock_card, controls_card]
  rfl

/-- This equivalence enumerates the actual complement of the active block. -/
noncomputable def guardEquiv (d A : Nat) (hA : 0 < A) (active : Active d A) :
    Guard d A hA active ≃ Fin (guardNumber d A) :=
  Fintype.equivFinOfCardEq (guard_card d A hA active)

noncomputable def guardLabel (d A : Nat) (hA : 0 < A) (active : Active d A)
    (j : Fin (guardNumber d A)) : Physical d A :=
  ((guardEquiv d A hA active).symm j).val

theorem guardLabel_injective (d A : Nat) (hA : 0 < A) (active : Active d A) :
    Function.Injective (guardLabel d A hA active) := by
  intro i j hij
  apply (guardEquiv d A hA active).symm.injective
  exact Subtype.ext hij

def foreignControl (d A : Nat) (hA : 0 < A) (foreign : Active d A)
    (mobile : Fin (d + 3)) (i : Fin (d + 2)) : Physical d A :=
  controlAt (d + 3) A (by omega) hA foreign (mobile.succAbove i)

theorem foreignControl_injective (d A : Nat) (hA : 0 < A) (foreign : Active d A)
    (mobile : Fin (d + 3)) : Function.Injective (foreignControl d A hA foreign mobile) := by
  intro i j hij
  apply Fin.succAbove_right_injective (p := mobile)
  exact congrArg Prod.fst hij

def AllGuards (d A : Nat) (hA : 0 < A) (active foreign : Active d A)
    (mobile : Fin (d + 3)) : Prop :=
  ∀ i, foreignControl d A hA foreign mobile i ∉
    activeBlock (d + 3) A (by omega) hA active

noncomputable def foreignGuardIndex (d A : Nat) (hA : 0 < A)
    (active foreign : Active d A) (mobile : Fin (d + 3))
    (hguards : AllGuards d A hA active foreign mobile) (i : Fin (d + 2)) :
    Fin (guardNumber d A) :=
  guardEquiv d A hA active ⟨foreignControl d A hA foreign mobile i, hguards i⟩

theorem foreignGuardIndex_injective (d A : Nat) (hA : 0 < A)
    (active foreign : Active d A) (mobile : Fin (d + 3))
    (hguards : AllGuards d A hA active foreign mobile) :
    Function.Injective (foreignGuardIndex d A hA active foreign mobile hguards) := by
  intro i j hij
  have hsub := (guardEquiv d A hA active).injective hij
  exact foreignControl_injective d A hA foreign mobile (congrArg Subtype.val hsub)

theorem foreign_guard_label (d A : Nat) (hA : 0 < A)
    (active foreign : Active d A) (mobile : Fin (d + 3))
    (hguards : AllGuards d A hA active foreign mobile) (i : Fin (d + 2)) :
    guardLabel d A hA active (foreignGuardIndex d A hA active foreign mobile hguards i) =
      foreignControl d A hA foreign mobile i := by
  simp only [guardLabel, foreignGuardIndex, Equiv.symm_apply_apply]

abbrev Event (d A : Nat) :=
  Active d A × Fin (d + 3) × Assignment d ×
    Fin (2 * stationaryOffsetBound d (guardNumber d A) + 1)

def eventRhs {d A : Nat} (event : Event d A) : Int :=
  (event.2.2.2.val : Int) - stationaryOffsetBound d (guardNumber d A)

noncomputable def badEvent (m d A : Nat) (hA : 0 < A) (active : Active d A)
    (event : Event d A) : Finset (Fin (guardNumber d A) → Fin m) := by
  classical
  exact if h : AllGuards d A hA active event.1 event.2.1 then
    Finset.univ.filter (fun x => Int.ModEq (m : Int)
      (∑ i, weight event.2.2.1 i *
        (x (foreignGuardIndex d A hA active event.1 event.2.1 h i)).val)
      (eventRhs event))
  else ∅

theorem badEvent_card (m d A : Nat) (hm : 0 < m) (hd : 2 ≤ d)
    (hA : 0 < A) (active : Active d A) (event : Event d A) :
    (badEvent m d A hA active event).card ≤ m ^ (guardNumber d A - 1) * (d - 1) := by
  classical
  by_cases h : AllGuards d A hA active event.1 event.2.1
  · have hcount := EmbeddedLinearCount.root_count m hm
      (foreignGuardIndex d A hA active event.1 event.2.1 h)
      (foreignGuardIndex_injective d A hA active event.1 event.2.1 h)
      (weight event.2.2.1) (eventRhs event) (0 : Fin (d + 2))
      (weight_nonzero hd event.2.2.1 0)
    have hc : (weight event.2.2.1 (0 : Fin (d + 2))).natAbs ≤ d - 1 := by
      rw [weight_abs_formula hd]
      split_ifs <;> omega
    simpa only [badEvent, dif_pos h] using
      hcount.trans (Nat.mul_le_mul_left _ hc)
  · simp only [badEvent, dif_neg h, Finset.card_empty]
    exact Nat.zero_le _

def eventCount (d A : Nat) : Nat :=
  (A * ((d + 3) * A)) * (d + 3) * ((d + 2) * (d + 1)) *
    (2 * stationaryOffsetBound d (guardNumber d A) + 1)

theorem event_card (d A : Nat) : Fintype.card (Event d A) = eventCount d A := by
  simp only [Event, Fintype.card_prod, Fintype.card_fin, assignment_card, blocks_card,
    eventCount]
  ring

noncomputable def badTuples (m d A : Nat) (hA : 0 < A) (active : Active d A) :
    Finset (Fin (guardNumber d A) → Fin m) := by
  classical
  exact Finset.univ.biUnion (badEvent m d A hA active)

theorem badTuples_card (m d A : Nat) (hm : 0 < m) (hd : 2 ≤ d)
    (hA : 0 < A) (active : Active d A) :
    (badTuples m d A hA active).card ≤
      eventCount d A * (m ^ (guardNumber d A - 1) * (d - 1)) := by
  classical
  have h := FiniteFibers.bad_union_count Finset.univ (badEvent m d A hA active)
    (m ^ (guardNumber d A - 1) * (d - 1))
    (fun event _ => badEvent_card m d A hm hd hA active event)
  simpa only [badTuples, Finset.card_univ, event_card] using h

noncomputable def badEmbeddings (m d A : Nat) (hA : 0 < A) (active : Active d A) :
    Finset (Fin (guardNumber d A) ↪ Fin m) := by
  classical
  exact Finset.univ.filter (fun cuts : Fin (guardNumber d A) ↪ Fin m =>
    cuts.toFun ∈ badTuples m d A hA active)

noncomputable def goodEmbeddings (m d A : Nat) (hA : 0 < A) (active : Active d A) :
    Finset (Fin (guardNumber d A) ↪ Fin m) := by
  classical
  exact Finset.univ \ badEmbeddings m d A hA active

/-- The discarded injective maps inject into the counted bad tuple set.
There is no division by a putative density of the selected frame code. -/
theorem goodEmbeddings_lower (m d A : Nat) (hm : 0 < m) (hd : 2 ≤ d)
    (hA : 0 < A) (active : Active d A) :
    m.descFactorial (guardNumber d A) ≤ (goodEmbeddings m d A hA active).card +
      eventCount d A * (m ^ (guardNumber d A - 1) * (d - 1)) := by
  classical
  have hmap : Set.MapsTo (fun cuts : Fin (guardNumber d A) ↪ Fin m => cuts.toFun)
      (badEmbeddings m d A hA active) (badTuples m d A hA active) := by
    intro cuts hcuts
    exact (Finset.mem_filter.mp hcuts).2
  have hinj : (badEmbeddings m d A hA active : Set (Fin (guardNumber d A) ↪ Fin m)).InjOn
      (fun cuts => cuts.toFun) := by
    intro cuts _ cuts' _ he
    exact DFunLike.coe_injective he
  have hbad := (Finset.card_le_card_of_injOn _ hmap hinj).trans
    (badTuples_card m d A hm hd hA active)
  have hpartition := Finset.card_le_card_sdiff_add_card
    (s := (Finset.univ : Finset (Fin (guardNumber d A) ↪ Fin m)))
    (t := badEmbeddings m d A hA active)
  have hall : (Finset.univ : Finset (Fin (guardNumber d A) ↪ Fin m)).card =
      m.descFactorial (guardNumber d A) := by simp [Fintype.card_embedding_eq]
  rw [hall] at hpartition
  exact hpartition.trans (Nat.add_le_add_left hbad _)

/-- Every bounded guard-only relation is absent from a retained actual
injective background map. This is the exhaustive catalogue property. -/
theorem good_excludes (m d A : Nat) (hA : 0 < A) (active foreign : Active d A)
    (mobile : Fin (d + 3)) (assignment : Assignment d)
    (hguards : AllGuards d A hA active foreign mobile)
    (cuts : Fin (guardNumber d A) ↪ Fin m)
    (hgood : cuts ∈ goodEmbeddings m d A hA active)
    (b : Int) (hb : b.natAbs ≤ stationaryOffsetBound d (guardNumber d A)) :
    ¬ Int.ModEq (m : Int)
      (∑ i, weight assignment i *
        (cuts (foreignGuardIndex d A hA active foreign mobile hguards i)).val) b := by
  classical
  intro hrel
  let C := stationaryOffsetBound d (guardNumber d A)
  let offset : Fin (2 * C + 1) := ⟨(b + C).toNat, by dsimp [C] at *; omega⟩
  let event : Event d A := (foreign, mobile, assignment, offset)
  have hrhs : eventRhs event = b := by
    dsimp [eventRhs, event, offset, C]
    omega
  have hevent : cuts.toFun ∈ badEvent m d A hA active event := by
    simp only [badEvent, event, dif_pos hguards]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [show eventRhs (foreign, mobile, assignment, offset) = b from hrhs]
    exact hrel
  have hbad : cuts.toFun ∈ badTuples m d A hA active :=
    Finset.mem_biUnion.mpr ⟨event, Finset.mem_univ _, hevent⟩
  have hbadEmb : cuts ∈ badEmbeddings m d A hA active :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩
  exact (Finset.mem_sdiff.mp hgood).2 hbadEmb

end CoefficientTwoPrecision.GuardCatalogue

#print axioms CoefficientTwoPrecision.GuardCatalogue.badTuples_card
#print axioms CoefficientTwoPrecision.GuardCatalogue.goodEmbeddings_lower
#print axioms CoefficientTwoPrecision.GuardCatalogue.good_excludes
