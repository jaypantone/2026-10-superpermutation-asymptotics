import Quantitative.ProximitySurvivors
import Quantitative.GuardFreeCount

/-!
# Counting one actual proximity equation in the candidate product

For a nonzero guard coefficient, fix the selected labelled node and count
guard assignments. If all guard coefficients vanish, count ambient
labelled frames and multiply by the exact number of injective guard maps.
Both arguments apply to one fixed selection shared by every background.
-/

namespace CoefficientTwoPrecision.ProximityPairCount

open GuardCatalogue CandidateSpace LabelledReconstruction PrimaryCatalogue PrimaryRank
open ProximityCatalogue ProximitySurvivors SortedFrameSupply

variable {m d A : Nat}

abbrev Fiber (m d A : Nat) :=
  (Fin (guardNumber d A) ↪ Fin m) × Labelled (m + guardNumber d A) d

noncomputable def pairSolutions (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) (event : PairEvent d A hA active) :
    Finset (Fiber m d A) := by
  classical
  exact (Finset.univ ×ˢ S).filter (fun p =>
    forbiddenPair hA active event.1 ≠ forbiddenPair hA active event.2.1 ∧
      Equation hA active p.1 p.2.1 event)

theorem guard_variable_count (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A)
    (active : Active d A) (S : Finset (Labelled (m + guardNumber d A) d))
    (event : PairEvent d A hA active) (u : Fin (guardNumber d A))
    (hu : guardCross hA active event.1 event.2.1 u ≠ 0) :
    (pairSolutions hA active S event).card ≤
      S.card * (m ^ (guardNumber d A - 1) * (2 * (d - 1) ^ 2)) := by
  classical
  apply FiniteFibers.card_le_of_fiber_bound (pairSolutions hA active S event) S Prod.snd
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  · intro node hnode
    let T := Finset.univ.filter (fun x : Fin (guardNumber d A) → Fin m =>
      Int.ModEq (m : Int) (∑ v, guardCross hA active event.1 event.2.1 v * (x v).val)
        (rightSide hA active event - frameTerm hA active node.1 event))
    let F := (pairSolutions hA active S event).filter (fun p => p.2 = node)
    have hmap : Set.MapsTo (fun p : Fiber m d A => (p.1 : Fin (guardNumber d A) → Fin m))
        F T := by
      intro p hp
      obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
      have heq := (Finset.mem_filter.mp hp).2.2
      rw [he] at heq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (equation_iff_guards hA active p.1 node.1 event).mp heq⟩
    have hinj : (F : Set (Fiber m d A)).InjOn
        (fun p => (p.1 : Fin (guardNumber d A) → Fin m)) := by
      intro p hp q hq he
      apply Prod.ext
      · exact DFunLike.coe_injective he
      · exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    exact (Finset.card_le_card_of_injOn _ hmap hinj).trans
      (guard_root_count m hm hd hA active event.1 event.2.1
        (rightSide hA active event - frameTerm hA active node.1 event) u hu)

theorem labelled_frame_count (m M : Nat) [NeZero M] (hm : 0 < m) (hMpos : 0 < M)
    (hM : M ≤ 2 * m) (hd : 3 ≤ d) (a : Int) (ha : a ≠ 0)
    (j l : Fin (d + 2)) (hne : j ≠ l) (b : Int) :
    (d - 1).factorial * ((labelledFrames M d).filter
      (fun node => Int.ModEq (m : Int) (a * ((node.1 j).val - ((node.1 l).val : Int))) b)).card ≤
        (d + 3).factorial * ((d + 1) * d * (M ^ (d - 1) * (2 * a.natAbs))) := by
  classical
  have he : ((labelledFrames M d).filter
      (fun node => Int.ModEq (m : Int) (a * ((node.1 j).val - ((node.1 l).val : Int))) b)).card =
      ((physicalFrames M d).filter
        (fun q => Int.ModEq (m : Int) (a * ((q j).val - ((q l).val : Int))) b)).card *
          (d + 3).factorial := by
    rw [labelledFrames, Finset.filter_product_left
      (fun q : Fin (d + 2) → Fin M =>
        Int.ModEq (m : Int) (a * ((q j).val - ((q l).val : Int))) b), Finset.card_product]
    simp [FiniteRoles.Role, Fintype.card_perm, Nat.add_assoc]
  rw [he]
  have h := Nat.mul_le_mul_left (d + 3).factorial
    (GuardFreeCount.physical_count m M hm hMpos hM hd a ha j l hne b)
  nlinarith only [h]

theorem guard_free_count [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hM : m + guardNumber d A ≤ 2 * m) (hd : 3 ≤ d) (hA : 0 < A)
    (active : Active d A) (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ labelledFrames (m + guardNumber d A) d)
    (event : PairEvent d A hA active)
    (hzero : ∀ u, guardCross hA active event.1 event.2.1 u = 0) :
    (d - 1).factorial * (pairSolutions hA active S event).card ≤
      m.descFactorial (guardNumber d A) * (d + 3).factorial *
        ((d + 1) * d * ((m + guardNumber d A) ^ (d - 1) * (2 * (d - 1) ^ 2))) := by
  classical
  by_cases hdistinct : forbiddenPair hA active event.1 ≠ forbiddenPair hA active event.2.1
  · let a := coefficient hA active event.1 * coefficient hA active event.2.1
    let j := slot hA active event.1
    let l := slot hA active event.2.1
    let b := rightSide hA active event
    let T := (labelledFrames (m + guardNumber d A) d).filter (fun node =>
      Int.ModEq (m : Int) (a * ((node.1 j).val - ((node.1 l).val : Int))) b)
    have hsub : pairSolutions hA active S event ⊆
        (Finset.univ : Finset (Fin (guardNumber d A) ↪ Fin m)) ×ˢ T := by
      intro p hp
      obtain ⟨hbase, hneq, heq⟩ := Finset.mem_filter.mp hp
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact hS (Finset.mem_product.mp hbase).2
      · exact (equation_guard_free hA active p.1 p.2.1 event hzero).mp heq
    have hcard : (pairSolutions hA active S event).card ≤
        m.descFactorial (guardNumber d A) * T.card := by
      simpa only [Finset.card_product, Finset.card_univ, Fintype.card_embedding_eq,
        Fintype.card_fin] using Finset.card_le_card hsub
    have ha : a ≠ 0 := mul_ne_zero
      (PrimaryCatalogue.coefficient_nonzero (by omega) hA active event.1)
      (PrimaryCatalogue.coefficient_nonzero (by omega) hA active event.2.1)
    have hne : j ≠ l := distinct_slots_of_guard_free hd hA active event.1 event.2.1 hdistinct hzero
    have hbound := labelled_frame_count m (m + guardNumber d A) hm (by omega) hM hd
      a ha j l hne b
    have hcoef (e : Event d A hA active) : (coefficient hA active e).natAbs ≤ d - 1 := by
      unfold coefficient
      rw [StationaryRelations.weight_abs_formula (by omega)]
      split_ifs <;> omega
    have habs : a.natAbs ≤ (d - 1) ^ 2 := by
      dsimp only [a]
      rw [Int.natAbs_mul, pow_two]
      exact Nat.mul_le_mul (hcoef event.1) (hcoef event.2.1)
    have hsmall : (d - 1).factorial * T.card ≤ (d + 3).factorial *
        ((d + 1) * d * ((m + guardNumber d A) ^ (d - 1) * (2 * (d - 1) ^ 2))) := by
      apply hbound.trans
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 habs)))
    have hlarge := Nat.mul_le_mul_left (m.descFactorial (guardNumber d A)) hsmall
    have hcard' := Nat.mul_le_mul_left (d - 1).factorial hcard
    nlinarith only [hlarge, hcard']
  · have hempty : pairSolutions hA active S event = ∅ := by
      ext p
      simp [pairSolutions, hdistinct]
    rw [hempty, Finset.card_empty, Nat.mul_zero]
    exact Nat.zero_le _

end CoefficientTwoPrecision.ProximityPairCount

#print axioms CoefficientTwoPrecision.ProximityPairCount.guard_variable_count
#print axioms CoefficientTwoPrecision.ProximityPairCount.guard_free_count
