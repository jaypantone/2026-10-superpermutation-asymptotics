import Quantitative.IntervalRoots
import Quantitative.LinearCount
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort

/-!
# Counting a congruence among actual increasing coordinate tuples

Deleting one coordinate leaves an increasing tuple, which is uniquely
determined by its value set. There are choose(M,d-1) such sets. For each
one, the deleted coordinate has at most 2|a_j| roots when M is at most 2m.
This preserves the factorial denominator required for guard-free deletion.
-/

namespace CoefficientTwoPrecision.SortedLinearCount

def restSet {M d : Nat} (j : Fin d) (x : Fin d → Fin M) : Finset (Fin M) :=
  (Finset.univ.erase j).image x

theorem restSet_card {M d : Nat} (j : Fin d) (x : Fin d → Fin M)
    (hx : StrictMono x) : (restSet j x).card = d - 1 := by
  rw [restSet, Finset.card_image_of_injective _ hx.injective,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- Strict order recovers all surviving coordinates from their value set. -/
theorem rest_eq_of_set_eq {M d : Nat} (j : Fin d) (x y : Fin d → Fin M)
    (hx : StrictMono x) (hy : StrictMono y) (heq : restSet j x = restSet j y) :
    ∀ i, i ≠ j → x i = y i := by
  let f : {i : Fin d // i ≠ j} → Fin M := fun i => x i.val
  let g : {i : Fin d // i ≠ j} → Fin M := fun i => y i.val
  have hf : StrictMono f := fun _ _ h => hx h
  have hg : StrictMono g := fun _ _ h => hy h
  have hrange : Set.range f = Set.range g := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      have hm : x i.val ∈ restSet j x :=
        Finset.mem_image.mpr ⟨i.val, Finset.mem_erase.mpr ⟨i.property, Finset.mem_univ _⟩, rfl⟩
      rw [heq] at hm
      obtain ⟨i', hi', he'⟩ := Finset.mem_image.mp hm
      exact ⟨⟨i', (Finset.mem_erase.mp hi').1⟩, he'⟩
    · rintro ⟨i, rfl⟩
      have hm : y i.val ∈ restSet j y :=
        Finset.mem_image.mpr ⟨i.val, Finset.mem_erase.mpr ⟨i.property, Finset.mem_univ _⟩, rfl⟩
      rw [← heq] at hm
      obtain ⟨i', hi', he'⟩ := Finset.mem_image.mp hm
      exact ⟨⟨i', (Finset.mem_erase.mp hi').1⟩, he'⟩
  have hfun : f = g := hf.range_inj_of_wellFoundedLT hg |>.mp hrange
  intro i hi
  exact congrFun hfun ⟨i, hi⟩

noncomputable def solutions (m M d : Nat) (a : Fin d → Int) (b : Int) :
    Finset (Fin d → Fin M) := by
  classical
  exact Finset.univ.filter (fun x => StrictMono x ∧
    Int.ModEq (m : Int) (∑ i, a i * (x i).val) b)

theorem fiber_card (m M d : Nat) (hm : 0 < m) (hM : M ≤ 2 * m)
    (a : Fin d → Int) (b : Int) (j : Fin d) (ha : a j ≠ 0)
    (A : Finset (Fin M)) :
    ((solutions m M d a b).filter (fun x => restSet j x = A)).card ≤ 2 * (a j).natAbs := by
  classical
  let S := (solutions m M d a b).filter (fun x => restSet j x = A)
  rcases S.eq_empty_or_nonempty with hS | ⟨y, hy⟩
  · change S.card ≤ _
    rw [hS, Finset.card_empty]
    exact Nat.zero_le _
  · have hySol : y ∈ solutions m M d a b := (Finset.mem_filter.mp hy).1
    have hyMono : StrictMono y := (Finset.mem_filter.mp hySol).2.1
    have hySet : restSet j y = A := (Finset.mem_filter.mp hy).2
    let rhs := b - LinearCount.restSum j a (fun i => y i.val)
    let T := Finset.univ.filter (fun z : Fin M => Int.ModEq (m : Int) (a j * z.val) rhs)
    have hrest (x : Fin d → Fin M) (hx : x ∈ S) :
        ∀ i, i ≠ j → x i = y i := by
      have hxSol := (Finset.mem_filter.mp hx).1
      have hxMono : StrictMono x := (Finset.mem_filter.mp hxSol).2.1
      have hxSet := (Finset.mem_filter.mp hx).2
      exact rest_eq_of_set_eq j x y hxMono hyMono (hxSet.trans hySet.symm)
    have hmap : Set.MapsTo (fun x : Fin d → Fin M => x j) S T := by
      intro x hx
      have hxSol := (Finset.mem_filter.mp hx).1
      have hrel := (Finset.mem_filter.mp hxSol).2.2
      have hre : (fun i : {i : Fin d // i ≠ j} => x i.val) = (fun i => y i.val) :=
        funext (fun i => hrest x hx i.val i.property)
      rw [LinearCount.split_sum j a x, hre] at hrel
      have hsub := hrel.sub_right (LinearCount.restSum j a (fun i => y i.val))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [rhs] using hsub⟩
    have hinj : (S : Set (Fin d → Fin M)).InjOn (fun x => x j) := by
      intro x hx z hz hj
      funext i
      by_cases hi : i = j
      · subst i
        exact hj
      · exact (hrest x hx i hi).trans (hrest z hz i hi).symm
    exact (Finset.card_le_card_of_injOn _ hmap hinj).trans
      (IntervalRoots.fin_root_count m M hm hM (a j) rhs ha)

theorem solutions_card (m M d : Nat) (hm : 0 < m) (hM : M ≤ 2 * m)
    (a : Fin d → Int) (b : Int) (j : Fin d) (ha : a j ≠ 0) :
    (solutions m M d a b).card ≤ M.choose (d - 1) * (2 * (a j).natAbs) := by
  classical
  have hmap : Set.MapsTo (restSet j) (solutions m M d a b)
      (((Finset.univ : Finset (Fin M)).powersetCard (d - 1)) : Set (Finset (Fin M))) := by
    intro x hx
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, restSet_card j x (Finset.mem_filter.mp hx).2.1⟩
  have h := FiniteFibers.card_le_of_fiber_bound (solutions m M d a b)
    ((Finset.univ : Finset (Fin M)).powersetCard (d - 1)) (restSet j) (2 * (a j).natAbs)
    hmap (fun A _ => fiber_card m M d hm hM a b j ha A)
  simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using h

/-- Multiplying by the factorial keeps the estimate entirely integral. -/
theorem solutions_card_factorial (m M d : Nat) (hm : 0 < m) (hM : M ≤ 2 * m)
    (a : Fin d → Int) (b : Int) (j : Fin d) (ha : a j ≠ 0) :
    (d - 1).factorial * (solutions m M d a b).card ≤
      M ^ (d - 1) * (2 * (a j).natAbs) := by
  have h := Nat.mul_le_mul_left (d - 1).factorial (solutions_card m M d hm hM a b j ha)
  calc
    (d - 1).factorial * (solutions m M d a b).card
        ≤ (d - 1).factorial * (M.choose (d - 1) * (2 * (a j).natAbs)) := h
    _ = M.descFactorial (d - 1) * (2 * (a j).natAbs) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      ring
    _ ≤ M ^ (d - 1) * (2 * (a j).natAbs) :=
      Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow _ _)

end CoefficientTwoPrecision.SortedLinearCount

#print axioms CoefficientTwoPrecision.SortedLinearCount.solutions_card
#print axioms CoefficientTwoPrecision.SortedLinearCount.solutions_card_factorial
