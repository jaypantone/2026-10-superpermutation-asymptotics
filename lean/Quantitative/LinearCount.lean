import Quantitative.FiniteFibers
import Quantitative.FrameAlgebra

/-!
# A finite linear congruence count

Separate one coordinate with a nonzero coefficient. The remaining
coordinates range over a complete finite product. The root count then
applies uniformly to each fibre, even for composite moduli.
-/

namespace CoefficientTwoPrecision.LinearCount

def restSum {M d : Nat} (j : Fin d) (a : Fin d → Int)
    (y : {i : Fin d // i ≠ j} → Fin M) : Int :=
  ∑ i, if h : i = j then 0 else a i * (y ⟨i, h⟩).val

theorem split_sum {M d : Nat} (j : Fin d) (a : Fin d → Int) (x : Fin d → Fin M) :
    (∑ i, a i * (x i).val) =
      a j * (x j).val + restSum j a (fun i => x i.val) := by
  calc
    ∑ i, a i * (x i).val =
        ∑ i, ((if i = j then a j * (x j).val else 0) +
          (if h : i = j then 0 else a i * (x (⟨i, h⟩ : {i : Fin d // i ≠ j})).val)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = j
      · subst i; simp
      · simp [hi]
    _ = a j * (x j).val + restSum j a (fun i => x i.val) := by
      simp [Finset.sum_add_distrib, restSum]

theorem linear_root_count (M d : Nat) (hM : 0 < M)
    (a : Fin d → Int) (b : Int) (j : Fin d) (ha : a j ≠ 0) :
    (Finset.univ.filter (fun x : Fin d → Fin M =>
      Int.ModEq (M : Int) (∑ i, a i * (x i).val) b)).card ≤
      M ^ (d - 1) * (a j).natAbs := by
  let S := Finset.univ.filter (fun x : Fin d → Fin M =>
    Int.ModEq (M : Int) (∑ i, a i * (x i).val) b)
  let rhs : ({i : Fin d // i ≠ j} → Fin M) → Int := fun y => b - restSum j a y
  let T := Finset.univ.filter
    (fun p : ({i : Fin d // i ≠ j} → Fin M) × Fin M =>
      Int.ModEq (M : Int) (a j * p.2.val) (rhs p.1))
  let f : (Fin d → Fin M) → ({i : Fin d // i ≠ j} → Fin M) × Fin M :=
    fun x => (fun i => x i.val, x j)
  have hmap : Set.MapsTo f (S : Set (Fin d → Fin M))
      (T : Set (({i : Fin d // i ≠ j} → Fin M) × Fin M)) := by
    intro x hx
    have h := (Finset.mem_filter.mp hx).2
    rw [split_sum j a x] at h
    have hsub := h.sub_right (restSum j a (fun i => x i.val))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [f, rhs] using hsub⟩
  have hinj : (S : Set (Fin d → Fin M)).InjOn f := by
    intro x _ y _ hxy
    have hrest := congrArg Prod.fst hxy
    have hcoord := congrArg Prod.snd hxy
    funext i
    by_cases hi : i = j
    · subst i; exact hcoord
    · exact congrFun hrest ⟨i, hi⟩
  have hcard : Fintype.card {i : Fin d // i ≠ j} = d - 1 := by
    rw [Fintype.card_subtype_compl (fun i : Fin d => i = j)]
    simp
  have hproduct : Fintype.card ({i : Fin d // i ≠ j} → Fin M) = M ^ (d - 1) := by
    simp [hcard]
  have hbound := FiniteFibers.dependent_root_count M hM (a j) ha rhs
  rw [hproduct] at hbound
  exact (Finset.card_le_card_of_injOn f hmap hinj).trans hbound

end CoefficientTwoPrecision.LinearCount

#print axioms CoefficientTwoPrecision.LinearCount.linear_root_count
