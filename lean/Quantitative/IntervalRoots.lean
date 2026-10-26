import Quantitative.ModularRoots

/-!
# Modular roots in the actual unscaled coordinate interval

The background length M can be larger than the old-circle modulus m.
When M is at most 2m, a nonzero coefficient a has at most 2|a| roots in
the whole interval [0,M). This factor of two is retained explicitly.
-/

namespace CoefficientTwoPrecision.IntervalRoots

theorem integer_root_count (m M : Nat) (hm : 0 < m) (hM : M ≤ 2 * m)
    (a b : Int) (ha : a ≠ 0) :
    ((Finset.range M).filter (fun x : Nat => Int.ModEq (m : Int) (a * x) b)).card ≤
      2 * a.natAbs := by
  let S := (Finset.range M).filter (fun x : Nat => Int.ModEq (m : Int) (a * x) b)
  have haAbs : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  have hmap : Set.MapsTo (fun x => a.natAbs * x / m) S (Finset.range (2 * a.natAbs)) := by
    intro x hx
    have hxM := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hm).mpr
    nlinarith
  have hmod (x : Nat) (hx : x ∈ S) (y : Nat) (hy : y ∈ S) :
      Nat.ModEq m (a.natAbs * x) (a.natAbs * y) := by
    have hxy : Int.ModEq (m : Int) (a * x) (a * y) :=
      (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have habs : Int.ModEq (m : Int) ((a.natAbs : Int) * x) ((a.natAbs : Int) * y) := by
      by_cases hnonneg : 0 ≤ a
      · simpa only [Int.natAbs_of_nonneg hnonneg] using hxy
      · have hnonpos : a ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
        simpa only [Int.ofNat_natAbs_of_nonpos hnonpos, neg_mul] using hxy.neg
    exact Int.natCast_modEq_iff.mp (by simpa only [Int.natCast_mul] using habs)
  have hinj : (S : Set Nat).InjOn (fun x => a.natAbs * x / m) := by
    intro x hx y hy hq
    have heq : a.natAbs * x = a.natAbs * y :=
      (Nat.ext_div_modEq_iff m (a.natAbs * x) (a.natAbs * y)).mpr ⟨hq, hmod x hx y hy⟩
    exact Nat.eq_of_mul_eq_mul_left haAbs heq
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmap hinj

theorem fin_root_count (m M : Nat) (hm : 0 < m) (hM : M ≤ 2 * m)
    (a b : Int) (ha : a ≠ 0) :
    (Finset.univ.filter (fun x : Fin M => Int.ModEq (m : Int) (a * x.val) b)).card ≤
      2 * a.natAbs := by
  let S := Finset.univ.filter (fun x : Fin M => Int.ModEq (m : Int) (a * x.val) b)
  let T := (Finset.range M).filter (fun x : Nat => Int.ModEq (m : Int) (a * x) b)
  have hmap : Set.MapsTo (fun x : Fin M => x.val) S T := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.isLt, (Finset.mem_filter.mp hx).2⟩
  have hinj : (S : Set (Fin M)).InjOn Fin.val := by
    intro x _ y _ he
    exact Fin.ext he
  exact (Finset.card_le_card_of_injOn Fin.val hmap hinj).trans
    (integer_root_count m M hm hM a b ha)

end CoefficientTwoPrecision.IntervalRoots

#print axioms CoefficientTwoPrecision.IntervalRoots.fin_root_count
