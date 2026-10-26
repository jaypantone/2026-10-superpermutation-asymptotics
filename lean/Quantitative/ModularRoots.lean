import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Counting roots of a congruence for an arbitrary modulus

There are at most |a| roots of a*x = b modulo M when a is a nonzero
integer and x runs through one complete set of residues. No primality
assumption is used. The proof assigns each root the quotient of |a|*x by M;
there are only |a| possible quotients, and equal quotients and remainders
determine equal roots.
-/

namespace CoefficientTwoPrecision.ModularRoots

theorem card_le_of_congruent_products (M a : Nat) (hM : 0 < M) (ha : 0 < a)
    (S : Finset Nat) (hS : S ⊆ Finset.range M)
    (hmod : ∀ x ∈ S, ∀ y ∈ S, Nat.ModEq M (a * x) (a * y)) :
    S.card ≤ a := by
  have hmap : Set.MapsTo (fun x => a * x / M) S (Finset.range a) := by
    intro x hx
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hM).mpr
    have hxM : x < M := Finset.mem_range.mp (hS hx)
    simpa only [Nat.mul_comm M a] using Nat.mul_lt_mul_of_pos_left hxM ha
  have hinj : (S : Set Nat).InjOn (fun x => a * x / M) := by
    intro x hx y hy hq
    have heq : a * x = a * y := (Nat.ext_div_modEq_iff M (a * x) (a * y)).mpr
      ⟨hq, hmod x hx y hy⟩
    exact Nat.eq_of_mul_eq_mul_left ha heq
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmap hinj

/-- Uniform root count for the displayed integer congruence. -/
theorem integer_root_count (M : Nat) (hM : 0 < M) (a b : Int) (ha : a ≠ 0) :
    ((Finset.range M).filter (fun x : Nat => Int.ModEq (M : Int) (a * x) b)).card ≤
      a.natAbs := by
  let S := (Finset.range M).filter (fun x : Nat => Int.ModEq (M : Int) (a * x) b)
  have haAbs : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  apply card_le_of_congruent_products M a.natAbs hM haAbs S (Finset.filter_subset _ _)
  intro x hx y hy
  have hxy : Int.ModEq (M : Int) (a * x) (a * y) :=
    (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  have habs : Int.ModEq (M : Int) ((a.natAbs : Int) * x) ((a.natAbs : Int) * y) := by
    by_cases hnonneg : 0 ≤ a
    · simpa only [Int.natAbs_of_nonneg hnonneg] using hxy
    · have hnonpos : a ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
      simpa only [Int.ofNat_natAbs_of_nonpos hnonpos, neg_mul] using hxy.neg
  exact Int.natCast_modEq_iff.mp (by simpa only [Int.natCast_mul] using habs)

/-- The same estimate applies to any restricted residue set. -/
theorem restricted_integer_root_count (M : Nat) (hM : 0 < M)
    (a b : Int) (ha : a ≠ 0) (S : Finset Nat) (hS : S ⊆ Finset.range M) :
    (S.filter (fun x : Nat => Int.ModEq (M : Int) (a * x) b)).card ≤ a.natAbs := by
  apply le_trans (Finset.card_le_card ?_) (integer_root_count M hM a b ha)
  intro x hx
  obtain ⟨hx, heq⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hS hx, heq⟩

end CoefficientTwoPrecision.ModularRoots

#print axioms CoefficientTwoPrecision.ModularRoots.integer_root_count
#print axioms CoefficientTwoPrecision.ModularRoots.restricted_integer_root_count
