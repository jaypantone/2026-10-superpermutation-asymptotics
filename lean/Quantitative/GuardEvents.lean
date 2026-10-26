import Quantitative.GuardPositions
import Quantitative.StationaryRelations
import Mathlib.Data.Int.ModEq

/-!
# The actual stationary relation in original-cut coordinates

The coefficients are the finite catalogue in StationaryRelations. A common
cyclic change of anchor cancels because their sum is zero. The winding is
bounded using the actual local positions. Finally, every local position is
an original cut plus at most G guards, giving the explicit constant C1.
-/

namespace CoefficientTwoPrecision.GuardEvents

open StationaryRelations StationaryCircle StationaryUpdate GuardPositions

private theorem modEq_sum {ι : Type} [Fintype ι] (M : Int)
    (a b : ι → Int) (h : ∀ i, Int.ModEq M (a i) (b i)) :
    Int.ModEq M (∑ i, a i) (∑ i, b i) := by
  classical
  have hs (s : Finset ι) : Int.ModEq M (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
    induction s using Finset.induction_on with
    | empty => exact Int.ModEq.rfl
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (h i).add ih
  exact hs Finset.univ

/-- Reanchoring every coordinate by the same cyclic translation does not
change a zero-sum relation. This includes reanchoring at an old symbol. -/
theorem reanchor_relation {ι : Type} [Fintype ι] (M shift : Int)
    (c y z : ι → Int) (hc : ∑ i, c i = 0)
    (hy : ∀ i, Int.ModEq M (y i) (z i + shift)) :
    Int.ModEq M (∑ i, c i * y i) (∑ i, c i * z i) := by
  have h := modEq_sum M (fun i => c i * y i) (fun i => c i * (z i + shift))
    (fun i => (hy i).mul_left (c i))
  simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hc,
    zero_mul, add_zero] using h

theorem frame_relation {ι : Type} [Fintype ι] (M t : Int)
    (c q phase y : ι → Int) (hc : ∑ i, c i = 0)
    (hq : Int.ModEq M (∑ i, c i * q i) 0)
    (hy : ∀ i, Int.ModEq M (y i) (q i + t + phase i)) :
    Int.ModEq M (∑ i, c i * y i) (∑ i, c i * phase i) := by
  have h := modEq_sum M (fun i => c i * y i)
    (fun i => c i * (q i + t + phase i))
    (fun i => (hy i).mul_left (c i))
  have hr : (∑ i, c i * (q i + t + phase i)) =
      (∑ i, c i * q i) + (∑ i, c i * phase i) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hc,
      zero_mul, add_zero]
  rw [hr] at h
  exact h.trans (by simpa only [zero_add] using hq.add_right (∑ i, c i * phase i))

theorem weighted_abs_bound {ι : Type} [Fintype ι] (c x : ι → Int) (K : Nat)
    (hx : ∀ i, (x i).natAbs ≤ K) :
    (∑ i, c i * x i).natAbs ≤ (∑ i, (c i).natAbs) * K := by
  calc
    (∑ i, c i * x i).natAbs ≤ ∑ i, (c i * x i).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ i, (c i).natAbs * K := by
      apply Finset.sum_le_sum
      intro i _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul_left _ (hx i)
    _ = (∑ i, (c i).natAbs) * K := (Finset.sum_mul ..).symm

/-- The bounded integer winding is derived from residues and phases. -/
theorem bounded_winding {ι : Type} [Fintype ι] (M C : Nat) (hM : 0 < M)
    (c y phase : ι → Int) (hc : ∑ i, (c i).natAbs = C)
    (hy : ∀ i, 0 ≤ y i ∧ y i < (M : Int))
    (hphase : ∀ i, 0 ≤ phase i ∧ phase i ≤ 1)
    (hrel : Int.ModEq (M : Int) (∑ i, c i * y i) (∑ i, c i * phase i)) :
    ∃ ell : Int, ell.natAbs ≤ C ∧
      (∑ i, c i * y i) = ell * M + (∑ i, c i * phase i) := by
  obtain ⟨ell, he⟩ := hrel.symm.dvd
  have hdiff : (∑ i, c i * (y i - phase i)) = ell * M := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    nlinarith only [he]
  have hsmall : ∀ i, (y i - phase i).natAbs ≤ M := by
    intro i
    have h1 := hy i
    have h2 := hphase i
    omega
  have hbound := weighted_abs_bound c (fun i => y i - phase i) M hsmall
  rw [hdiff, Int.natAbs_mul, Int.natAbs_natCast, hc] at hbound
  refine ⟨ell, by nlinarith, ?_⟩
  nlinarith only [he]

def stationaryOffsetBound (d G : Nat) : Nat := (4 * d + 1) * G + 2 * d

/-- Exact coordinate substitution produces one of a fixed finite interval
of congruences modulo the number of original old symbols. -/
theorem old_relation_of_offsets {ι : Type} [Fintype ι]
    (m G d : Nat) (c x e y : ι → Int) (ell phase : Int)
    (hc : ∑ i, (c i).natAbs = 2 * d)
    (he : ∀ i, (e i).natAbs ≤ G) (hy : ∀ i, y i = x i + e i)
    (hell : ell.natAbs ≤ 2 * d + 1) (hphase : phase.natAbs ≤ 2 * d)
    (hrel : (∑ i, c i * y i) = ell * (m + G) + phase) :
    ∃ b : Int, b.natAbs ≤ stationaryOffsetBound d G ∧
      Int.ModEq (m : Int) (∑ i, c i * x i) b := by
  let b := ell * G + phase - ∑ i, c i * e i
  have hsum : (∑ i, c i * y i) = (∑ i, c i * x i) + (∑ i, c i * e i) := by
    simp_rw [hy, mul_add]
    exact Finset.sum_add_distrib
  have herror := weighted_abs_bound c e G he
  rw [hc] at herror
  have hmain : (ell * G).natAbs ≤ (2 * d + 1) * G := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_right _ hell
  have hb1 := Int.natAbs_sub_le (ell * G + phase) (∑ i, c i * e i)
  have hb2 := Int.natAbs_add_le (ell * G) phase
  refine ⟨b, ?_, ?_⟩
  · change (ell * G + phase - ∑ i, c i * e i).natAbs ≤ stationaryOffsetBound d G
    unfold stationaryOffsetBound
    nlinarith
  · apply Int.modEq_iff_dvd.mpr
    refine ⟨-ell, ?_⟩
    dsimp [b]
    push_cast at hrel
    nlinarith only [hrel, hsum]

/-- The actual guard renderer and an actual cyclic stationary frame give a
foreign stationary event from the stated finite coefficient catalogue. -/
theorem actual_stationary_event {m G d : Nat} {α : Type}
    (hm : 0 < m) (hd : 2 ≤ d) (old : Fin m → α) (guard : Fin G → α)
    (cuts : Fin G → Fin m) (ho : Function.Injective old)
    (hg : Function.Injective guard) (hcross : ∀ j i, guard j ≠ old i)
    (assignment : Assignment d) (y : Fin (d + 2) → Fin (m + G))
    (q : Fin (d + 2) → Int) (phase : Fin (d + 2) → Fin 2) (t : Int)
    (hq : Int.ModEq ((m + G : Nat) : Int) (∑ i, weight assignment i * q i) 0)
    (hy : ∀ i, Int.ModEq ((m + G : Nat) : Int) (y i).val
      (q i + t + (phase i).val)) :
    ∃ x : Fin (d + 2) → Fin m, ∃ e : Fin (d + 2) → Nat, ∃ b : Int,
      (∀ i, e i ≤ G ∧ (y i).val = (x i).val + e i) ∧
      b.natAbs ≤ stationaryOffsetBound d G ∧
      Int.ModEq (m : Int) (∑ i, weight assignment i * (x i).val) b := by
  have hpositions (i : Fin (d + 2)) :
      ∃ x : Fin m, ∃ e ≤ G, (y i).val = x.val + e := by
    apply position_offset old guard cuts ho hg hcross
    rw [render_length old guard cuts ho hg hcross]
    exact (y i).isLt
  choose x e he hxe using hpositions
  have hsum := weight_abs_sum hd assignment
  have hphase (i : Fin (d + 2)) :
      0 ≤ ((phase i).val : Int) ∧ ((phase i).val : Int) ≤ 1 := by
    have hi := (phase i).isLt
    omega
  have hframe := frame_relation ((m + G : Nat) : Int) t (weight assignment) q
    (fun i => ((phase i).val : Int)) (fun i => ((y i).val : Int))
    (weight_sum assignment) hq hy
  obtain ⟨ell, hell, hrel⟩ := bounded_winding (m + G) (2 * d) (by omega)
    (weight assignment) (fun i => ((y i).val : Int))
    (fun i => ((phase i).val : Int)) hsum
    (fun i => by have hi := (y i).isLt; omega) hphase hframe
  have hph := weighted_abs_bound (weight assignment)
    (fun i => ((phase i).val : Int)) 1 (fun i => by have hi := hphase i; omega)
  rw [hsum, Nat.mul_one] at hph
  obtain ⟨b, hb, hmod⟩ := old_relation_of_offsets m G d (weight assignment)
    (fun i => ((x i).val : Int)) (fun i => (e i : Int)) (fun i => ((y i).val : Int))
    ell (∑ i, weight assignment i * (phase i).val) hsum
    (fun i => by simpa only [Int.natAbs_natCast] using he i)
    (fun i => by exact_mod_cast hxe i) (by omega) hph (by simpa only [Nat.cast_add] using hrel)
  exact ⟨x, e, b, fun i => ⟨he i, hxe i⟩, hb, hmod⟩

end CoefficientTwoPrecision.GuardEvents

#print axioms CoefficientTwoPrecision.GuardEvents.reanchor_relation
#print axioms CoefficientTwoPrecision.GuardEvents.bounded_winding
#print axioms CoefficientTwoPrecision.GuardEvents.actual_stationary_event
