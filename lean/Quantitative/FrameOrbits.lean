import Quantitative.FrameCounting
import Mathlib.Data.Fintype.Perm

/-!
# Removing the coordinate-order multiplicity

An injective ordered d-tuple with a fixed image differs from any chosen
representative by a permutation of its d indices. Thus each image has at
most d! ordered representatives. Applying this to the actual good frame
set proves a finite lower bound for distinct coordinate sets.
-/

namespace CoefficientTwoPrecision.FrameOrbits

open FrameCounting FrameAlgebra RobustMatching

theorem cuts_coordinate {M d : Nat} (x : Fin d → Fin M) (j : Fin d) :
    cuts x (some (some j)) = (x j).val := by
  simp [cuts, coordinate, ite_mul]

theorem good_injective {M d : Nat} {x : Fin d → Fin M}
    (hx : x ∈ goodFrames M d) : Function.Injective x := by
  intro i j hij
  have hcuts : cuts x (some (some i)) = cuts x (some (some j)) := by
    rw [cuts_coordinate, cuts_coordinate, hij]
  have h := robust_injective (cuts x) (goodFrames_robust hx) hcuts
  exact Option.some.inj (Option.some.inj h)

def coordinateSet {M d : Nat} (x : Fin d → Fin M) : Finset (Fin M) :=
  Finset.univ.image x

theorem same_image_permutation {M d : Nat} (x y : Fin d → Fin M)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (himage : coordinateSet x = coordinateSet y) :
    ∃ e : Equiv.Perm (Fin d), ∀ i, x i = y (e i) := by
  classical
  have hpre (i : Fin d) : ∃ j, y j = x i := by
    have hm : x i ∈ coordinateSet x := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [himage] at hm
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact ⟨j, hj⟩
  choose f hf using hpre
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hx
    rw [← hf i, ← hf j, hij]
  let e := Equiv.ofBijective f ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  exact ⟨e, fun i => (hf i).symm⟩

theorem fixed_image_card_le (M d : Nat) (A : Finset (Fin M)) :
    ((goodFrames M d).filter (fun x => coordinateSet x = A)).card ≤ d.factorial := by
  classical
  let S := (goodFrames M d).filter (fun x => coordinateSet x = A)
  rcases S.eq_empty_or_nonempty with hS | ⟨y, hy⟩
  · change S.card ≤ d.factorial
    rw [hS, Finset.card_empty]
    exact Nat.zero_le _
  · have hygood : y ∈ goodFrames M d := (Finset.mem_filter.mp hy).1
    have hperm (x : S) : ∃ e : Equiv.Perm (Fin d), ∀ i, x.val i = y (e i) := by
      have hxgood := (Finset.mem_filter.mp x.property).1
      have hset := (Finset.mem_filter.mp x.property).2.trans (Finset.mem_filter.mp hy).2.symm
      exact same_image_permutation x.val y (good_injective hxgood) (good_injective hygood) hset
    choose f hf using hperm
    have hfinj : Function.Injective f := by
      intro x z hxz
      apply Subtype.ext
      funext i
      rw [hf x i, hf z i, hxz]
    have hcard := Fintype.card_le_of_injective f hfinj
    simpa only [Fintype.card_coe, Fintype.card_perm, Fintype.card_fin] using hcard

def frames (M d : Nat) : Finset (Finset (Fin M)) :=
  (goodFrames M d).image coordinateSet

theorem ordered_card_le (M d : Nat) :
    (goodFrames M d).card ≤ (frames M d).card * d.factorial := by
  classical
  apply FiniteFibers.card_le_of_fiber_bound (goodFrames M d) (frames M d) coordinateSet
    d.factorial
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro A _
    exact fixed_image_card_le M d A

/-- The explicit count for distinct modular coordinate sets. Each member
has a robust ordered representative; their order multiplicity has been
removed by a proved factorial bound. -/
theorem frames_card_lower (M d : Nat) (hM : 0 < M) (hd : 3 ≤ d) :
    M ^ d ≤ (frames M d).card * d.factorial +
      18 * (d + 2) ^ 4 * M ^ (d - 1) := by
  exact (goodFrames_card M d hM hd).trans (Nat.add_le_add_right (ordered_card_le M d) _)

theorem frame_has_robust_representative {M d : Nat} {A : Finset (Fin M)}
    (hA : A ∈ frames M d) :
    ∃ x : Fin d → Fin M, coordinateSet x = A ∧ Function.Injective x ∧ Robust (cuts x) := by
  obtain ⟨x, hx, hset⟩ := Finset.mem_image.mp hA
  exact ⟨x, hset, good_injective hx, goodFrames_robust hx⟩

end CoefficientTwoPrecision.FrameOrbits

#print axioms CoefficientTwoPrecision.FrameOrbits.frames_card_lower
#print axioms CoefficientTwoPrecision.FrameOrbits.frame_has_robust_representative
