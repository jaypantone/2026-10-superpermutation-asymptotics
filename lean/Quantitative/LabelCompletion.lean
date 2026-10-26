import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# Completing two missing labels

An envelope intersection matches all but at most two controls. For a fixed
positional matching, at most two bijective initial assignments extend the
retained assignments. This count is made on labelled frames, before any
packing is selected.
-/

namespace CoefficientTwoPrecision.LabelCompletion

theorem equiv_eq_of_agree_except_one {α β : Type*} (s t : α ≃ β) (missing : α)
    (h : ∀ x, x ≠ missing → s x = t x) : s = t := by
  apply Equiv.ext
  intro x
  by_cases hx : x = missing
  · subst x
    let y := t.symm (s missing)
    have hy : t y = s missing := t.apply_symm_apply _
    by_cases hym : y = missing
    · simpa only [hym] using hy.symm
    · have hsy : s y = s missing := (h y hym).trans hy
      exact False.elim (hym (s.injective hsy))
  · exact h x hx

theorem two_missing_image {α β : Type*} (s t : α ≃ β) (a b : α)
    (h : ∀ x, x ≠ a → x ≠ b → s x = t x) : s a = t a ∨ s a = t b := by
  let y := t.symm (s a)
  have hy : t y = s a := t.apply_symm_apply _
  by_cases hya : y = a
  · exact Or.inl (by simpa only [hya] using hy.symm)
  · by_cases hyb : y = b
    · exact Or.inr (by simpa only [hyb] using hy.symm)
    · have hsa : s y = s a := (h y hya hyb).trans hy
      exact False.elim (hya (s.injective hsa))

/-- At most two bijections extend a specified assignment outside two slots. -/
theorem extensions_card_le_two {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (reference : α ≃ β) (a b : α) :
    (Finset.univ.filter (fun s : α ≃ β =>
      ∀ x, x ≠ a → x ≠ b → s x = reference x)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun s : α ≃ β =>
    ∀ x, x ≠ a → x ≠ b → s x = reference x)
  have hmap : Set.MapsTo (fun s : α ≃ β => s a) (S : Set (α ≃ β))
      ({reference a, reference b} : Finset β) := by
    intro s hs
    change s a ∈ ({reference a, reference b} : Finset β)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (two_missing_image s reference a b (Finset.mem_filter.mp hs).2)
  have hinj : (S : Set (α ≃ β)).InjOn (fun s => s a) := by
    intro s hs t ht ha
    apply equiv_eq_of_agree_except_one s t b
    intro x hxb
    by_cases hxa : x = a
    · simpa only [hxa] using ha
    · exact ((Finset.mem_filter.mp hs).2 x hxa hxb).trans
        ((Finset.mem_filter.mp ht).2 x hxa hxb).symm
  exact (Finset.card_le_card_of_injOn _ hmap hinj).trans Finset.card_le_two

end CoefficientTwoPrecision.LabelCompletion

#print axioms CoefficientTwoPrecision.LabelCompletion.extensions_card_le_two
