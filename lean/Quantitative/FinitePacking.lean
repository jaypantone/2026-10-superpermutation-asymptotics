import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Selecting separated labelled objects

The relation in this module records forbidden pairs of labelled objects.
Its degree bound includes the selected object itself. Consequently, when
distinct objects have at most Delta forbidden neighbours, the parameter
in this theorem is Delta + 1. Identical envelopes remain distinct vertices
when their labels differ; the relation, rather than an image operation,
removes such collisions.
-/

namespace CoefficientTwoPrecision.FinitePacking

/-- A finite relation with at most D forbidden choices per vertex admits
a separated subset whose cardinality, multiplied by D, covers the original
cardinality. The proof removes a full forbidden neighbourhood at each step. -/
theorem exists_separated {α : Type*} [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R]
    (hsymm : ∀ {x y}, R x y → R y x) (href : ∀ x, R x x)
    (D : Nat) (V : Finset α)
    (hdegree : ∀ x ∈ V, (V.filter (R x)).card ≤ D) :
    ∃ S : Finset α, S ⊆ V ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y) ∧
      V.card ≤ D * S.card := by
  induction V using Finset.strongInductionOn with
  | _ V ih =>
    rcases V.eq_empty_or_nonempty with hV | ⟨a, ha⟩
    · subst V
      exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    · let B := V.filter (R a)
      let T := V \ B
      have hB : B ⊆ V := Finset.filter_subset _ _
      have haB : a ∈ B := Finset.mem_filter.mpr ⟨ha, href a⟩
      have hT : T ⊂ V := Finset.sdiff_ssubset hB ⟨a, haB⟩
      have hdegreeT : ∀ x ∈ T, (T.filter (R x)).card ≤ D := by
        intro x hx
        apply le_trans (Finset.card_le_card ?_) (hdegree x (Finset.mem_sdiff.mp hx).1)
        intro y hy
        obtain ⟨hy, hxy⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hy).1, hxy⟩
      obtain ⟨S, hST, hsep, hcard⟩ := ih T hT hdegreeT
      have haS : a ∉ S := by
        intro has
        exact (Finset.mem_sdiff.mp (hST has)).2 haB
      refine ⟨insert a S, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ha
        · exact (Finset.mem_sdiff.mp (hST hx)).1
      · intro x hx y hy hne
        rcases Finset.mem_insert.mp hx with hxa | hxS
        · subst x
          rcases Finset.mem_insert.mp hy with rfl | hyS
          · exact False.elim (hne rfl)
          · intro hay
            have hyT := Finset.mem_sdiff.mp (hST hyS)
            exact hyT.2 (Finset.mem_filter.mpr ⟨hyT.1, hay⟩)
        · rcases Finset.mem_insert.mp hy with hya | hyS
          · subst y
            intro hxa
            have hxT := Finset.mem_sdiff.mp (hST hxS)
            exact hxT.2 (Finset.mem_filter.mpr ⟨hxT.1, hsymm hxa⟩)
          · exact hsep x hxS y hyS hne
      · have hsplit : T.card + B.card = V.card :=
          Finset.card_sdiff_add_card_eq_card hB
        have hbound : B.card ≤ D := hdegree a ha
        rw [Finset.card_insert_of_notMem haS, Nat.mul_add, Nat.mul_one]
        omega

/-- Remove vertices from a separated family to obtain any smaller exact
size. This is the step that realizes the prescribed floor count. -/
theorem exists_separated_of_mul_le {α : Type*} [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R]
    (hsymm : ∀ {x y}, R x y → R y x) (href : ∀ x, R x x)
    (D : Nat) (hD : 0 < D) (V : Finset α)
    (hdegree : ∀ x ∈ V, (V.filter (R x)).card ≤ D)
    (K : Nat) (hK : D * K ≤ V.card) :
    ∃ S : Finset α, S ⊆ V ∧ S.card = K ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y) := by
  obtain ⟨T, hTV, hsep, hcard⟩ := exists_separated R hsymm href D V hdegree
  have hKT : K ≤ T.card := Nat.le_of_mul_le_mul_left (hK.trans hcard) hD
  obtain ⟨S, hST, hsize⟩ := Finset.exists_subset_card_eq hKT
  exact ⟨S, hST.trans hTV, hsize,
    fun x hx y hy hne => hsep x (hST hx) y (hST hy) hne⟩

end CoefficientTwoPrecision.FinitePacking

#print axioms CoefficientTwoPrecision.FinitePacking.exists_separated
#print axioms CoefficientTwoPrecision.FinitePacking.exists_separated_of_mul_le
