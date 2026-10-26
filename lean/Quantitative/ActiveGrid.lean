import IntegerControlGrid
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.ModEq

/-!
# The actual finite active-block grid and its incidence counts

Controls are labelled grid points. Blocks are labelled slope/intercept
pairs and are actual finite sets of controls. No field or primality
hypothesis is used. Each control lies in exactly A blocks because a fixed
slope has one uniquely determined intercept.
-/

namespace CoefficientTwoPrecision.ActiveGrid

abbrev Control (r A : Nat) := Fin r × Fin (r * A)
abbrev Block (r A : Nat) := Fin A × Fin (r * A)

def controlAt (r A : Nat) (hr : 0 < r) (hA : 0 < A)
    (b : Block r A) (i : Fin r) : Control r A :=
  (i, ⟨IntegerControlGrid.column r A b.1.val b.2.val i.val,
    Nat.mod_lt _ (Nat.mul_pos hr hA)⟩)

def activeBlock (r A : Nat) (hr : 0 < r) (hA : 0 < A) (b : Block r A) : Finset (Control r A) :=
  Finset.univ.image (controlAt r A hr hA b)

theorem mem_activeBlock (r A : Nat) (hr : 0 < r) (hA : 0 < A)
    (b : Block r A) (p : Control r A) :
    p ∈ activeBlock r A hr hA b ↔
      p.2.val = IntegerControlGrid.column r A b.1.val b.2.val p.1.val := by
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    rfl
  · intro hp
    refine Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, ?_⟩
    unfold controlAt
    apply Prod.ext
    · rfl
    · apply Fin.ext
      exact hp.symm

theorem activeBlock_card (r A : Nat) (hr : 0 < r) (hA : 0 < A) (b : Block r A) :
    (activeBlock r A hr hA b).card = r := by
  have hi : Function.Injective (controlAt r A hr hA b) := by
    intro i j hij
    exact congrArg Prod.fst hij
  rw [activeBlock, Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]

theorem activeBlock_inter_card (r A : Nat) (hr : 0 < r) (hA : 0 < A)
    (b c : Block r A) (hne : b ≠ c) :
    ((activeBlock r A hr hA b) ∩ (activeBlock r A hr hA c)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have hdist : (b.1.val, b.2.val) ≠ (c.1.val, c.2.val) := by
    intro he
    exact hne (Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he)))
  have hp' := Finset.mem_inter.mp hp
  have hq' := Finset.mem_inter.mp hq
  have he := IntegerControlGrid.intersection_at_most_one r A b.1.val c.1.val b.2.val c.2.val
    b.1.isLt c.1.isLt b.2.isLt c.2.isLt hdist (p.1.val, p.2.val) (q.1.val, q.2.val)
    ⟨p.1.isLt, (mem_activeBlock r A hr hA b p).mp hp'.1⟩
    ⟨p.1.isLt, (mem_activeBlock r A hr hA c p).mp hp'.2⟩
    ⟨q.1.isLt, (mem_activeBlock r A hr hA b q).mp hq'.1⟩
    ⟨q.1.isLt, (mem_activeBlock r A hr hA c q).mp hq'.2⟩
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

def interceptThrough (r A : Nat) (hr : 0 < r) (hA : 0 < A)
    (a : Fin A) (p : Control r A) : Fin (r * A) :=
  ⟨(p.2.val + r * A - (a.val * p.1.val) % (r * A)) % (r * A),
    Nat.mod_lt _ (Nat.mul_pos hr hA)⟩

theorem column_interceptThrough (r A : Nat) (hr : 0 < r) (hA : 0 < A)
    (a : Fin A) (p : Control r A) :
    IntegerControlGrid.column r A a.val (interceptThrough r A hr hA a p).val p.1.val = p.2.val := by
  have hs : (a.val * p.1.val) % (r * A) < r * A := Nat.mod_lt _ (Nat.mul_pos hr hA)
  unfold IntegerControlGrid.column interceptThrough
  simp only [Fin.val_mk, Nat.add_mod_mod]
  rw [← Nat.mod_add_mod]
  have he : (a.val * p.1.val) % (r * A) +
      (p.2.val + r * A - (a.val * p.1.val) % (r * A)) = p.2.val + r * A := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt p.2.isLt]

theorem intercept_unique (r A : Nat) (a : Fin A) (i : Fin r) (b c : Fin (r * A))
    (he : IntegerControlGrid.column r A a.val b.val i.val =
      IntegerControlGrid.column r A a.val c.val i.val) : b = c := by
  apply Fin.ext
  exact (Nat.ModEq.add_left_cancel (Nat.ModEq.refl (a.val * i.val)) he).eq_of_lt_of_lt b.isLt c.isLt

def blocksThrough (r A : Nat) (hr : 0 < r) (hA : 0 < A) (p : Control r A) : Finset (Block r A) :=
  Finset.univ.filter (fun b => p ∈ activeBlock r A hr hA b)

/-- Exactly one block of each slope passes through each control. -/
theorem blocksThrough_card (r A : Nat) (hr : 0 < r) (hA : 0 < A) (p : Control r A) :
    (blocksThrough r A hr hA p).card = A := by
  have hinj : Set.InjOn (fun b : Block r A => b.1) (blocksThrough r A hr hA p) := by
    intro b hb c hc hbc
    have hb' := (mem_activeBlock r A hr hA b p).mp (Finset.mem_filter.mp hb).2
    have hc' := (mem_activeBlock r A hr hA c p).mp (Finset.mem_filter.mp hc).2
    have hcols : IntegerControlGrid.column r A b.1.val b.2.val p.1.val =
        IntegerControlGrid.column r A b.1.val c.2.val p.1.val := by
      simpa only [hbc] using hb'.symm.trans hc'
    exact Prod.ext hbc (intercept_unique r A b.1 p.1 b.2 c.2 hcols)
  have himage : (blocksThrough r A hr hA p).image (fun b => b.1) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    refine Finset.mem_image.mpr ⟨(a, interceptThrough r A hr hA a p), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (mem_activeBlock r A hr hA _ p).mpr
    exact (column_interceptThrough r A hr hA a p).symm
  calc
    (blocksThrough r A hr hA p).card
        = ((blocksThrough r A hr hA p).image (fun b => b.1)).card :=
          (Finset.card_image_iff.mpr hinj).symm
    _ = A := by rw [himage, Finset.card_univ, Fintype.card_fin]

theorem controls_card (r A : Nat) : Fintype.card (Control r A) = r * (r * A) := by
  simp [Control]

theorem blocks_card (r A : Nat) : Fintype.card (Block r A) = A * (r * A) := by
  simp [Block]

end CoefficientTwoPrecision.ActiveGrid

#print axioms CoefficientTwoPrecision.ActiveGrid.activeBlock_inter_card
#print axioms CoefficientTwoPrecision.ActiveGrid.blocksThrough_card
