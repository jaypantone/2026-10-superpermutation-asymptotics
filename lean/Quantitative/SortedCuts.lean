import Quantitative.RobustMatching
import Mathlib.Data.Finset.Sort
import Mathlib.Data.ZMod.Basic

/-!
# Sorting robust cuts without forgetting their identities

The increasing tuple is accompanied by the actual bijection from sorted
positions to the original formal points. Robustness is preserved by this
change of indices. If the original tuple contains zero, sorting puts its
unique zero point in position zero.
-/

namespace CoefficientTwoPrecision.SortedCuts

open RobustMatching

variable {M : Nat} {α β : Type} [DecidableEq α] [DecidableEq β]

def mapIndex (f : α → β) (hf : Function.Injective f) :
    DifferenceIndex α → DifferenceIndex β
  | none => none
  | some p => some ⟨(f p.val.1, f p.val.2), fun h => p.property (hf h)⟩

theorem mapIndex_injective (f : α → β) (hf : Function.Injective f) :
    Function.Injective (mapIndex f hf) := by
  intro a b hab
  cases a with
  | none => cases b <;> simpa [mapIndex] using hab
  | some a =>
    cases b with
    | none => simp [mapIndex] at hab
    | some b =>
      have heq : (f a.val.1, f a.val.2) = (f b.val.1, f b.val.2) := by
        exact congrArg Subtype.val (Option.some.inj hab)
      exact congrArg some (Subtype.ext (Prod.ext
        (hf (congrArg Prod.fst heq)) (hf (congrArg Prod.snd heq))))

theorem robust_comp (q : β → ZMod M) (hrobust : Robust q)
    (f : α → β) (hf : Function.Injective f) : Robust (q ∘ f) := by
  intro a b offset hlo hhi heq
  apply mapIndex_injective f hf
  apply hrobust _ _ offset hlo hhi
  have hdiff (i : DifferenceIndex α) :
      difference q (mapIndex f hf i) = difference (q ∘ f) i := by
    cases i <;> rfl
  simpa only [hdiff] using heq

/-- An increasing list of actual residue representatives, together with
the exact original point represented at each position. -/
theorem exists_sorted [NeZero M] [Fintype α]
    (q : α → ZMod M) (hrobust : Robust q) (k : Nat) (hcard : Fintype.card α = k) :
    ∃ sorted : Fin k → Fin M, ∃ order : Fin k ≃ α,
      StrictMono sorted ∧ (∀ i, (sorted i).val = (q (order i)).val) ∧
        Robust (fun i => ((sorted i).val : ZMod M)) := by
  classical
  let value (a : α) : Fin M := ⟨(q a).val, ZMod.val_lt _⟩
  have hinj : Function.Injective value := by
    intro a b hab
    apply robust_injective q hrobust
    exact ZMod.val_injective M (congrArg Fin.val hab)
  let S : Finset (Fin M) := Finset.univ.image value
  have hS : S.card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard]
  let toImage (a : α) : S := ⟨value a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have hbij : Function.Bijective toImage := by
    constructor
    · intro a b h
      exact hinj (congrArg Subtype.val h)
    · intro y
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp y.property
      exact ⟨a, Subtype.ext ha⟩
  let imageEquiv : α ≃ S := Equiv.ofBijective toImage hbij
  let order : Fin k ≃ α := (S.orderIsoOfFin hS).toEquiv.trans imageEquiv.symm
  let sorted : Fin k → Fin M := S.orderEmbOfFin hS
  have hvalue (i : Fin k) : value (order i) = sorted i := by
    exact congrArg Subtype.val (imageEquiv.apply_symm_apply (S.orderIsoOfFin hS i))
  have hcast (i : Fin k) : ((sorted i).val : ZMod M) = q (order i) := by
    rw [← hvalue]
    exact ZMod.natCast_zmod_val _
  refine ⟨sorted, order, (S.orderEmbOfFin hS).strictMono, ?_, ?_⟩
  · intro i
    exact (congrArg Fin.val (hvalue i)).symm
  · have hfun : (fun i => ((sorted i).val : ZMod M)) = q ∘ order := funext hcast
    rw [hfun]
    exact robust_comp q hrobust order order.injective

theorem sorted_zero [NeZero M] [Fintype α]
    (q : α → ZMod M) (k : Nat) (hk : 0 < k)
    (sorted : Fin k → Fin M) (order : Fin k ≃ α) (hmono : StrictMono sorted)
    (hvalue : ∀ i, (sorted i).val = (q (order i)).val)
    (anchor : α) (hanchor : q anchor = 0) : sorted ⟨0, hk⟩ = 0 := by
  have hat : (sorted (order.symm anchor)).val = 0 := by
    rw [hvalue, order.apply_symm_apply, hanchor]
    simp
  have hle := hmono.monotone (show (⟨0, hk⟩ : Fin k) ≤ order.symm anchor by
    change 0 ≤ (order.symm anchor).val
    exact Nat.zero_le _)
  apply Fin.ext
  change (sorted ⟨0, hk⟩).val = 0
  change (sorted ⟨0, hk⟩).val ≤ (sorted (order.symm anchor)).val at hle
  omega

end CoefficientTwoPrecision.SortedCuts

#print axioms CoefficientTwoPrecision.SortedCuts.exists_sorted
#print axioms CoefficientTwoPrecision.SortedCuts.sorted_zero
