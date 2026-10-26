import Quantitative.FiniteRoles

/-!
# Deleting two control labels from two role assignments

Two rows can have different mobile controls. On each side we omit the
stationary control that is mobile on the other side. If the mobiles agree,
we omit one further common control. In both cases exactly the same controls
remain, with one stationary position omitted on each side.
-/

namespace CoefficientTwoPrecision.ControlOmissions

open FiniteRoles

theorem exists_omissions {n : Nat} {Control : Type}
    (first second : Role (n + 1) ≃ Control) :
    ∃ i j : Fin (n + 1), ∀ c,
      (c ≠ first none ∧ c ≠ first (some i)) ↔
        (c ≠ second none ∧ c ≠ second (some j)) := by
  classical
  by_cases hm : first none = second none
  · obtain ⟨role, hrole⟩ := second.surjective (first (some 0))
    cases role with
    | none =>
      have h := first.injective (hm.trans hrole)
      cases h
    | some j =>
      refine ⟨0, j, ?_⟩
      intro c
      rw [hm, hrole]
  · obtain ⟨role, hrole⟩ := first.surjective (second none)
    cases role with
    | none => exact False.elim (hm hrole)
    | some i =>
      obtain ⟨role', hrole'⟩ := second.surjective (first none)
      cases role' with
      | none => exact False.elim (hm hrole'.symm)
      | some j =>
        refine ⟨i, j, ?_⟩
        intro c
        rw [hrole, hrole']
        exact and_comm

noncomputable def keep {n : Nat} {Control α : Type}
    (embed : Control → α) (first : Role (n + 1) ≃ Control)
    (omitted : Fin (n + 1)) (symbol : α) : Bool := by
  classical
  exact decide (∃ c, embed c = symbol ∧ c ≠ first none ∧ c ≠ first (some omitted))

theorem keep_embed {n : Nat} {Control α : Type} [DecidableEq Control]
    (embed : Control → α) (hembed : Function.Injective embed)
    (first : Role (n + 1) ≃ Control) (omitted : Fin (n + 1)) (c : Control) :
    keep embed first omitted (embed c) =
      decide (c ≠ first none ∧ c ≠ first (some omitted)) := by
  classical
  simp only [keep, hembed.eq_iff, exists_eq_left]

theorem keep_background {n : Nat} {Control α : Type}
    (embed : Control → α) (first : Role (n + 1) ≃ Control)
    (omitted : Fin (n + 1)) (symbol : α)
    (hbackground : ∀ c, embed c ≠ symbol) : keep embed first omitted symbol = false := by
  classical
  simp only [keep, decide_eq_false_iff_not]
  rintro ⟨c, hc, _, _⟩
  exact hbackground c hc

theorem keep_first_mobile {n : Nat} {Control α : Type} [DecidableEq Control]
    (embed : Control → α) (hembed : Function.Injective embed)
    (first : Role (n + 1) ≃ Control) (omitted : Fin (n + 1)) :
    keep embed first omitted (embed (first none)) = false := by
  rw [keep_embed embed hembed]
  simp

theorem keep_first_stationary {n : Nat} {Control α : Type} [DecidableEq Control]
    (embed : Control → α) (hembed : Function.Injective embed)
    (first : Role (n + 1) ≃ Control) (omitted i : Fin (n + 1)) :
    keep embed first omitted (embed (first (some i))) = decide (i ≠ omitted) := by
  rw [keep_embed embed hembed]
  simp only [first.injective.ne_iff]
  simp

theorem keep_second_mobile {n : Nat} {Control α : Type} [DecidableEq Control]
    (embed : Control → α) (hembed : Function.Injective embed)
    (first second : Role (n + 1) ≃ Control) (omitted other : Fin (n + 1))
    (homit : ∀ c, (c ≠ first none ∧ c ≠ first (some omitted)) ↔
      (c ≠ second none ∧ c ≠ second (some other))) :
    keep embed first omitted (embed (second none)) = false := by
  rw [keep_embed embed hembed]
  simp only [homit, ne_eq, not_true_eq_false, false_and, decide_false]

theorem keep_second_stationary {n : Nat} {Control α : Type} [DecidableEq Control]
    (embed : Control → α) (hembed : Function.Injective embed)
    (first second : Role (n + 1) ≃ Control) (omitted other i : Fin (n + 1))
    (homit : ∀ c, (c ≠ first none ∧ c ≠ first (some omitted)) ↔
      (c ≠ second none ∧ c ≠ second (some other))) :
    keep embed first omitted (embed (second (some i))) = decide (i ≠ other) := by
  rw [keep_embed embed hembed]
  simp only [homit, second.injective.ne_iff]
  simp

end CoefficientTwoPrecision.ControlOmissions

#print axioms CoefficientTwoPrecision.ControlOmissions.exists_omissions
#print axioms CoefficientTwoPrecision.ControlOmissions.keep_second_stationary
