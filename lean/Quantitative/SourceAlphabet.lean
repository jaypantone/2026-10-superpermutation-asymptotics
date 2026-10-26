import Quantitative.SourceProjection
import Quantitative.ActualPrefix
import Quantitative.RowValidity

/-!
# Alphabet validity and insertion erasure of the constructed literal rows

The alphabet hypotheses below specify the background and active control
symbols, not a row certificate. The trace preserves this alphabet. Its
old-letter projection is the filtered background cyclic order, even when
the background contains inactive guard controls.
-/

namespace CoefficientTwoPrecision.SourceAlphabet

open LiteralState StationaryCircle StationaryUpdate LiteralSchedule PositiveSchedule TargetTrace
open FiniteRoles ActualPrefix RowValidity SourceProjection SourceUniverse
open SuperpermutationUpperBound

variable {M k : Nat} {Control : Type}

def engineLabels (embed : Control → Nat) (assignment : Role k ≃ Control) : Option Nat → Nat :=
  fun p => embed (lift assignment p)

theorem residents_injective (embed : Control → Nat) (hembed : Function.Injective embed)
    (assignment : Role k ≃ Control) :
    Function.Injective (residents (k := k) (engineLabels embed assignment)) :=
  hembed.comp (FiniteRoles.residents_injective assignment)

theorem residents_disjoint (background : Fin M → Nat) (embed : Control → Nat)
    (hdisjoint : ∀ c i, embed c ≠ background i) (assignment : Role k ≃ Control) :
    ∀ (j : Fin k) (i : Fin M), residents (engineLabels embed assignment) j ≠ background i := by
  intro j i
  exact hdisjoint (lift assignment (some j.val)) i

theorem base_nodup (background : Fin M → Nat) (embed : Control → Nat)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (hdisjoint : ∀ c i, embed c ≠ background i) (assignment : Role k ≃ Control)
    (cuts : Fin k → Fin M) (gap : Nat) :
    (renderedBase background (engineLabels embed assignment) cuts gap).Nodup := by
  have hplain := StationaryUpdate.base_nodup background (residents (engineLabels embed assignment)) cuts
    hbackground (residents_injective embed hembed assignment)
    (residents_disjoint background embed hdisjoint assignment)
    (engineLabels embed assignment none)
    (fun i => Ne.symm (hdisjoint (assignment none) i))
    (fun j heq => mobile_ne_resident assignment j (hembed heq.symm))
  have hp : (renderedBase background (engineLabels embed assignment) cuts gap).Perm
      (render background (residents (engineLabels embed assignment)) cuts ++ [engineLabels embed assignment none]) := by
    unfold renderedBase
    rw [LiteralState.rotateLeft_eq_rotate]
    exact (List.rotate_perm _ gap).append_right _
  exact hp.nodup_iff.mpr hplain

theorem base_length (background : Fin M → Nat) (embed : Control → Nat)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (hdisjoint : ∀ c i, embed c ≠ background i) (assignment : Role k ≃ Control)
    (cuts : Fin k → Fin M) (gap : Nat) :
    (renderedBase background (engineLabels embed assignment) cuts gap).length = M + k + 1 := by
  simp only [renderedBase, List.length_append, List.length_singleton,
    LiteralState.rotateLeft_eq_rotate, List.length_rotate]
  rw [render_length background _ cuts hbackground (residents_injective embed hembed assignment)
    (residents_disjoint background embed hdisjoint assignment)]

theorem base_support (background : Fin M → Nat) (embed : Control → Nat)
    (assignment : Role k ≃ Control) (cuts : Fin k → Fin M) (gap symbol : Nat) :
    symbol ∈ renderedBase background (engineLabels embed assignment) cuts gap ↔
      (∃ i, background i = symbol) ∨ ∃ c, embed c = symbol := by
  constructor
  · intro hmem
    rcases List.mem_append.mp hmem with hstationary | hmobile
    · rw [LiteralState.rotateLeft_eq_rotate, List.mem_rotate] at hstationary
      rcases (mem_render background (residents (engineLabels embed assignment)) cuts symbol).mp hstationary with
        ⟨i, hi⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨i, hi⟩
      · exact Or.inr ⟨lift assignment (some j.val), hj⟩
    · have hm : symbol = engineLabels embed assignment none := List.mem_singleton.mp hmobile
      exact Or.inr ⟨assignment none, hm.symm⟩
  · rintro (⟨i, hi⟩ | ⟨c, hc⟩)
    · apply List.mem_append_left
      rw [LiteralState.rotateLeft_eq_rotate, List.mem_rotate]
      exact (mem_render background (residents (engineLabels embed assignment)) cuts symbol).mpr (Or.inl ⟨i, hi⟩)
    · obtain ⟨role, hrole⟩ := assignment.surjective c
      cases role with
      | none =>
        apply List.mem_append_right
        apply List.mem_singleton.mpr
        exact ((congrArg embed hrole).trans hc).symm
      | some j =>
        apply List.mem_append_left
        rw [LiteralState.rotateLeft_eq_rotate, List.mem_rotate]
        apply (mem_render background (residents (engineLabels embed assignment)) cuts symbol).mpr
        exact Or.inr ⟨j, by simpa only [residents, engineLabels, lift_stationary] using
          (congrArg embed hrole).trans hc⟩

theorem base_perm (A : List Nat) (hA : A.Nodup)
    (background : Fin M → Nat) (embed : Control → Nat)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (hdisjoint : ∀ c i, embed c ≠ background i)
    (hsupport : ∀ a, a ∈ A ↔ (∃ i, background i = a) ∨ ∃ c, embed c = a)
    (assignment : Role k ≃ Control) (cuts : Fin k → Fin M) (gap : Nat) :
    (renderedBase background (engineLabels embed assignment) cuts gap).Perm A := by
  apply (List.perm_ext_iff_of_nodup
    (base_nodup background embed hbackground hembed hdisjoint assignment cuts gap) hA).mpr
  intro symbol
  rw [base_support, hsupport]

theorem schedule_basedOn (hM : 2 ≤ M) (A : List Nat) (hA : A.Nodup) (hsatellite : 9 ∉ A)
    (background : Fin M → Nat) (embed : Control → Nat)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (hdisjoint : ∀ c i, embed c ≠ background i)
    (hsupport : ∀ a, a ∈ A ↔ (∃ i, background i = a) ∨ ∃ c, embed c = a)
    (assignment : Role k ≃ Control) (word : List (Fin k)) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background word (engineLabels embed assignment) cuts gap sweeps finalGap) :
    BasedOn A 9 (scheduleRows 9 sweeps (renderedBase background (engineLabels embed assignment) cuts gap)) := by
  have hp := base_perm A hA background embed hbackground hembed hdisjoint hsupport assignment cuts gap
  have hvalid := trace_suffixSchedule hM background word _ cuts gap sweeps finalGap htrace
  have hrows := scheduleRows_valid 9 sweeps _ hvalid (hp.nodup_iff.mpr hA)
    (fun hmem => hsatellite (hp.mem_iff.mp hmem)) (by
      rw [base_length background embed hbackground hembed hdisjoint assignment cuts gap]
      omega)
  intro row hrow
  obtain ⟨hperm, hsat, hkind⟩ := scheduleRows_inventory 9 sweeps _ hvalid row hrow
  exact ⟨hrows row hrow, hperm.trans hp, hsat, hkind⟩

theorem schedule_insertion (hM : 2 ≤ M) (controls old : List Nat) (hold : 0 < old.length)
    (hA : (controls ++ old).Nodup)
    (background : Fin M → Nat) (embed : Control → Nat)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (hdisjoint : ∀ c i, embed c ≠ background i)
    (hsupport : ∀ a, a ∈ controls ++ old ↔ (∃ i, background i = a) ∨ ∃ c, embed c = a)
    (hcontrols : ∀ c, embed c ∈ controls)
    (hprojection : CyclicEq old (((List.finRange M).map background).filter (fun a => decide (a ∉ controls))))
    (assignment : Role k ≃ Control) (word : List (Fin k)) (cuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace (by omega) background word (engineLabels embed assignment) cuts gap sweeps finalGap)
    (row : Row Nat) (hrow : row ∈ scheduleRows 9 sweeps (renderedBase background (engineLabels embed assignment) cuts gap)) :
    InsertionAbove controls old row.base := by
  have hp := base_perm (controls ++ old) hA background embed hbackground hembed hdisjoint hsupport assignment cuts gap
  have hvalid := trace_suffixSchedule hM background word _ cuts gap sweeps finalGap htrace
  have hrowPerm := (scheduleRows_inventory 9 sweeps _ hvalid row hrow).1.trans hp
  apply insertionAbove_of_projection controls old row.base hold hA hrowPerm
  obtain ⟨pre, target, tail, rowGap, _, hbase⟩ :=
    row_prefix_state (show 0 < M by omega) background word _ cuts gap sweeps finalGap htrace 9 row hrow
  rw [hbase]
  have hkeep (p : Option Nat) :
      decide (executeLabels pre (engineLabels embed assignment) p ∉ controls) = false := by
    unfold engineLabels
    rw [executeLabels_map]
    simp only [decide_eq_false_iff_not, not_not]
    exact hcontrols _
  have hne : (((List.finRange M).map background).filter (fun a => decide (a ∉ controls))) ≠ [] := by
    intro heq
    have hl := hprojection.length_eq
    rw [heq, List.length_nil] at hl
    omega
  exact hprojection.trans (rendered_base_projection background _ _ _ rowGap _
    (fun j => hkeep (some j.val)) (hkeep none) hne)

end CoefficientTwoPrecision.SourceAlphabet

#print axioms CoefficientTwoPrecision.SourceAlphabet.schedule_basedOn
#print axioms CoefficientTwoPrecision.SourceAlphabet.schedule_insertion
