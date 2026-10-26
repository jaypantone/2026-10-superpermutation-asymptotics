import Quantitative.PhasedControlOrder
import Quantitative.CyclicMatching
import Quantitative.ActualMatching

/-!
# Retaining all but one stationary control in an actual row

The increasing physical slots, after deleting one slot, are enumerated by
`Fin.succAbove`. Applying the actual row filter therefore produces precisely
the retained-label list used by the reconstruction catalogue, up to rotation.
-/

namespace CoefficientTwoPrecision.RetainedControlOrder

open FiniteRoles ControlOrder TranslatedControlOrder

theorem finRange_except {n : Nat} (omitted : Fin (n + 1)) :
    (List.finRange (n + 1)).filter (fun i => decide (i ≠ omitted)) =
      List.ofFn omitted.succAbove := by
  have hleft := (List.pairwise_lt_finRange (n + 1)).filter
    (fun i => decide (i ≠ omitted))
  have hright : (List.ofFn omitted.succAbove).Pairwise (· < ·) := by
    rw [List.ofFn_eq_map, List.pairwise_map]
    exact (List.pairwise_lt_finRange n).imp (fun h => Fin.strictMono_succAbove omitted h)
  have hperm : ((List.finRange (n + 1)).filter (fun i => decide (i ≠ omitted))).Perm
      (List.ofFn omitted.succAbove) := by
    apply (List.perm_ext_iff_of_nodup
      (hleft.imp (fun h => ne_of_lt h)) (hright.imp (fun h => ne_of_lt h))).mpr
    intro i
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      List.mem_ofFn]
    constructor
    · intro hi
      exact Fin.exists_succAbove_eq hi
    · rintro ⟨j, rfl⟩
      exact Fin.succAbove_ne omitted j
  exact List.Perm.eq_of_pairwise' (hleft.imp (fun h => le_of_lt h))
    (hright.imp (fun h => le_of_lt h)) hperm

theorem filter_residents {n : Nat} {Control α : Type}
    (embed : Control → α) (assignment : Role (n + 1) ≃ Control)
    (omitted : Fin (n + 1)) (keep : α → Bool)
    (hkeep : ∀ i, keep (embed (assignment (some i))) = decide (i ≠ omitted)) :
    (((List.finRange (n + 1)).map (fun i => embed (assignment (some i)))).filter keep) =
      (CyclicMatching.retainedLabels assignment omitted).map embed := by
  rw [List.filter_map]
  simp only [Function.comp_def]
  have hpred : (fun i => keep (embed (assignment (some i)))) =
      (fun i => decide (i ≠ omitted)) := funext hkeep
  rw [hpred, finRange_except]
  simp only [List.map_ofFn, CyclicMatching.retainedLabels, Function.comp_def]

theorem translated_base_projection {M n : Nat} [NeZero M] {Control α : Type} [DecidableEq α]
    (background : Fin M → α) (embed : Control → α) (assignment : Role (n + 1) ≃ Control)
    (cuts : Fin (n + 1) → Fin M) (hcuts : StrictMono cuts)
    (translation : Fin M) (gap : Nat) (omitted : Fin (n + 1))
    (keep : α → Bool) (hbackground : ∀ i, keep (background i) = false)
    (hmobile : keep (embed (assignment none)) = false)
    (hkeep : ∀ i, keep (embed (assignment (some i))) = decide (i ≠ omitted)) :
    ((CyclicMatching.retainedLabels assignment omitted).map embed).IsRotated
      ((ActualMatching.base background embed assignment
        (fun i => cuts i + translation) gap).filter keep) := by
  have h := TranslatedControlOrder.base_control_order background
    (fun i => embed (assignment (some i))) cuts hcuts translation (embed (assignment none))
    gap keep hbackground hmobile
  rw [filter_residents embed assignment omitted keep hkeep] at h
  exact h

end CoefficientTwoPrecision.RetainedControlOrder

#print axioms CoefficientTwoPrecision.RetainedControlOrder.finRange_except
#print axioms CoefficientTwoPrecision.RetainedControlOrder.translated_base_projection
