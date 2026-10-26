import Quantitative.FullRunSimplicity

/-!
# The only possible return across one short update

For a nodup short source ending in resident, crossed background, mobile,
the only post-update full gap with the same cyclic class is the last gap
before completing the stationary circuit. Thus a full run that stops
before that gap cannot repeat the short source. The robust geometry must
still prove the needed stopping bound for successive distinct targets.
-/

namespace CoefficientTwoPrecision.ShortBoundarySimplicity

open LiteralState

variable {α : Type}

def newStationary (pre : List α) (crossed mobile : α) : List α :=
  mobile :: (pre ++ [crossed])

theorem shortStep_as_base (pre : List α) (resident crossed mobile : α) :
    shortStep (pre ++ [resident, crossed, mobile]) =
      newStationary pre crossed mobile ++ [resident] := by
  rw [shortStep_suffix]
  simp [newStationary, List.append_assoc]

theorem old_source_is_last_gap (pre : List α) (resident crossed mobile : α) :
    (pre ++ [resident, crossed, mobile]).IsRotated
      ((newStationary pre crossed mobile).rotate
        ((newStationary pre crossed mobile).length - 1) ++ [resident]) := by
  have hform : newStationary pre crossed mobile = (mobile :: pre) ++ [crossed] := by
    simp [newStationary]
  have hrot : (newStationary pre crossed mobile).rotate
      ((newStationary pre crossed mobile).length - 1) = crossed :: mobile :: pre := by
    rw [hform]
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    rw [List.rotate_append_length_eq]
    rfl
  rw [hrot]
  have h := List.isRotated_append (l := pre ++ [resident]) (l' := [crossed, mobile])
  simpa [List.append_assoc] using h

/-- A cyclic return after one short update can occur only at the final
stationary gap. This is an exact literal statement for arbitrary alphabets. -/
theorem one_short_return_gap (pre : List α) (resident crossed mobile : α)
    (hnodup : (pre ++ [resident, crossed, mobile]).Nodup) (j : Nat)
    (hj : j < (newStationary pre crossed mobile).length)
    (hreturn : (pre ++ [resident, crossed, mobile]).IsRotated
      (fullIterate j (shortStep (pre ++ [resident, crossed, mobile])))) :
    j = (newStationary pre crossed mobile).length - 1 := by
  have hnew : (newStationary pre crossed mobile ++ [resident]).Nodup := by
    rw [← shortStep_as_base]
    exact shortStep_nodup pre resident crossed mobile hnodup
  have hstationary : (newStationary pre crossed mobile).Nodup :=
    (List.nodup_append.mp hnew).1
  have hfresh : resident ∉ newStationary pre crossed mobile := by
    intro hmem
    exact (List.nodup_append.mp hnew).2.2 resident hmem resident (by simp) rfl
  have hlen : 0 < (newStationary pre crossed mobile).length := by
    simp [newStationary]
  rw [shortStep_as_base, fullIterate_formula, rotateLeft_eq_rotate] at hreturn
  have hcompare := (old_source_is_last_gap pre resident crossed mobile).symm.trans hreturn
  have heq := SourceUniverse.insertion_class_injective hstationary hfresh
    (by omega : (newStationary pre crossed mobile).length - 1 <
      (newStationary pre crossed mobile).length) hj hcompare
  exact heq.symm

theorem no_short_return_before_last_gap (pre : List α) (resident crossed mobile : α)
    (hnodup : (pre ++ [resident, crossed, mobile]).Nodup) (j : Nat)
    (hj : j < (newStationary pre crossed mobile).length - 1) :
    ¬ (pre ++ [resident, crossed, mobile]).IsRotated
      (fullIterate j (shortStep (pre ++ [resident, crossed, mobile]))) := by
  intro hreturn
  have heq := one_short_return_gap pre resident crossed mobile hnodup j (by omega) hreturn
  omega

end CoefficientTwoPrecision.ShortBoundarySimplicity

#print axioms CoefficientTwoPrecision.ShortBoundarySimplicity.one_short_return_gap
#print axioms CoefficientTwoPrecision.ShortBoundarySimplicity.no_short_return_before_last_gap
