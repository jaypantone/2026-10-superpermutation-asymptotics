import Quantitative.TargetTrace
import Quantitative.BatchSafety
import Quantitative.SourceUniverse

/-!
# A positive sweep stops before the last stationary gap

After a short update, the stationary word ends in the crossed background
symbol, and the last target has advanced to its successor cut. At the
last possible full gap that background symbol would become first. The
next target suffix instead makes the successor of its own cut first.
Equality would put two resident cuts two background positions apart,
which robust separation excludes. This proves the needed stopping bound
without an unformalized count of crossed background symbols.
-/

namespace CoefficientTwoPrecision.StoppingBound

open JointStates LiteralState StationaryCircle StationaryUpdate StationarySuccessor
open LiteralSchedule RobustMatching RobustSafety BatchSafety

variable {M k : Nat} {α : Type}

theorem two_steps_unoccupied (hM : 3 ≤ M) (q : Fin k → ZMod M) (hrobust : Robust q)
    (translation : ZMod M) (phases : Fin k → Bool) (i j : Fin k) :
    perturbed q translation phases i ≠ perturbed q translation phases j + 2 := by
  intro hij
  let e : ℤ := bit (phases j) - bit (phases i) + 2
  have hlo : -4 ≤ e := by
    dsimp only [e]
    cases phases i <;> cases phases j <;> norm_num [bit]
  have hhi : e ≤ 4 := by
    dsimp only [e]
    cases phases i <;> cases phases j <;> norm_num [bit]
  have heq : pairIndex i j = none := by
    apply hrobust (pairIndex i j) none e hlo hhi
    rw [difference_pairIndex]
    simp only [difference, zero_add, e, Int.cast_add, Int.cast_sub, Int.cast_ofNat]
    change q i + translation + (bit (phases i) : ZMod M) =
      q j + translation + (bit (phases j) : ZMod M) + 2 at hij
    linear_combination hij
  have hijSlots := index_zero_implies_diagonal i j heq
  subst j
  have htwo : (2 : ZMod M) = 0 := by linear_combination -hij
  have hdiv : M ∣ 2 := (ZMod.natCast_eq_zero_iff 2 M).mp htwo
  have hle : M ≤ 2 := Nat.le_of_dvd (by omega) hdiv
  omega

/-- A target suffix determines the first background symbol of the
stationary rotation, because the successor cut is unoccupied. -/
theorem target_suffix_head (hM : 2 ≤ M) (background : Fin M → α)
    (resident : Fin k → α) (cuts : Fin k → Fin M)
    (hcuts : Function.Injective cuts) (hnd : (render background resident cuts).Nodup)
    (target : Fin k) (mobile : α)
    (hfree : ∀ j, cuts j ≠ successor (by omega) (cuts target))
    (gap : Nat) (pre : List α)
    (hform : (render background resident cuts).rotateLeft gap =
      pre ++ [resident target, background (cuts target)]) :
    ((render background resident cuts).rotateLeft gap).head? =
      some (background (successor (by omega) (cuts target))) := by
  obtain ⟨rest, hold, _⟩ := positive_local_forms hM background resident cuts hcuts target mobile hfree
  have hdesired : (render background resident cuts).IsRotated
      ((background (successor (by omega) (cuts target)) :: rest) ++
        [resident target, background (cuts target)]) :=
    hold.trans (List.isRotated_append
      (l := [resident target, background (cuts target)])
      (l' := background (successor (by omega) (cuts target)) :: rest))
  have hreached : (render background resident cuts).IsRotated
      (pre ++ [resident target, background (cuts target)]) := by
    exact ⟨gap, by simpa only [LiteralState.rotateLeft_eq_rotate] using hform⟩
  have hndReached : ((pre ++ [resident target]) ++ [background (cuts target)]).Nodup := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hreached.nodup_iff.mp hnd
  have hfresh : background (cuts target) ∉ pre ++ [resident target] := by
    intro hmem
    exact (List.nodup_append.mp hndReached).2.2 _ hmem _ (by simp) rfl
  have hcompare : ((pre ++ [resident target]) ++ [background (cuts target)]).IsRotated
      (((background (successor (by omega) (cuts target)) :: rest) ++ [resident target]) ++
        [background (cuts target)]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hreached.symm.trans hdesired
  have heq := SourceUniverse.append_last_eq_of_isRotated hfresh hcompare
  rw [hform]
  have hfull : pre ++ [resident target, background (cuts target)] =
      ((background (successor (by omega) (cuts target)) :: rest) ++
        [resident target, background (cuts target)]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      congrArg (fun l => l ++ [background (cuts target)]) heq
  rw [hfull]
  rfl

/-- The proper full sweep after any positive endpoint stops strictly
before the last gap. The endpoint data are literal list data, and its
resident cut is the actual successor of the last crossed background. -/
theorem sweep_lt_last_gap (hM : 3 ≤ M) (background : Fin M → α)
    (hbackground : Function.Injective background) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : Function.Injective cuts)
    (hnd : (render background resident cuts).Nodup)
    (q : Fin k → ZMod M) (hrobust : Robust q)
    (translation : ZMod M) (phases : Fin k → Bool)
    (hrep : Represents q translation phases cuts)
    (previous target : Fin k) (crossed : Fin M)
    (hprevious : cuts previous = successor (by omega) crossed)
    (mobile : α) (gap moves : Nat)
    (hlast : ((render background resident cuts).rotateLeft gap).getLast? = some (background crossed))
    (hmoves : moves < (render background resident cuts).length)
    (pre : List α)
    (hsuffix : fullIterate moves
      ((render background resident cuts).rotateLeft gap ++ [mobile]) =
        pre ++ [resident target, background (cuts target), mobile]) :
    moves < (render background resident cuts).length - 1 := by
  have hfree : ∀ j, cuts j ≠ successor (by omega) (cuts target) :=
    represented_successor_free (by omega) q hrobust translation phases cuts hrep target
  have hform : (render background resident cuts).rotateLeft (gap + moves) =
      pre ++ [resident target, background (cuts target)] := by
    rw [fullIterate_formula, rotateLeft_add] at hsuffix
    exact List.append_cancel_right (by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hsuffix)
  have hhead := target_suffix_head (by omega) background resident cuts hcuts hnd target mobile
    hfree (gap + moves) pre hform
  by_contra hnot
  have hlastMove : moves = (render background resident cuts).length - 1 := by omega
  have hlength : ((render background resident cuts).rotateLeft gap).length =
      (render background resident cuts).length := by
    rw [LiteralState.rotateLeft_eq_rotate, List.length_rotate]
  have hheadLast : ((render background resident cuts).rotateLeft (gap + moves)).head? =
      some (background crossed) := by
    rw [← rotateLeft_add, LiteralState.rotateLeft_eq_rotate,
      List.head?_rotate (by omega : moves < ((render background resident cuts).rotateLeft gap).length)]
    rw [show moves = ((render background resident cuts).rotateLeft gap).length - 1 by omega,
      ← List.getLast?_eq_getElem?]
    exact hlast
  have hcrossed : crossed = successor (by omega) (cuts target) :=
    hbackground (Option.some.inj (hheadLast.symm.trans hhead))
  have heq : perturbed q translation phases previous = perturbed q translation phases target + 2 := by
    rw [← hrep previous, ← hrep target, hprevious, hcrossed, successor_cutValue, successor_cutValue]
    ring
  exact two_steps_unoccupied hM q hrobust translation phases previous target heq

end CoefficientTwoPrecision.StoppingBound

#print axioms CoefficientTwoPrecision.StoppingBound.target_suffix_head
#print axioms CoefficientTwoPrecision.StoppingBound.sweep_lt_last_gap
