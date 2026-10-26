import Quantitative.NormalCuts
import Quantitative.TranslatedRenderer

/-!
# Literal sweep lengths within a descending normal batch

The first target is the last physical cut and the initial head is at
physical cut zero. Every later target is immediately before the previous
target in physical order. The previous cut has already advanced once,
whereas the target has not. The exact offset theorem therefore determines
each actual proper sweep and yields the adjacent-cut cancellation formula.
-/

namespace CoefficientTwoPrecision.NormalSweepLocal

open LiteralState StationaryCircle RobustMatching BatchSafety
open PhasedControlOrder NormalCuts

variable {M k : Nat} {α : Type} [NeZero M] [DecidableEq α]

theorem first_sweep (hM : 2 ≤ M) (hk : 0 < k)
    (q : Fin k → Fin M) (hmono : StrictMono q)
    (hrobust : Robust (fun i => cutValue (q i)))
    (hzero : q ⟨0, hk⟩ = 0)
    (background : Fin M → α) (resident : Fin k → α) (translation : Fin M)
    (hnd : (render background resident (fun i => q i + translation)).Nodup)
    (hlen : (render background resident (fun i => q i + translation)).length = M + k)
    (mobile : α) (gap moves : Nat) (pre : List α)
    (hmoves : moves < M + k)
    (hhead : ((render background resident (fun i => q i + translation)).rotateLeft gap).head? =
      some (resident ⟨0, hk⟩))
    (hsuffix : fullIterate moves
      ((render background resident (fun i => q i + translation)).rotateLeft gap ++ [mobile]) =
        pre ++ [resident (⟨0, hk⟩ : Fin k).rev,
          background (q (⟨0, hk⟩ : Fin k).rev + translation), mobile]) :
    moves = (q (⟨0, hk⟩ : Fin k).rev).val + k + 1 := by
  have hlast := last_gap hM q hrobust ⟨0, hk⟩ hzero (⟨0, hk⟩ : Fin k).rev
  have hrev : (⟨0, hk⟩ : Fin k).rev.val = k - 1 := by simp [Fin.val_rev]
  have hfirst : (q ⟨0, hk⟩).val = 0 := by simp only [hzero, Fin.val_zero]
  have h := TranslatedRenderer.sweep_length background resident q hmono translation hnd
    ⟨0, hk⟩ (⟨0, hk⟩ : Fin k).rev mobile gap moves pre
    (by rw [hlen, hfirst]; simp only [Fin.val_mk]; omega)
    (by rw [hlen, hrev]; omega)
    (by rw [hlen]; exact hmoves) hhead hsuffix
  rw [hfirst] at h
  simp only [Fin.val_mk, Nat.zero_add, Nat.zero_le, ite_true, Nat.sub_zero] at h
  rw [hrev] at h
  omega

theorem later_sweep (hM : 2 ≤ M) (hk : 0 < k)
    (q : Fin k → Fin M) (hmono : StrictMono q)
    (hrobust : Robust (fun i => cutValue (q i)))
    (hzero : q ⟨0, hk⟩ = 0)
    (ell : Nat) (hell : ell < k) (hpos : 0 < ell)
    (background : Fin M → α) (resident : Fin k → α) (translation : Fin M)
    (hnd : (render background resident (fun i =>
      phased hM q hrobust ⟨0, hk⟩ hzero (normalPhase ell) i + translation)).Nodup)
    (hlen : (render background resident (fun i =>
      phased hM q hrobust ⟨0, hk⟩ hzero (normalPhase ell) i + translation)).length = M + k)
    (mobile : α) (gap moves : Nat) (pre : List α)
    (hmoves : moves < M + k)
    (hhead : ((render background resident (fun i =>
      phased hM q hrobust ⟨0, hk⟩ hzero (normalPhase ell) i + translation)).rotateLeft gap).head? =
        some (resident (⟨ell - 1, by omega⟩ : Fin k).rev))
    (hsuffix : fullIterate moves
      ((render background resident (fun i =>
        phased hM q hrobust ⟨0, hk⟩ hzero (normalPhase ell) i + translation)).rotateLeft gap ++ [mobile]) =
          pre ++ [resident (⟨ell, hell⟩ : Fin k).rev,
            background (phased hM q hrobust ⟨0, hk⟩ hzero (normalPhase ell)
              (⟨ell, hell⟩ : Fin k).rev + translation), mobile]) :
    moves + (q (⟨ell - 1, by omega⟩ : Fin k).rev).val =
      M + k + (q (⟨ell, hell⟩ : Fin k).rev).val := by
  let previous : Fin k := (⟨ell - 1, by omega⟩ : Fin k).rev
  let target : Fin k := (⟨ell, hell⟩ : Fin k).rev
  let current := phased hM q hrobust ⟨0, hk⟩ hzero (normalPhase ell)
  have hindex : previous.val = target.val + 1 := by
    dsimp only [previous, target]
    simp only [Fin.val_rev, Fin.val_mk]
    omega
  have horder : target < previous := by change target.val < previous.val; omega
  have hgap := increasing_gap q hmono hrobust target previous horder
  have hprev : (current previous).val = (q previous).val + 1 :=
    previous_phase_value hM q hrobust ⟨0, hk⟩ hzero ell hell hpos
  have htarg : (current target).val = (q target).val :=
    target_phase_value hM q hrobust ⟨0, hk⟩ hzero ell hell
  have hprevBound := last_gap hM q hrobust ⟨0, hk⟩ hzero previous
  have htargBound := last_gap hM q hrobust ⟨0, hk⟩ hzero target
  have hpidx := previous.isLt
  have htidx := target.isLt
  have h := TranslatedRenderer.sweep_length background resident current
    (phased_strictMono hM q hmono hrobust ⟨0, hk⟩ hzero (normalPhase ell)) translation hnd
    previous target mobile gap moves pre
    (by rw [hlen, hprev]; omega)
    (by rw [hlen, htarg]; omega)
    (by rw [hlen]; exact hmoves) hhead hsuffix
  rw [hprev, htarg, hlen, if_neg (by omega)] at h
  change moves + (q previous).val = M + k + (q target).val
  omega

end CoefficientTwoPrecision.NormalSweepLocal

#print axioms CoefficientTwoPrecision.NormalSweepLocal.first_sweep
#print axioms CoefficientTwoPrecision.NormalSweepLocal.later_sweep
