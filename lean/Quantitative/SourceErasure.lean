import Quantitative.SourceComplement

/-!
# Membership in the insertion universe from literal control erasure

This bridge lets the source construction prove its old-letter projection
directly. No finite search for an insertion chain is required.
-/

namespace CoefficientTwoPrecision.SourceErasure

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open CoefficientTwoPrecision.SourceUniverse

def eraseControls : List Nat → List Nat → List Nat
  | [], word => word
  | control :: rest, word => eraseControls rest (eraseSatellite control word)

theorem cyclicEq_isRotated {a b : List Nat} (hab : CyclicEq a b) : a.IsRotated b := by
  obtain ⟨j, hj⟩ := hab
  refine ⟨j.val, ?_⟩
  change a.rotateLeft j.val = b at hj
  rwa [rotateLeft_eq_rotate] at hj

theorem insertionAbove_of_erasure (controls d word : List Nat)
    (hd : 0 < d.length) (hnd : (controls ++ d).Nodup)
    (hp : word.Perm (controls ++ d))
    (herase : CyclicEq d (eraseControls controls word)) :
    InsertionAbove controls d word := by
  induction controls generalizing word with
  | nil => exact cyclicEq_isRotated herase
  | cons v controls ih =>
    have hnd' : (v :: (controls ++ d)).Nodup := hnd
    have hv : v ∉ controls ++ d := (List.nodup_cons.mp hnd').1
    have hold : (controls ++ d).Nodup := (List.nodup_cons.mp hnd').2
    have hrotate : (v :: (controls ++ d)).Perm ((controls ++ d) ++ [v]) := by
      simpa only [List.singleton_append] using
        (List.perm_append_comm (l₁ := [v]) (l₂ := controls ++ d))
    have hp' : word.Perm ((controls ++ d) ++ [v]) := hp.trans hrotate
    have he : (eraseSatellite v word).Perm (controls ++ d) :=
      eraseSatellite_perm_of_perm_append_satellite hp' hv
    have hc : InsertionAbove controls d (eraseSatellite v word) :=
      ih (eraseSatellite v word) hold he herase
    have hword : word.Nodup := hp.nodup_iff.mpr hnd
    have hvmem : v ∈ word := hp.mem_iff.mpr (by simp)
    have hne : eraseSatellite v word ≠ [] := by
      apply List.length_pos_iff.mp
      rw [he.length_eq, List.length_append]
      omega
    have hb := inInsertionBlock_of_cyclicEq_eraseSatellite hword hvmem (CyclicEq.refl hne)
    obtain ⟨j, hj⟩ := hb
    refine ⟨eraseSatellite v word, hc, j.val, ?_⟩
    have hr := cyclicEq_isRotated hj
    change ((eraseSatellite v word).rotateLeft j.val ++ [v]).IsRotated word at hr
    rwa [rotateLeft_eq_rotate] at hr

end CoefficientTwoPrecision.SourceErasure

#print axioms CoefficientTwoPrecision.SourceErasure.insertionAbove_of_erasure
