import Quantitative.ConnectorRun

/-!
# The actual component and connector lists for one source contour

Canonical initial ports are the integers below the gcd. A component is the
literal transport of the source repeated for one minimal port orbit. Its
connector phase is the required residue of its actual source prefix.
The circle count is exactly twice the square of the gcd, with repeated
circle values retained as separate occurrences.
-/

namespace CoefficientTwoPrecision.SourceAdvancement

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371
open CoefficientTwoPrecision.SafeConnectors CoefficientTwoPrecision.ConnectorRun

def portGcd (source : List (Row Nat)) (h : Nat) : Nat :=
  Nat.gcd (h + 1) (source.map delta).sum.natAbs

def orbitLaps (source : List (Row Nat)) (h : Nat) : Nat :=
  (h + 1) / portGcd source h

def connectorPhase (source : List (Row Nat)) (start h e : Nat) : Nat :=
  (((e : Int) + ((source.take start).map delta).sum) % (portGcd source h : Int)).toNat

theorem portGcd_pos (source : List (Row Nat)) (h : Nat) : 0 < portGcd source h :=
  Nat.gcd_pos_of_pos_left _ (Nat.succ_pos h)

theorem portGcd_le (source : List (Row Nat)) (h : Nat) : portGcd source h ≤ h + 1 :=
  Nat.le_of_dvd (Nat.succ_pos h) (Nat.gcd_dvd_left _ _)

theorem connectorPhase_lt (source : List (Row Nat)) (start h e : Nat) :
    connectorPhase source start h e < portGcd source h := by
  have hg : (0 : Int) < portGcd source h := by exact_mod_cast portGcd_pos source h
  apply (Int.toNat_lt (Int.emod_nonneg _ (by omega))).mpr
  exact Int.emod_lt_of_pos _ hg

theorem connectorPhase_modEq (source : List (Row Nat)) (start h e : Nat) :
    Int.ModEq (portGcd source h : Int)
      ((e : Int) + ((source.take start).map delta).sum)
      (connectorPhase source start h e) := by
  have hg : (portGcd source h : Int) ≠ 0 := by have := portGcd_pos source h; omega
  have hcast : ((connectorPhase source start h e : Nat) : Int) =
      ((e : Int) + ((source.take start).map delta).sum) % (portGcd source h : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hg)
  rw [hcast]
  exact (Int.mod_modEq _ _).symm

/-- One literal advanced component for each canonical initial source port. -/
def advancedComponents (source : List (Row Nat)) (z h : Nat) : List (List (Row Nat)) :=
  (List.range (portGcd source h)).map
    (fun e => transportWalk (rep (orbitLaps source h) source) z e)

/-- The actual circle list, concatenated separately for every component. -/
def advancedCircles (source : List (Row Nat)) (H : List Nat) (start f h L : Nat) :
    List (List Nat) :=
  (List.range (portGcd source h)).flatMap (fun e =>
    connectorCircles (rot H (connectorPhase source start h e)) f (portGcd source h) L)

@[simp] theorem advancedComponents_length (source : List (Row Nat)) (z h : Nat) :
    (advancedComponents source z h).length = portGcd source h := by
  simp [advancedComponents]

theorem advancedCircles_length (source : List (Row Nat)) (H : List Nat)
    (start f h L : Nat) :
    (advancedCircles source H start f h L).length = 2 * (portGcd source h) ^ 2 := by
  simp [advancedCircles, List.length_flatMap, pow_two,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem advancedCircles_valid (source : List (Row Nat)) (H : List Nat)
    (start f h L : Nat) (hH : H.length = h + 1) (hnd : H.Nodup) (hf : f ∉ H) :
    CircleFamilyValid (h + 2) (advancedCircles source H start f h L) := by
  intro C hC
  obtain ⟨e, he, hC⟩ := List.mem_flatMap.mp hC
  have hrot := rot_perm H (connectorPhase source start h e)
  have hc := connectorCircles_valid (rot H (connectorPhase source start h e)) f
    (portGcd source h) L (hrot.nodup_iff.mpr hnd)
    (fun hm => hf (hrot.mem_iff.mp hm)) C hC
  simpa only [rot_length, hH, Nat.add_assoc] using hc

theorem advancedCircles_support (source : List (Row Nat)) (H : List Nat)
    (start f h L : Nat) :
    ∀ C ∈ advancedCircles source H start f h L, ∀ a ∈ C, a ∈ f :: H := by
  intro C hC a ha
  obtain ⟨e, he, hC⟩ := List.mem_flatMap.mp hC
  have hm := connectorCircles_support hC ha
  rcases List.mem_cons.mp hm with hm | hm
  · exact List.mem_cons.mpr (Or.inl hm)
  · exact List.mem_cons.mpr (Or.inr ((rot_perm H _).mem_iff.mp hm))

/-- Every tagged completion port of every actual component has a literal
connector witness. The only geometric hypothesis is the full source run. -/
theorem advanced_safe (source : List (Row Nat)) (start R : Nat) (H : List Nat)
    (mobile z f h L : Nat) (hH : H.length = h + 1)
    (run : LiteralFRun source start R H mobile) (hn : 3 ≤ h + 2)
    (hlen : ∀ r ∈ source, r.base.length = h + 2)
    (hkind : ∀ r ∈ source,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hLpos : 0 < L) (hL : portGcd source h * L ≤ R) (hR : R ≤ h + 1)
    (hcover : h + 1 ≤ 2 * (portGcd source h * L)) :
    ∀ W ∈ advancedComponents source z h,
      SafeComp W f (h + 2) (advancedCircles source H start f h L) := by
  intro W hW
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hW
  have he' : e < h + 1 := lt_of_lt_of_le (List.mem_range.mp he) (portGcd_le source h)
  have hs := safe_run_component source start R H mobile z f h L
    (connectorPhase source start h e) hH run hn hlen hkind ⟨e, he'⟩
    (connectorPhase_lt source start h e) hLpos hL hR hcover
    (connectorPhase_modEq source start h e)
  apply hs.mono
  intro C hC
  exact List.mem_flatMap.mpr ⟨e, he, hC⟩

end CoefficientTwoPrecision.SourceAdvancement

#print axioms CoefficientTwoPrecision.SourceAdvancement.advancedCircles_length
#print axioms CoefficientTwoPrecision.SourceAdvancement.advanced_safe
