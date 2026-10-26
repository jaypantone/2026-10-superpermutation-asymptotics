import Quantitative.SafeConnectors
import Mathlib.Tactic.LinearCombination

/-!
# Actual transported prefixes at exceptional full-row occurrences

The winding ledger determines the completion port before the second row
of every full transport path entered at source port zero. This file derives
that identity from actual lists, rather than assuming a prefix-port table.
The remaining orbit obligation is to locate the selected zero-port source
occurrences. Those locations are explicit hypotheses below.
-/

namespace CoefficientTwoPrecision.ConnectorPrefixes

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase
open SuperpermutationUpperBound43586371
open CoefficientTwoPrecision.SafeConnectors

theorem transportWalk_metadata (source : List (Row Nat)) (z h p : Nat)
    (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ source, r.base.length = h + 1)
    (hkind : ∀ r ∈ source,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ∀ r ∈ transportWalk source z p,
      r.base.length = h + 2 ∧
      (r.visible = r.base.length ∨ r.visible = r.base.length - 2) := by
  induction source generalizing p with
  | nil => simp [transportWalk]
  | cons r rest ih =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have hr := hlen r (by simp)
      have hm := transportPath_metadata r z p (by omega) (hkind r (by simp)) t ht
      simpa only [hr, Nat.add_assoc] using hm
    · exact ih _ (fun r hr => hlen r (by simp [hr]))
        (fun r hr => hkind r (by simp [hr])) t ht

theorem shiftPort_val_of_modEq (h shift : Nat) (d : Int) (J : Fin (h + 1))
    (hd : Int.ModEq (h + 1 : Nat) d shift) :
    (shiftPort h d J).val = (J.val + shift) % (h + 1) := by
  apply Int.ofNat_inj.mp
  rw [shiftPort_val, Int.natCast_emod, Int.natCast_add]
  exact hd.add_left J.val

/-- The exact old-to-new winding equation fixes the transported prefix
displacement whenever the actual old prefix ends at port zero. -/
theorem zero_port_displacement (pre : List (Row Nat)) (z h e : Nat)
    (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ pre, r.base.length = h + 1)
    (hkind : ∀ r ∈ pre,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (he : e < h) (hz : completionExit pre e = 0) :
    Int.ModEq (h + 1 : Nat)
      (((transportWalk pre z e).map delta).sum - 1) (h - e : Nat) := by
  have hledger := transportWalk_winding_ledger pre z h hn hlen hkind e he
  rw [hz] at hledger
  have hsub : ((h - e : Nat) : Int) = (h : Int) - e := by omega
  apply Int.modEq_iff_dvd.mpr
  refine ⟨1 - ((transportWalk pre z e).map delta).sum + (pre.map delta).sum, ?_⟩
  push_cast at hledger ⊢
  rw [hsub]
  linear_combination hledger

/-- The true completion port immediately before the second exceptional
full row is independent of the chosen source occurrence. -/
theorem exceptional_prefix_port (pre : List (Row Nat)) (r : Row Nat) (z h e : Nat)
    (hn : 3 ≤ h + 1)
    (hlen : ∀ t ∈ pre, t.base.length = h + 1)
    (hkind : ∀ t ∈ pre,
      t.visible = t.base.length ∨ t.visible = t.base.length - 2)
    (hr : r.base.length = h + 1) (he : e < h)
    (hz : completionExit pre e = 0) (J : Fin (h + 1)) :
    completionExit (transportWalk pre z e ++ [fullAt r z 0]) J.val =
      (J.val + (h - e)) % (h + 1) := by
  have hmeta := transportWalk_metadata pre z h e hn hlen hkind
  have hlen' : ∀ t ∈ transportWalk pre z e ++ [fullAt r z 0],
      t.base.length = h + 2 := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (hmeta t ht).1
    · have ht' : t = fullAt r z 0 := List.mem_singleton.mp ht
      subst t
      simp [fullAt, hr, Nat.add_assoc]
  have hkind' : ∀ t ∈ transportWalk pre z e ++ [fullAt r z 0],
      t.visible = t.base.length ∨ t.visible = t.base.length - 2 := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (hmeta t ht).2
    · have ht' : t = fullAt r z 0 := List.mem_singleton.mp ht
      subst t
      exact Or.inl (by simp [fullAt])
  rw [completionExit_eq_shift _ h (by omega) hlen' hkind' J]
  apply shiftPort_val_of_modEq
  simpa only [List.map_append, List.map_singleton, List.sum_append,
    List.sum_singleton, fullAt_delta, sub_eq_add_neg] using
    zero_port_displacement pre z h e hn hlen hkind he hz

theorem fullAt_last_head (r : Row Nat) (H : List Nat) (mobile z : Nat)
    (hbase : r.base = H ++ [mobile]) :
    (fullAt r z H.length).head = H := by
  simp [fullAt, Row.head, hbase, insertLetter]

/-- Decomposing the source at a genuine port-zero full row exhibits both
exceptional advanced row occurrences in their actual order. -/
theorem exceptional_decomposition (pre post : List (Row Nat)) (r : Row Nat)
    (z e : Nat) (hf : r.visible = r.base.length)
    (hz : completionExit pre e = 0) :
    transportWalk (pre ++ r :: post) z e =
      (transportWalk pre z e ++ [fullAt r z 0]) ++
        fullAt r z (r.base.length - 1) ::
          transportWalk post z (portTarget r 0) := by
  rw [transportWalk_append, hz, transportWalk]
  simp [portPath, hf, fullPathAt, List.append_assoc]

/-- An actual row after a specified prefix is the row at its prefix length. -/
theorem rowAt_prefix (pre post : List (Row Nat)) (r : Row Nat) :
    rowAt (pre ++ r :: post) pre.length = r := by
  simp [rowAt]

/-- Source occurrences selected within the actual traversal list. The
index choice, typically in repeated laps of one closed contour, remains
explicit. No advanced-prefix identity or safe incidence is assumed. -/
structure ZeroPortSources (source : List (Row Nat))
    (H : List Nat) (mobile g L e : Nat) where
  pre : Fin L → List (Row Nat)
  entry : Fin L → Row Nat
  post : Fin L → List (Row Nat)
  decomp : ∀ u, source = pre u ++ entry u :: post u
  base : ∀ u, (entry u).base = rot H (g * u.val) ++ [mobile]
  full : ∀ u, (entry u).visible = (entry u).base.length
  zeroPort : ∀ u, completionExit (pre u) e = 0

/-- The advanced occurrence table is derived from actual source positions,
their port-zero property, and the transported-prefix ledger. -/
def selectedOccurrences (source : List (Row Nat)) (H : List Nat)
    (mobile z g L e : Nat) (hn : 3 ≤ H.length + 1) (he : e < H.length)
    (hlen : ∀ r ∈ source, r.base.length = H.length + 1)
    (hkind : ∀ r ∈ source,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (occ : ZeroPortSources source H mobile g L e) :
    SelectedOccurrences (transportWalk source z e) H g L (H.length - e) where
  row u := (transportWalk (occ.pre u) z e ++ [fullAt (occ.entry u) z 0]).length
  row_lt u := by
    have hwalk := congrArg (fun src => transportWalk src z e) (occ.decomp u)
    rw [hwalk, exceptional_decomposition _ _ _ _ _ (occ.full u) (occ.zeroPort u)]
    simp only [List.length_append, List.length_cons]
    omega
  head u := by
    have hwalk := congrArg (fun src => transportWalk src z e) (occ.decomp u)
    rw [hwalk, exceptional_decomposition _ _ _ _ _ (occ.full u) (occ.zeroPort u),
      rowAt_prefix]
    have hb : (occ.entry u).base.length - 1 = H.length := by simp [occ.base u]
    rw [hb]
    simpa only [rot_length] using
      fullAt_last_head (occ.entry u) (rot H (g * u.val)) mobile z (occ.base u)
  prefixShift u J := by
    have hwalk := congrArg (fun src => transportWalk src z e) (occ.decomp u)
    rw [hwalk, exceptional_decomposition _ _ _ _ _ (occ.full u) (occ.zeroPort u),
      List.take_left]
    have hpre : ∀ r ∈ occ.pre u, r ∈ source := by
      intro r hr
      exact (occ.decomp u).symm ▸ List.mem_append_left (occ.entry u :: occ.post u) hr
    exact exceptional_prefix_port (occ.pre u) (occ.entry u) z H.length e hn
      (fun r hr => hlen r (hpre r hr)) (fun r hr => hkind r (hpre r hr))
      (by simp [occ.base u]) he (occ.zeroPort u) J

end CoefficientTwoPrecision.ConnectorPrefixes

#print axioms CoefficientTwoPrecision.ConnectorPrefixes.exceptional_prefix_port
#print axioms CoefficientTwoPrecision.ConnectorPrefixes.selectedOccurrences
