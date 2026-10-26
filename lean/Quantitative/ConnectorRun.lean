import Quantitative.ConnectorPrefixes
import Quantitative.PortReachability

/-!
# Selecting genuine exceptional occurrences from a literal full-row run

This file locates each selected phase in the actual repeated source list.
It uses the signed port orbit to choose the lap and then uses the literal
transported-prefix theorem. Its conclusion concerns the actual transported
row list; its hypotheses contain no safe-incidence certificate.
-/

namespace CoefficientTwoPrecision.ConnectorRun

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase
open SuperpermutationUpperBound43586371
open CoefficientTwoPrecision.SafeConnectors CoefficientTwoPrecision.ConnectorPrefixes
open CoefficientTwoPrecision.PortReachability

theorem rep_add (a b : Nat) (source : List (Row Nat)) :
    rep (a + b) source = rep a source ++ rep b source := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp [rep, Nat.succ_add, ih, List.append_assoc]

theorem sum_delta_rep (k : Nat) (source : List (Row Nat)) :
    ((rep k source).map delta).sum = (k : Int) * (source.map delta).sum := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    simp only [rep, List.map_append, List.sum_append, ih]
    push_cast
    ring

theorem source_decomposition (source : List (Row Nat)) (j : Nat) (hj : j < source.length) :
    source = source.take j ++ rowAt source j :: source.drop (j + 1) := by
  have he := List.take_append_drop j source
  rw [List.drop_eq_getElem_cons (l := source) hj] at he
  have hg : rowAt source j = source[j]'hj := by
    simp [rowAt, List.getElem?_eq_getElem (l := source) hj]
  rw [hg]
  exact he.symm

theorem rep_occurrence (source : List (Row Nat)) (ell k j : Nat)
    (hk : k < ell) (hj : j < source.length) :
    rep ell source = (rep k source ++ source.take j) ++ rowAt source j ::
      (source.drop (j + 1) ++ rep (ell - k - 1) source) := by
  have hsplit : ell = k + ((ell - k - 1) + 1) := by omega
  have hrep : rep ell source = (rep k source ++ source) ++ rep (ell - k - 1) source := by
    conv_lhs => rw [hsplit, rep_add, rep]
    rw [List.append_assoc]
  have hs := congrArg (fun tail => (rep k source ++ tail) ++ rep (ell - k - 1) source)
    (source_decomposition source j hj)
  exact hrep.trans (by simpa only [List.append_assoc, List.cons_append] using hs)

/-- A literal full run subtracts one displacement per actual source row. -/
theorem full_run_prefix_delta (source : List (Row Nat)) (start R : Nat)
    (H : List Nat) (mobile : Nat) (run : LiteralFRun source start R H mobile)
    (j : Nat) (hj : j ≤ R) :
    ((source.take (start + j)).map delta).sum =
      ((source.take start).map delta).sum - (j : Int) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjR : j < R := by omega
    have hjlen : start + j < source.length := by have := run.1; omega
    have hrow : rowAt source (start + j) = source[start + j]'hjlen := by
      simp [rowAt, List.getElem?_eq_getElem (l := source) hjlen]
    have hd : delta (source[start + j]'hjlen) = -1 := by
      rw [← hrow]
      exact delta_full (by simp [Row.charge, (run.2 j hjR).2])
    rw [show start + (j + 1) = (start + j) + 1 by omega,
      List.take_succ_eq_append_getElem hjlen, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, hd, ih (by omega)]
    push_cast
    ring

/-- A prefix displacement divisible by the gcd can be cancelled during one
minimal port orbit, with its cancellation witnessed at an actual lap. -/
theorem exists_zero_lap (h : Nat) (d s : Int) (e : Fin (h + 1))
    (hres : (Nat.gcd (h + 1) d.natAbs : Int) ∣ (e.val : Int) + s) :
    ∃ k < (h + 1) / Nat.gcd (h + 1) d.natAbs,
      shiftPort h ((k : Int) * d + s) e = ⟨0, by omega⟩ := by
  let p := shiftPort h s e
  have hg : (Nat.gcd (h + 1) d.natAbs : Int) ∣ ((h + 1 : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have hmod : Int.ModEq (Nat.gcd (h + 1) d.natAbs : Int)
      (p.val : Int) ((e.val : Int) + s) := by
    rw [show (p.val : Int) = ((e.val : Int) + s) % ((h + 1 : Nat) : Int) from
      shiftPort_val h s e]
    exact (Int.mod_modEq _ _).of_dvd hg
  have hp : (Nat.gcd (h + 1) d.natAbs : Int) ∣ (p.val : Int) :=
    Int.modEq_zero_iff_dvd.mp (hmod.trans (Int.modEq_zero_iff_dvd.mpr hres))
  have hpneg : (Nat.gcd (h + 1) d.natAbs : Int) ∣ (0 : Int) - p.val := by
    simpa only [zero_sub] using Int.dvd_neg.mpr hp
  obtain ⟨k, hk, he⟩ := exists_bounded_hit h d p ⟨0, by omega⟩ hpneg
  refine ⟨k, hk, ?_⟩
  rw [shiftPort_iterate] at he
  change shiftPort h ((k : Int) * d) (shiftPort h s e) = _ at he
  rw [shiftPort_add] at he
  simpa only [add_comm s] using he

/-- Each permitted run phase has a genuine port-zero occurrence in the
repeated traversal, found before its minimal port orbit ends. -/
theorem run_phase_occurrence (source : List (Row Nat)) (start R : Nat)
    (H : List Nat) (mobile h : Nat) (hH : H.length = h + 1)
    (run : LiteralFRun source start R H mobile)
    (hn : 3 ≤ h + 2)
    (hlen : ∀ r ∈ source, r.base.length = h + 2)
    (hkind : ∀ r ∈ source,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (e : Fin (h + 1)) (j : Nat) (hj : j < R)
    (hres : (Nat.gcd (h + 1) (source.map delta).sum.natAbs : Int) ∣
      (e.val : Int) + ((source.take start).map delta).sum - j) :
    ∃ pre post : List (Row Nat),
      rep ((h + 1) / Nat.gcd (h + 1) (source.map delta).sum.natAbs) source =
        pre ++ rowAt source (start + j) :: post ∧
      completionExit pre e.val = 0 := by
  let d := (source.map delta).sum
  let ell := (h + 1) / Nat.gcd (h + 1) d.natAbs
  let oldPre := source.take (start + j)
  have hdelta : (oldPre.map delta).sum = ((source.take start).map delta).sum - j :=
    full_run_prefix_delta source start R H mobile run j hj.le
  have hres' : (Nat.gcd (h + 1) d.natAbs : Int) ∣ (e.val : Int) + (oldPre.map delta).sum := by
    rw [hdelta]
    simpa only [sub_eq_add_neg, add_assoc] using hres
  obtain ⟨k, hk, hzero⟩ := exists_zero_lap h d (oldPre.map delta).sum e hres'
  have hjlen : start + j < source.length := by have := run.1; omega
  let pre := rep k source ++ oldPre
  let post := source.drop (start + j + 1) ++ rep (ell - k - 1) source
  refine ⟨pre, post, rep_occurrence source ell k (start + j) hk hjlen, ?_⟩
  have hmem : ∀ r ∈ pre, r ∈ source := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact mem_rep hr
    · exact List.mem_of_mem_take hr
  rw [completionExit_eq_shift pre h hn (fun r hr => hlen r (hmem r hr))
    (fun r hr => hkind r (hmem r hr)) e]
  have hsum : (pre.map delta).sum = (k : Int) * d + (oldPre.map delta).sum := by
    simp only [pre, List.map_append, List.sum_append, sum_delta_rep, d]
  rw [hsum, hzero]

/-- The arithmetic progression of run phases yields the actual source
occurrence table required by the transported-prefix theorem. -/
noncomputable def zeroPortSources_of_run
    (source : List (Row Nat)) (start R : Nat) (H : List Nat) (mobile h L a : Nat)
    (hH : H.length = h + 1) (run : LiteralFRun source start R H mobile)
    (hn : 3 ≤ h + 2)
    (hlen : ∀ r ∈ source, r.base.length = h + 2)
    (hkind : ∀ r ∈ source,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (e : Fin (h + 1))
    (ha : a < Nat.gcd (h + 1) (source.map delta).sum.natAbs)
    (hL : Nat.gcd (h + 1) (source.map delta).sum.natAbs * L ≤ R)
    (hphase : Int.ModEq (Nat.gcd (h + 1) (source.map delta).sum.natAbs : Int)
      ((e.val : Int) + ((source.take start).map delta).sum) a) :
    ZeroPortSources
      (rep ((h + 1) / Nat.gcd (h + 1) (source.map delta).sum.natAbs) source)
      (rot H a) mobile (Nat.gcd (h + 1) (source.map delta).sum.natAbs) L e.val := by
  let g := Nat.gcd (h + 1) (source.map delta).sum.natAbs
  let phase (u : Fin L) := a + g * u.val
  have hphase_lt (u : Fin L) : phase u < R := by
    have hm : g * (u.val + 1) ≤ g * L := Nat.mul_le_mul_left g (by have := u.isLt; omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    dsimp only [phase]
    change a < g at ha
    change g * L ≤ R at hL
    omega
  have hres (u : Fin L) : (g : Int) ∣
      (e.val : Int) + ((source.take start).map delta).sum - phase u := by
    have hd : (g : Int) ∣ (e.val : Int) + ((source.take start).map delta).sum - a := by
      have := Int.dvd_neg.mpr hphase.dvd
      simpa only [neg_sub] using this
    have hm : (g : Int) ∣ (g : Int) * u.val := ⟨u.val, rfl⟩
    have hs := Int.dvd_sub hd hm
    simpa only [phase, Int.natCast_add, Int.natCast_mul, sub_sub] using hs
  have hits : ∀ u : Fin L, ∃ pre post : List (Row Nat),
      rep ((h + 1) / g) source = pre ++ rowAt source (start + phase u) :: post ∧
      completionExit pre e.val = 0 := by
    intro u
    exact run_phase_occurrence source start R H mobile h hH run hn hlen hkind e
      (phase u) (hphase_lt u) (hres u)
  choose pre post hdecomp hzero using hits
  refine ⟨pre, (fun u => rowAt source (start + phase u)), post, hdecomp, ?_, ?_, hzero⟩
  · intro u
    rw [(run.2 (phase u) (hphase_lt u)).1, rot_add]
  · intro u
    exact (run.2 (phase u) (hphase_lt u)).2

/-- A full run produces the literal safe connector list for the actual
transported repeated traversal, for every tagged completion port. -/
theorem safe_run_component
    (source : List (Row Nat)) (start R : Nat) (H : List Nat) (mobile z f h L a : Nat)
    (hH : H.length = h + 1) (run : LiteralFRun source start R H mobile)
    (hn : 3 ≤ h + 2)
    (hlen : ∀ r ∈ source, r.base.length = h + 2)
    (hkind : ∀ r ∈ source,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (e : Fin (h + 1))
    (ha : a < Nat.gcd (h + 1) (source.map delta).sum.natAbs)
    (hLpos : 0 < L)
    (hL : Nat.gcd (h + 1) (source.map delta).sum.natAbs * L ≤ R)
    (hR : R ≤ h + 1)
    (hcover : h + 1 ≤ 2 * (Nat.gcd (h + 1) (source.map delta).sum.natAbs * L))
    (hphase : Int.ModEq (Nat.gcd (h + 1) (source.map delta).sum.natAbs : Int)
      ((e.val : Int) + ((source.take start).map delta).sum) a) :
    SafeComp
      (transportWalk (rep ((h + 1) / Nat.gcd (h + 1) (source.map delta).sum.natAbs) source) z e.val)
      f (h + 2)
      (connectorCircles (rot H a) f (Nat.gcd (h + 1) (source.map delta).sum.natAbs) L) := by
  let src := rep ((h + 1) / Nat.gcd (h + 1) (source.map delta).sum.natAbs) source
  have hlen' : ∀ r ∈ src, r.base.length = h + 2 := fun r hr => hlen r (mem_rep hr)
  have hkind' : ∀ r ∈ src,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2 :=
    fun r hr => hkind r (mem_rep hr)
  have hH' : (rot H a).length = h + 1 := by simpa using hH
  let zeroOcc := zeroPortSources_of_run source start R H mobile h L a hH run hn hlen hkind
    e ha hL hphase
  let occ := selectedOccurrences src (rot H a) mobile z
    (Nat.gcd (h + 1) (source.map delta).sum.natAbs) L e.val
    (by omega) (by have := e.isLt; omega)
    (fun r hr => by rw [hH']; simpa only [Nat.add_assoc] using hlen' r hr)
    hkind' zeroOcc
  have hmeta := transportWalk_metadata src z (h + 1) e.val (by omega)
    (fun r hr => by simpa only [Nat.add_assoc] using hlen' r hr) hkind'
  have hs := safe_of_selected_occurrences (transportWalk src z e.val) (rot H a) f
    (Nat.gcd (h + 1) (source.map delta).sum.natAbs) L ((rot H a).length - e.val)
    (by omega) hLpos (by omega) (by omega) (by omega) occ
    (fun r hr => by rw [hH']; simpa only [Nat.add_assoc] using (hmeta r hr).1)
    (fun r hr => (hmeta r hr).2)
  simpa only [hH', Nat.add_assoc] using hs

end CoefficientTwoPrecision.ConnectorRun

#print axioms CoefficientTwoPrecision.ConnectorRun.run_phase_occurrence
#print axioms CoefficientTwoPrecision.ConnectorRun.safe_run_component
