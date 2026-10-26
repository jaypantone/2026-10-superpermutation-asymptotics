import SuperpermutationUpperBound43586371.Stage
import Quantitative.SourceUniverse

/-!
# Actual empty extensions and insertion of certified pending families

These constructors use the original `Stage` and `Level` predicates. They
prove every field of the resulting stage. The certificate below contains
actual row/circle/pending lists and their structural proofs, not an assumed
existence of a new stage or an assumed superpermutation theorem.

The arbitrary-width constructor will iterate `empty_step`, then replace
the resulting insertion universe by the transported selected source family
and its complement. The local lemmas are also useful for final one-letter
padding, where no new source family is selected.
-/

namespace CoefficientTwoPrecision.StageExtension

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371
open CoefficientTwoPrecision.SourceUniverse

/-- Canonical representatives of all insertion classes occurring in a block. -/
theorem insertion_representative {d x : List Nat} {v : Nat}
    (h : InInsertionBlock v d x) :
    ∃ t ∈ insertions v d, CyclicEq t x := by
  obtain ⟨i, hi⟩ := h
  have hr : rot d i.val = d.rotate i.val := rotateLeft_eq_rotate d i.val
  refine ⟨d.rotate i.val ++ [v], mem_insertions.mpr ⟨i.val, i.isLt, rfl⟩, ?_⟩
  rwa [hr] at hi

/-- The actual pending representatives after one empty extension. -/
def emptyPending (z : Nat) (pending : List (List Nat)) : List (List Nat) :=
  pending.flatMap (insertions z)

/-- Adjoin one fresh ordinary letter without selecting any new source class. -/
theorem empty_step {A0 : List Nat} {z : Nat} {comps : List (List (Row Nat))}
    {circles pending : List (List Nat)} {R Q c P : Nat}
    (S : Stage A0 z comps circles pending R Q c P)
    (a : Nat) (ha : a ∉ z :: A0) (ha9 : a ≠ 9) (ha10 : a ≠ 10) :
    Stage (z :: A0) a (transportComps comps a A0.length)
      (extendCircles circles a) (emptyPending z pending)
      ((A0.length + 1) * R) ((A0.length + 1) * Q)
      (A0.length * c) (A0.length * P) := by
  have hn : 3 ≤ A0.length + 1 := by have := S.two; omega
  have counts := S.level.transport_counts a rfl hn ha ha9
  refine ⟨by simp only [List.length_cons]; have := S.two; omega,
    List.nodup_cons.mpr ⟨ha, S.nodup⟩, ?_, ?_,
    S.level.transport a rfl hn ha ha9,
    extend_valid S.valid S.support (not_mem_ten ha10 ha),
    extend_mem10 S.support,
    S.level.safe_transport rfl hn S.ten S.valid S.safe a,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h9
    rcases List.mem_cons.mp h9 with h9 | h9
    · exact ha9 h9.symm
    · exact S.nine h9
  · intro h10
    rcases List.mem_cons.mp h10 with h10 | h10
    · exact ha10 h10.symm
    · exact S.ten h10
  · intro t ht
    obtain ⟨e, he, ht⟩ := List.mem_flatMap.mp ht
    exact (insertion_perm ht).trans ((S.pend e he).cons z)
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := peel S.nodup (by simp) ha hy
    rcases S.cover x hx with ⟨r, hr, hrx⟩ | ⟨e, he, hex⟩
    · left
      exact S.level.cover_transport a rfl hn hr hrx hxy
    · right
      obtain ⟨t, ht, htx⟩ := insertion_representative hex
      exact ⟨t, List.mem_flatMap.mpr ⟨e, he, ht⟩,
        (InInsertionBlock.congr_base htx).mpr hxy⟩
  · rw [counts.1, S.rows]
  · rw [counts.2, S.charge]
  · rw [extend_length S.valid, S.ncirc]
  · unfold emptyPending
    rw [length_flatMap_const pending _ A0.length
      (fun e he => by rw [insertions_length, (S.pend e he).length_eq]), S.npend]
    exact Nat.mul_comm _ _

/-- Transport through a list of ordinary letters stored newest first. -/
def transportSequence (comps : List (List (Row Nat))) (h : Nat) :
    List Nat → List (List (Row Nat))
  | [] => comps
  | a :: rest => transportComps (transportSequence comps h rest) a (h + rest.length)

/-- Extend the actual circle list through the same sequence. -/
def circleSequence (circles : List (List Nat)) : List Nat → List (List Nat)
  | [] => circles
  | a :: rest => extendCircles (circleSequence circles rest) a

/-- All canonical insertion representatives above all old pending occurrences. -/
def pendingUniverse (controls : List Nat) (pending : List (List Nat)) : List (List Nat) :=
  pending.flatMap (sourceUniverse controls)

/-- An arbitrary finite sequence of empty extensions, including all stage fields. -/
theorem empty_many {A0 : List Nat} {z : Nat} {comps : List (List (Row Nat))}
    {circles pending : List (List Nat)} {R Q c P : Nat}
    (S : Stage A0 z comps circles pending R Q c P)
    (extra : List Nat) (next : Nat)
    (hnd : (next :: (extra ++ z :: A0)).Nodup)
    (h9 : 9 ∉ next :: (extra ++ z :: A0))
    (h10 : 10 ∉ next :: (extra ++ z :: A0)) :
    Stage (extra ++ z :: A0) next
      (transportSequence comps A0.length (next :: extra))
      (circleSequence circles (next :: extra))
      (pendingUniverse (extra ++ [z]) pending)
      (risingCount (A0.length + 1) (extra.length + 1) * R)
      (risingCount (A0.length + 1) (extra.length + 1) * Q)
      (risingCount A0.length (extra.length + 1) * c)
      (risingCount A0.length (extra.length + 1) * P) := by
  induction extra generalizing next with
  | nil =>
    have hn := List.nodup_cons.mp hnd
    have hn9 : next ≠ 9 := by
      intro he; subst next; exact h9 List.mem_cons_self
    have hn10 : next ≠ 10 := by
      intro he; subst next; exact h10 List.mem_cons_self
    have E := empty_step S next hn.1 hn9 hn10
    simpa [transportSequence, circleSequence, pendingUniverse, sourceUniverse,
      emptyPending, risingCount] using E
  | cons a extra ih =>
    have hn := List.nodup_cons.mp hnd
    have hi9 : 9 ∉ a :: (extra ++ z :: A0) :=
      fun hm => h9 (List.mem_cons_of_mem next hm)
    have hi10 : 10 ∉ a :: (extra ++ z :: A0) :=
      fun hm => h10 (List.mem_cons_of_mem next hm)
    have I := ih a hn.2 hi9 hi10
    have hn9 : next ≠ 9 := by
      intro he; subst next; exact h9 List.mem_cons_self
    have hn10 : next ≠ 10 := by
      intro he; subst next; exact h10 List.mem_cons_self
    have E := empty_step I next hn.1 hn9 hn10
    simpa [transportSequence, circleSequence, pendingUniverse, sourceUniverse,
      emptyPending, List.flatMap_assoc, risingCount, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using E

/-- A literal replacement of pending insertion blocks, with exact counts.
The existing stage's ordinary alphabet and distinguished letter are fixed. -/
structure PendingReplacement (A0 : List Nat) (z : Nat)
    (pending : List (List Nat)) where
  comps : List (List (Row Nat))
  circles : List (List Nat)
  remaining : List (List Nat)
  rowsCount : Nat
  chargeCount : Nat
  circleCount : Nat
  pendingCount : Nat
  level : Level (z :: A0) A0.length comps
  valid : CircleFamilyValid A0.length circles
  support : ∀ cc ∈ circles, ∀ a ∈ cc, a ∈ 10 :: z :: A0
  safe : ∀ rs ∈ comps, SafeComp rs 10 A0.length circles
  pend : ∀ e ∈ remaining, e.Perm A0
  cover : ∀ e ∈ pending, ∀ y, InInsertionBlock z e y →
    (∃ r ∈ comps.flatten, CyclicEq r.base y) ∨
      (∃ t ∈ remaining, InInsertionBlock z t y)
  rows : comps.flatten.length = rowsCount
  charge : (comps.flatten.map Row.charge).sum = chargeCount
  ncirc : circles.length = circleCount
  npend : remaining.length = pendingCount

/-- Add the certified rows and circles, and replace the pending list.
Every structural and counting field is proved here. -/
theorem replace_pending {A0 : List Nat} {z : Nat}
    {comps : List (List (Row Nat))} {circles pending : List (List Nat)}
    {R Q c P : Nat} (S : Stage A0 z comps circles pending R Q c P)
    (K : PendingReplacement A0 z pending) :
    Stage A0 z (comps ++ K.comps) (circles ++ K.circles) K.remaining
      (R + K.rowsCount) (Q + K.chargeCount) (c + K.circleCount) K.pendingCount := by
  refine ⟨S.two, S.nodup, S.nine, S.ten, S.level.append K.level,
    ?_, ?_, ?_, K.pend, ?_, ?_, ?_, ?_, K.npend⟩
  · intro cc hc
    rcases List.mem_append.mp hc with hc | hc
    · exact S.valid cc hc
    · exact K.valid cc hc
  · intro cc hc a ha
    rcases List.mem_append.mp hc with hc | hc
    · exact S.support cc hc a ha
    · exact K.support cc hc a ha
  · intro rs hrs
    rcases List.mem_append.mp hrs with hrs | hrs
    · exact (S.safe rs hrs).mono (fun cc hc => List.mem_append_left _ hc)
    · exact (K.safe rs hrs).mono (fun cc hc => List.mem_append_right _ hc)
  · intro y hy
    rcases S.cover y hy with ⟨r, hr, hry⟩ | ⟨e, he, hey⟩
    · left
      refine ⟨r, ?_, hry⟩
      rw [List.flatten_append]
      exact List.mem_append_left _ hr
    · rcases K.cover e he y hey with ⟨r, hr, hry⟩ | ht
      · left
        refine ⟨r, ?_, hry⟩
        rw [List.flatten_append]
        exact List.mem_append_right _ hr
      · exact Or.inr ht
  · rw [List.flatten_append, List.length_append, S.rows, K.rows]
  · rw [List.flatten_append, List.map_append, List.sum_append, S.charge, K.charge]
  · rw [List.length_append, S.ncirc, K.ncirc]

/-- The actual transported block objects above an old cyclic class. All
hypotheses are structural statements about the displayed lists. The record
has no field asserting the desired Stage or covering-word theorem. -/
structure WidthBlockFamily (A0 controls : List Nat) (next : Nat) where
  comps : List Nat → List (List (Row Nat))
  circles : List Nat → List (List Nat)
  remaining : List Nat → List (List Nat)
  sourceRows : Nat
  sourceCharge : Nat
  advancedCircles : Nat
  sourceBound : sourceRows ≤ risingCount A0.length controls.length
  level : ∀ d, d.Perm A0 →
    Level (next :: (controls ++ A0)) (controls ++ A0).length (comps d)
  valid : ∀ d, d.Perm A0 → CircleFamilyValid (controls ++ A0).length (circles d)
  support : ∀ d, d.Perm A0 → ∀ cc ∈ circles d, ∀ a ∈ cc,
    a ∈ 10 :: next :: (controls ++ A0)
  safe : ∀ d, d.Perm A0 → ∀ rs ∈ comps d,
    SafeComp rs 10 (controls ++ A0).length (circles d)
  pend : ∀ d, d.Perm A0 → ∀ e ∈ remaining d, e.Perm (controls ++ A0)
  cover : ∀ d, d.Perm A0 → ∀ t ∈ sourceUniverse controls d,
    ∀ y, InInsertionBlock next t y →
      (∃ r ∈ (comps d).flatten, CyclicEq r.base y) ∨
        (∃ e ∈ remaining d, InInsertionBlock next e y)
  rows : ∀ d, d.Perm A0 → (comps d).flatten.length =
    (controls ++ A0).length * sourceRows
  charge : ∀ d, d.Perm A0 → ((comps d).flatten.map Row.charge).sum =
    (controls ++ A0).length * sourceCharge
  ncirc : ∀ d, d.Perm A0 → (circles d).length = advancedCircles
  npend : ∀ d, d.Perm A0 → (remaining d).length =
    risingCount A0.length controls.length - sourceRows

/-- Combine actual block certificates over the original pending occurrences. -/
def collect_blocks {A0 controls : List Nat} {next : Nat}
    (K : WidthBlockFamily A0 controls next) (pending : List (List Nat))
    (hp : ∀ d ∈ pending, d.Perm A0) (P : Nat) (hlen : pending.length = P) :
    PendingReplacement (controls ++ A0) next (pendingUniverse controls pending) where
  comps := pending.flatMap K.comps
  circles := pending.flatMap K.circles
  remaining := pending.flatMap K.remaining
  rowsCount := P * ((controls ++ A0).length * K.sourceRows)
  chargeCount := P * ((controls ++ A0).length * K.sourceCharge)
  circleCount := P * K.advancedCircles
  pendingCount := P * (risingCount A0.length controls.length - K.sourceRows)
  level := Level.flatMap pending _ (fun d hd => K.level d (hp d hd))
  valid := by
    intro cc hc
    obtain ⟨d, hd, hc⟩ := List.mem_flatMap.mp hc
    exact K.valid d (hp d hd) cc hc
  support := by
    intro cc hc a ha
    obtain ⟨d, hd, hc⟩ := List.mem_flatMap.mp hc
    exact K.support d (hp d hd) cc hc a ha
  safe := by
    intro rs hrs
    obtain ⟨d, hd, hrs⟩ := List.mem_flatMap.mp hrs
    exact (K.safe d (hp d hd) rs hrs).mono
      (fun cc hc => List.mem_flatMap.mpr ⟨d, hd, hc⟩)
  pend := by
    intro e he
    obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp he
    exact K.pend d (hp d hd) e he
  cover := by
    intro t ht y hty
    obtain ⟨d, hd, ht⟩ := List.mem_flatMap.mp ht
    rcases K.cover d (hp d hd) t ht y hty with ⟨r, hr, hry⟩ | ⟨e, he, hey⟩
    · left
      obtain ⟨rs, hrs, hr⟩ := List.mem_flatten.mp hr
      exact ⟨r, List.mem_flatten.mpr ⟨rs, List.mem_flatMap.mpr ⟨d, hd, hrs⟩, hr⟩, hry⟩
    · exact Or.inr ⟨e, List.mem_flatMap.mpr ⟨d, hd, he⟩, hey⟩
  rows := by
    rw [flatten_flatMap, length_flatMap_const pending _
      ((controls ++ A0).length * K.sourceRows) (fun d hd => K.rows d (hp d hd)), hlen]
  charge := by
    rw [flatten_flatMap, List.map_flatMap, sum_flatMap_const pending _
      ((controls ++ A0).length * K.sourceCharge) (fun d hd => K.charge d (hp d hd)), hlen]
  ncirc := by
    rw [length_flatMap_const pending _ K.advancedCircles
      (fun d hd => K.ncirc d (hp d hd)), hlen]
  npend := by
    rw [length_flatMap_const pending _ (risingCount A0.length controls.length - K.sourceRows)
      (fun d hd => K.npend d (hp d hd)), hlen]

/-- The arbitrary-width extension, proved from actual transported block
certificates. `extra` is newest first; the current distinguished letter is
also a source control. The width is `extra.length + 1`. -/
theorem advance_width {A0 : List Nat} {z : Nat} {comps : List (List (Row Nat))}
    {circles pending : List (List Nat)} {R Q c P : Nat}
    (S : Stage A0 z comps circles pending R Q c P)
    (extra : List Nat) (next : Nat)
    (hnd : (next :: (extra ++ z :: A0)).Nodup)
    (h9 : 9 ∉ next :: (extra ++ z :: A0))
    (h10 : 10 ∉ next :: (extra ++ z :: A0))
    (K : WidthBlockFamily A0 (extra ++ [z]) next) :
    Stage (extra ++ z :: A0) next
      (transportSequence comps A0.length (next :: extra) ++ pending.flatMap K.comps)
      (circleSequence circles (next :: extra) ++ pending.flatMap K.circles)
      (pending.flatMap K.remaining)
      (risingCount (A0.length + 1) (extra.length + 1) * R +
        (A0.length + extra.length + 1) * P * K.sourceRows)
      (risingCount (A0.length + 1) (extra.length + 1) * Q +
        (A0.length + extra.length + 1) * P * K.sourceCharge)
      (risingCount A0.length (extra.length + 1) * c + P * K.advancedCircles)
      (P * (risingCount A0.length (extra.length + 1) - K.sourceRows)) := by
  have E := empty_many S extra next hnd h9 h10
  let Kall := collect_blocks K pending S.pend P S.npend
  have hOld : extra ++ z :: A0 = (extra ++ [z]) ++ A0 := by
    simp only [List.append_assoc, List.singleton_append]
  rw [hOld] at E
  have F := replace_pending E Kall
  simpa [Kall, collect_blocks, List.append_assoc, List.length_append, List.length_cons,
    List.length_singleton, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using F

end CoefficientTwoPrecision.StageExtension

#print axioms CoefficientTwoPrecision.StageExtension.empty_step
#print axioms CoefficientTwoPrecision.StageExtension.replace_pending

#print axioms CoefficientTwoPrecision.StageExtension.empty_many
#print axioms CoefficientTwoPrecision.StageExtension.advance_width
