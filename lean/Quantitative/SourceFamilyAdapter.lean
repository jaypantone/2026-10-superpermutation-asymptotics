import Quantitative.SourceInventory
import Quantitative.SourceComplement

/-!
# From actual source contours to the arbitrary-width Stage certificate

The input consists of actual closed source contours, their full-row runs,
their membership in the insertion-chain universe, and cyclic distinctness
of their rows. Transported levels, safe connectors, pending complements,
coverage and all counts are constructed and proved here. No input field
assumes a Stage, an advanced Level, or a superpermutation theorem.
-/

namespace CoefficientTwoPrecision.SourceFamilyAdapter

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound43586371
open CoefficientTwoPrecision.SourceUniverse CoefficientTwoPrecision.StageExtension
open CoefficientTwoPrecision.SafeConnectors CoefficientTwoPrecision.SourceAdvancement
open CoefficientTwoPrecision.SourceInventory

/-- A concrete source contour together with the local geometric facts
needed for its safe advancement. -/
structure SourceContour (A : List Nat) (h : Nat) where
  rows : List (Row Nat)
  closed : ClosedTrail rows
  basedOn : BasedOn A 9 rows
  headWord : List Nat
  headLength : headWord.length = h + 1
  headNodup : headWord.Nodup
  headSupport : ∀ a ∈ headWord, a ∈ A
  mobile : Nat
  start : Nat
  runLength : Nat
  gridLength : Nat
  fullRun : LiteralFRun rows start runLength headWord mobile
  gridPositive : 0 < gridLength
  gridFits : portGcd rows h * gridLength ≤ runLength
  runFits : runLength ≤ h + 1
  portsCovered : h + 1 ≤ 2 * (portGcd rows h * gridLength)

def sourceRows {A : List Nat} {h : Nat} (F : List (SourceContour A h)) : List (Row Nat) :=
  F.flatMap SourceContour.rows

def components {A : List Nat} {h : Nat} (F : List (SourceContour A h)) (next : Nat) :
    List (List (Row Nat)) := F.flatMap (fun C => advancedComponents C.rows next h)

def circles {A : List Nat} {h : Nat} (F : List (SourceContour A h)) : List (List Nat) :=
  F.flatMap (fun C => advancedCircles C.rows C.headWord C.start 10 h C.gridLength)

theorem sourceRows_basedOn {A : List Nat} {h : Nat} (F : List (SourceContour A h)) :
    BasedOn A 9 (sourceRows F) := by
  intro r hr
  obtain ⟨C, hC, hr⟩ := List.mem_flatMap.mp hr
  exact C.basedOn r hr

theorem components_inventory {A : List Nat} {h : Nat} (F : List (SourceContour A h))
    (next : Nat) (hA : A.length = h + 2) (hn : 3 ≤ h + 2) :
    (components F next).flatten.Perm (Transport.packingRows (sourceRows F) next) := by
  induction F with
  | nil => simp [components, sourceRows, Transport.packingRows]
  | cons C rest ih =>
    have hlen : ∀ r ∈ C.rows, r.base.length = h + 2 :=
      fun r hr => (C.basedOn r hr).2.1.length_eq.trans hA
    have hk := advancedComponents_inventory C.rows next h hn hlen
      (fun r hr => (C.basedOn r hr).2.2.2)
    simpa only [components, sourceRows, List.flatMap_cons, List.flatten_append,
      Transport.packingRows, List.flatMap_append] using hk.append ih

theorem components_level {A : List Nat} {h : Nat} (F : List (SourceContour A h))
    (next : Nat) (hA : A.length = h + 2) (hn : 3 ≤ h + 2)
    (hnext : next ∉ A) (hnext9 : next ≠ 9) :
    Level (next :: A) (h + 2) (components F next) :=
  Level.flatMap F _ (fun C _ => advancedLevel C.rows A next h C.closed hA hn
    C.basedOn hnext hnext9)

theorem circles_valid {A : List Nat} {h : Nat} (F : List (SourceContour A h))
    (h10 : 10 ∉ A) : CircleFamilyValid (h + 2) (circles F) := by
  intro cc hcc
  obtain ⟨C, hC, hcc⟩ := List.mem_flatMap.mp hcc
  exact advancedCircles_valid C.rows C.headWord C.start 10 h C.gridLength
    C.headLength C.headNodup (fun hm => h10 (C.headSupport 10 hm)) cc hcc

theorem circles_support {A : List Nat} {h : Nat} (F : List (SourceContour A h)) :
    ∀ cc ∈ circles F, ∀ a ∈ cc, a ∈ 10 :: A := by
  intro cc hcc a ha
  obtain ⟨C, hC, hcc⟩ := List.mem_flatMap.mp hcc
  have hm := advancedCircles_support C.rows C.headWord C.start 10 h C.gridLength cc hcc a ha
  rcases List.mem_cons.mp hm with hm | hm
  · exact List.mem_cons.mpr (Or.inl hm)
  · exact List.mem_cons.mpr (Or.inr (C.headSupport a hm))

theorem components_safe {A : List Nat} {h : Nat} (F : List (SourceContour A h))
    (next : Nat) (hA : A.length = h + 2) (hn : 3 ≤ h + 2) :
    ∀ W ∈ components F next, SafeComp W 10 (h + 2) (circles F) := by
  intro W hW
  obtain ⟨C, hC, hW⟩ := List.mem_flatMap.mp hW
  have hs := advanced_safe C.rows C.start C.runLength C.headWord C.mobile next 10 h C.gridLength
    C.headLength C.fullRun hn
    (fun r hr => (C.basedOn r hr).2.1.length_eq.trans hA)
    (fun r hr => (C.basedOn r hr).2.2.2)
    C.gridPositive C.gridFits C.runFits C.portsCovered W hW
  exact hs.mono (fun cc hcc => List.mem_flatMap.mpr ⟨C, hC, hcc⟩)

theorem circles_length {A : List Nat} {h : Nat} (F : List (SourceContour A h)) :
    (circles F).length = (F.map (fun C => 2 * (portGcd C.rows h) ^ 2)).sum := by
  simp only [circles, List.length_flatMap, advancedCircles_length]

/-- A family of actual source contours over every old pending representative.
Uniform source and connector counts are numerical data derived by the
source packing construction; no advanced structural certificate is assumed. -/
structure SourceFamily (A0 controls : List Nat) (next h : Nat) where
  oldPositive : 0 < A0.length
  alphabetSize : (controls ++ A0).length = h + 2
  sizeThree : 3 ≤ h + 2
  nextFresh : next ∉ controls ++ A0
  nextNine : next ≠ 9
  finalFresh : 10 ∉ controls ++ A0
  contours : List Nat → List (SourceContour (controls ++ A0) h)
  countRows : Nat
  countCharge : Nat
  countCircles : Nat
  insertion : ∀ d, d.Perm A0 → ∀ r ∈ sourceRows (contours d),
    InsertionAbove controls d r.base
  distinct : ∀ d, d.Perm A0 →
    (sourceRows (contours d)).Pairwise (fun r s => ¬ CyclicEq r.base s.base)
  rows : ∀ d, d.Perm A0 → (sourceRows (contours d)).length = countRows
  charge : ∀ d, d.Perm A0 → ((sourceRows (contours d)).map Row.charge).sum = countCharge
  circleCount : ∀ d, d.Perm A0 →
    ((contours d).map (fun C => 2 * (portGcd C.rows h) ^ 2)).sum = countCircles

/-- Construct the complete arbitrary-width block certificate from literal
source geometry and its occurrence packing. -/
noncomputable def toWidthBlockFamily {A0 controls : List Nat} {next h : Nat}
    (K : SourceFamily A0 controls next h) : WidthBlockFamily A0 controls next where
  comps d := components (K.contours d) next
  circles d := circles (K.contours d)
  remaining d := SourceComplement.remaining controls d (sourceRows (K.contours d))
  sourceRows := K.countRows
  sourceCharge := K.countCharge
  advancedCircles := K.countCircles
  sourceBound := by
    have hs := (SourceComplement.remaining_length controls A0 (sourceRows (K.contours A0))
      K.oldPositive (K.insertion A0 (List.Perm.refl _)) (K.distinct A0 (List.Perm.refl _))).2
    rwa [K.rows A0 (List.Perm.refl _)] at hs
  level d hd := by
    rw [K.alphabetSize]
    exact components_level (K.contours d) next K.alphabetSize K.sizeThree K.nextFresh K.nextNine
  valid d hd := by
    rw [K.alphabetSize]
    exact circles_valid (K.contours d) K.finalFresh
  support d hd cc hcc a ha := by
    have hm := circles_support (K.contours d) cc hcc a ha
    rcases List.mem_cons.mp hm with hm | hm
    · exact List.mem_cons.mpr (Or.inl hm)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)
  safe d hd := by
    rw [K.alphabetSize]
    exact components_safe (K.contours d) next K.alphabetSize K.sizeThree
  pend d hd e he := (SourceComplement.remaining_perm controls d (sourceRows (K.contours d)) he).trans
    ((List.Perm.refl controls).append hd)
  cover d hd t ht y hy := by
    have hdpos : 0 < d.length := by rw [hd.length_eq]; exact K.oldPositive
    rcases SourceComplement.source_or_remaining controls d (sourceRows (K.contours d)) hdpos
      (K.insertion d hd) (K.distinct d hd) t ht with ⟨r, hr, hrt⟩ | ht
    · have hvalid := (sourceRows_basedOn (K.contours d) r hr).1
      have hry : InInsertionBlock next r.base y := (InInsertionBlock.congr_base hrt).mpr hy
      obtain ⟨s, hs, hsy⟩ := (rows_cyclicEq_iff_inInsertionBlock hvalid next y).mpr hry
      have hm : s ∈ Transport.packingRows (sourceRows (K.contours d)) next :=
        List.mem_flatMap.mpr ⟨r, hr, hs⟩
      exact Or.inl ⟨s, (components_inventory (K.contours d) next K.alphabetSize K.sizeThree).mem_iff.mpr hm, hsy⟩
    · exact Or.inr ⟨t, ht, hy⟩
  rows d hd := by
    have hp := components_inventory (K.contours d) next K.alphabetSize K.sizeThree
    have hc := Transport.packingRows_counts (sourceRows (K.contours d)) next (controls ++ A0).length
      ((sourceRows_basedOn (K.contours d)).ready K.nextFresh K.nextNine)
    rw [hp.length_eq, hc.1, K.rows d hd]
  charge d hd := by
    have hp := components_inventory (K.contours d) next K.alphabetSize K.sizeThree
    have hc := Transport.packingRows_counts (sourceRows (K.contours d)) next (controls ++ A0).length
      ((sourceRows_basedOn (K.contours d)).ready K.nextFresh K.nextNine)
    rw [(hp.map Row.charge).sum_eq, hc.2.1, K.charge d hd]
  ncirc d hd := (circles_length (K.contours d)).trans (K.circleCount d hd)
  npend d hd := by
    have hdpos : 0 < d.length := by rw [hd.length_eq]; exact K.oldPositive
    have hn := (SourceComplement.remaining_length controls d (sourceRows (K.contours d)) hdpos
      (K.insertion d hd) (K.distinct d hd)).1
    simpa only [hd.length_eq, K.rows d hd] using hn

end CoefficientTwoPrecision.SourceFamilyAdapter

#print axioms CoefficientTwoPrecision.SourceFamilyAdapter.toWidthBlockFamily
