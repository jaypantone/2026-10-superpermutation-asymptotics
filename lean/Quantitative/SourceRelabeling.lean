import Quantitative.SourceFamilyAdapter
import SuperpermutationUpperBound43586371.Relabel

/-!
# Relabeling actual source contours

Literal full-row runs, insertion chains, cyclic distinctness, and the
connector gcd are preserved by an injective relabeling. The contour map
below acts on the actual row list and head word. It does not assume a
new contour or any of its geometric certificates.
-/

namespace CoefficientTwoPrecision.SourceRelabeling

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound43586371
open SuperpermutationUpperBound.Certificates.CircleBase
open SafeConnectors SourceAdvancement SourceFamilyAdapter SourceUniverse

/-- In-range row lookup commutes with literal relabeling. -/
theorem rowAt_map (f : ℕ → ℕ) (rows : List (Row ℕ)) (i : ℕ)
    (hi : i < rows.length) :
    rowAt (rows.map (Row.map f)) i = (rowAt rows i).map f := by
  have hi' : i < (rows.map (Row.map f)).length := by simpa only [List.length_map] using hi
  simp only [rowAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
    Option.getD_some, List.getElem_map]

/-- Every literal full-run equality survives the same relabeling. -/
theorem literalFRun_map (f : ℕ → ℕ) {rows : List (Row ℕ)} {start R : ℕ}
    {H : List ℕ} {mobile : ℕ} (h : LiteralFRun rows start R H mobile) :
    LiteralFRun (rows.map (Row.map f)) start R (H.map f) (f mobile) := by
  refine ⟨by simpa only [List.length_map] using h.1, ?_⟩
  intro j hj
  have hbound := h.1
  have hi : start + j < rows.length := by omega
  obtain ⟨hbase, hvisible⟩ := h.2 j hj
  rw [rowAt_map f rows (start + j) hi]
  constructor
  · simp only [Row.map_base, hbase, List.map_append, List.map_cons, List.map_nil, rot_map]
  · simpa only [Row.map_visible, Row.map_base_length] using hvisible

@[simp] theorem portGcd_map (f : ℕ → ℕ) (rows : List (Row ℕ)) (h : ℕ) :
    portGcd (rows.map (Row.map f)) h = portGcd rows h := by
  simp only [portGcd, List.map_map, Function.comp_def, delta, Row.map_charge] <;> rfl

/-- Injectivity reflects equality up to cyclic rotation. -/
theorem cyclicEq_of_map (f : ℕ → ℕ) (hf : Function.Injective f)
    {x y : List ℕ} (h : CyclicEq (x.map f) (y.map f)) : CyclicEq x y := by
  obtain ⟨j, hj⟩ := h
  refine ⟨⟨j.val, by simpa only [List.length_map] using j.isLt⟩, ?_⟩
  apply List.map_injective_iff.mpr hf
  exact (rot_map f x j.val).symm.trans hj

theorem insertionAbove_map {α β : Type*} (f : α → β) {controls d y : List α}
    (h : InsertionAbove controls d y) :
    InsertionAbove (controls.map f) (d.map f) (y.map f) := by
  induction controls generalizing y with
  | nil => exact h.map f
  | cons v controls ih =>
    obtain ⟨x, hx, j, hj⟩ := h
    refine ⟨x.map f, ih hx, j, ?_⟩
    simpa only [List.map_append, List.map_rotate, List.map_cons, List.map_nil] using hj.map f

/-- Relabel a concrete contour and retain the same ambient alphabet up to
permutation. Every structural and full-run field is proved from the old one. -/
def mapContour {A : List ℕ} {h : ℕ} (C : SourceContour A h)
    (f : ℕ → ℕ) (hf : Function.Injective f) (h9 : f 9 = 9)
    (hA : (A.map f).Perm A) : SourceContour A h where
  rows := C.rows.map (Row.map f)
  closed := closedTrail_map f C.closed
  basedOn := basedOn_congr_alphabet
    (by simpa only [h9] using basedOn_map f (fun a b hab => hf hab) C.basedOn) hA
  headWord := C.headWord.map f
  headLength := by simpa only [List.length_map] using C.headLength
  headNodup := C.headNodup.map (fun a b hab => hf hab)
  headSupport := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact hA.mem_iff.mp (List.mem_map.mpr ⟨x, C.headSupport x hx, rfl⟩)
  mobile := f C.mobile
  start := C.start
  runLength := C.runLength
  gridLength := C.gridLength
  fullRun := literalFRun_map f C.fullRun
  gridPositive := C.gridPositive
  gridFits := by simpa only [portGcd_map] using C.gridFits
  runFits := C.runFits
  portsCovered := by simpa only [portGcd_map] using C.portsCovered

@[simp] theorem mapContour_rows {A : List ℕ} {h : ℕ} (C : SourceContour A h)
    (f : ℕ → ℕ) (hf : Function.Injective f) (h9 : f 9 = 9)
    (hA : (A.map f).Perm A) :
    (mapContour C f hf h9 hA).rows = C.rows.map (Row.map f) := rfl

/-- Mapping a whole actual collection preserves its occurrence list exactly. -/
theorem sourceRows_map {A : List ℕ} {h : ℕ} (F : List (SourceContour A h))
    (f : ℕ → ℕ) (hf : Function.Injective f) (h9 : f 9 = 9)
    (hA : (A.map f).Perm A) :
    sourceRows (F.map (fun C => mapContour C f hf h9 hA)) =
      (sourceRows F).map (Row.map f) := by
  simp only [sourceRows, List.flatMap_map, List.map_flatMap, Function.comp_def, mapContour_rows]

/-- The actual collection remains cyclically simple. -/
theorem sourceRows_distinct_map {A : List ℕ} {h : ℕ} (F : List (SourceContour A h))
    (f : ℕ → ℕ) (hf : Function.Injective f) (h9 : f 9 = 9)
    (hA : (A.map f).Perm A)
    (hdistinct : (sourceRows F).Pairwise (fun r s => ¬ CyclicEq r.base s.base)) :
    (sourceRows (F.map (fun C => mapContour C f hf h9 hA))).Pairwise
      (fun r s => ¬ CyclicEq r.base s.base) := by
  rw [sourceRows_map]
  apply List.pairwise_map.mpr
  exact hdistinct.imp (fun {r s} hrs hmap => hrs (cyclicEq_of_map f hf hmap))

/-- Charge and connector counts do not depend on the chosen letter names. -/
theorem source_counts_map {A : List ℕ} {h : ℕ} (F : List (SourceContour A h))
    (f : ℕ → ℕ) (hf : Function.Injective f) (h9 : f 9 = 9)
    (hA : (A.map f).Perm A) :
    (sourceRows (F.map (fun C => mapContour C f hf h9 hA))).length = (sourceRows F).length ∧
      ((sourceRows (F.map (fun C => mapContour C f hf h9 hA))).map Row.charge).sum =
        ((sourceRows F).map Row.charge).sum ∧
      ((F.map (fun C => mapContour C f hf h9 hA)).map
        (fun C => 2 * (portGcd C.rows h) ^ 2)).sum =
        (F.map (fun C => 2 * (portGcd C.rows h) ^ 2)).sum := by
  simp only [sourceRows_map, List.length_map, List.map_map, Function.comp_def, Row.map_charge,
    mapContour_rows, portGcd_map, and_self]

end CoefficientTwoPrecision.SourceRelabeling

#print axioms CoefficientTwoPrecision.SourceRelabeling.mapContour
#print axioms CoefficientTwoPrecision.SourceRelabeling.sourceRows_distinct_map
#print axioms CoefficientTwoPrecision.SourceRelabeling.source_counts_map
