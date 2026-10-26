import Quantitative.StageExtension

/-!
# Actual pending complements in the finite insertion universe

Every selected source-row occurrence is matched to its canonical insertion
representative. Cyclic distinctness of the source rows proves that the
selected representative list has no repeats. Removing that actual list
from the insertion universe therefore leaves exactly D-B pending entries.
No cardinality or injectivity of the selected representatives is assumed.
-/

namespace CoefficientTwoPrecision.SourceComplement

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open CoefficientTwoPrecision.SourceUniverse

theorem cyclicEq_of_isRotated {a b : List Nat} (ha : 0 < a.length)
    (hab : a.IsRotated b) : CyclicEq a b := by
  obtain ⟨j, hj⟩ := hab
  refine ⟨⟨j % a.length, Nat.mod_lt _ ha⟩, ?_⟩
  change rot a (j % a.length) = b
  rw [rot_mod]
  change a.rotateLeft j = b
  rw [rotateLeft_eq_rotate]
  exact hj

theorem representative_exists (controls d : List Nat) (hd : 0 < d.length)
    (r : Row Nat) (hr : InsertionAbove controls d r.base) :
    ∃ t ∈ sourceUniverse controls d, CyclicEq t r.base := by
  obtain ⟨t, ht, hcyc⟩ := universe_covers_insertionAbove controls d hd hr
  have htpos : 0 < t.length := by rw [universe_entry_length controls d ht]; omega
  exact ⟨t, ht, cyclicEq_of_isRotated htpos hcyc⟩

noncomputable def representative (controls d : List Nat) (r : Row Nat) : List Nat :=
  if h : ∃ t ∈ sourceUniverse controls d, CyclicEq t r.base then Classical.choose h else []

theorem representative_spec (controls d : List Nat) (hd : 0 < d.length)
    (r : Row Nat) (hr : InsertionAbove controls d r.base) :
    representative controls d r ∈ sourceUniverse controls d ∧
      CyclicEq (representative controls d r) r.base := by
  have hex := representative_exists controls d hd r hr
  simp only [representative, dif_pos hex]
  exact Classical.choose_spec hex

noncomputable def selectedRepresentatives (controls d : List Nat) (rows : List (Row Nat)) :
    List (List Nat) := rows.map (representative controls d)

noncomputable def remaining (controls d : List Nat) (rows : List (Row Nat)) : List (List Nat) :=
  (sourceUniverse controls d).diff (selectedRepresentatives controls d rows)

theorem selected_nodup (controls d : List Nat) (rows : List (Row Nat)) (hd : 0 < d.length)
    (hchain : ∀ r ∈ rows, InsertionAbove controls d r.base)
    (hdist : rows.Pairwise (fun r s => ¬ CyclicEq r.base s.base)) :
    (selectedRepresentatives controls d rows).Nodup := by
  change (rows.map (representative controls d)).Pairwise (fun a b => a ≠ b)
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem (p := hdist)
  intro r s hr hs hne heq
  have h1 := (representative_spec controls d hd r (hchain r hr)).2
  have h2 := (representative_spec controls d hd s (hchain s hs)).2
  exact hne (h1.symm.trans (heq ▸ h2))

theorem selected_subset (controls d : List Nat) (rows : List (Row Nat)) (hd : 0 < d.length)
    (hchain : ∀ r ∈ rows, InsertionAbove controls d r.base) :
    selectedRepresentatives controls d rows ⊆ sourceUniverse controls d := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact (representative_spec controls d hd r (hchain r hr)).1

/-- Selected representatives and the literal list difference partition the
whole insertion universe with occurrence multiplicity preserved. -/
theorem selected_remaining_perm (controls d : List Nat) (rows : List (Row Nat))
    (hd : 0 < d.length) (hchain : ∀ r ∈ rows, InsertionAbove controls d r.base)
    (hdist : rows.Pairwise (fun r s => ¬ CyclicEq r.base s.base)) :
    (selectedRepresentatives controls d rows ++ remaining controls d rows).Perm
      (sourceUniverse controls d) := by
  have hs := List.subperm_of_subset (selected_nodup controls d rows hd hchain hdist)
    (selected_subset controls d rows hd hchain)
  exact List.subperm_append_diff_self_of_count_le (fun t ht => hs.count_le t)

theorem remaining_length (controls d : List Nat) (rows : List (Row Nat))
    (hd : 0 < d.length) (hchain : ∀ r ∈ rows, InsertionAbove controls d r.base)
    (hdist : rows.Pairwise (fun r s => ¬ CyclicEq r.base s.base)) :
    (remaining controls d rows).length = risingCount d.length controls.length - rows.length ∧
      rows.length ≤ risingCount d.length controls.length := by
  have hl := (selected_remaining_perm controls d rows hd hchain hdist).length_eq
  simp only [List.length_append, selectedRepresentatives, List.length_map,
    universe_length] at hl
  omega

theorem remaining_perm (controls d : List Nat) (rows : List (Row Nat))
    {t : List Nat} (ht : t ∈ remaining controls d rows) : t.Perm (controls ++ d) :=
  universe_perm controls d (List.diff_subset _ _ ht)

/-- Every universe entry is either a selected actual source row's cyclic
class or an actual pending complement entry. -/
theorem source_or_remaining (controls d : List Nat) (rows : List (Row Nat))
    (hd : 0 < d.length) (hchain : ∀ r ∈ rows, InsertionAbove controls d r.base)
    (hdist : rows.Pairwise (fun r s => ¬ CyclicEq r.base s.base))
    (t : List Nat) (ht : t ∈ sourceUniverse controls d) :
    (∃ r ∈ rows, CyclicEq r.base t) ∨ t ∈ remaining controls d rows := by
  have hm := (selected_remaining_perm controls d rows hd hchain hdist).mem_iff.mpr ht
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    exact Or.inl ⟨r, hr, (representative_spec controls d hd r (hchain r hr)).2.symm⟩
  · exact Or.inr hm

end CoefficientTwoPrecision.SourceComplement

#print axioms CoefficientTwoPrecision.SourceComplement.selected_remaining_perm
#print axioms CoefficientTwoPrecision.SourceComplement.remaining_length
#print axioms CoefficientTwoPrecision.SourceComplement.source_or_remaining
