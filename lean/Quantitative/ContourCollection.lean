import Quantitative.ContourAggregation

/- Finite collections of the actual contours chosen for surviving candidates.

Each candidate contributes one concrete SourceContour. Enumerating the
candidate subtype gives the actual finite contour list. The lemmas below
transport the already proved local properties to that list and combine
within-contour simplicity with the cross-candidate collision exclusion.
-/

namespace CoefficientTwoPrecision.ContourCollection

open SuperpermutationUpperBound SourceFamilyAdapter SourceAdvancement SourceUniverse
open ContourAggregation

variable {ι : Type*} {A : List Nat} {h : Nat}

/-- One actual contour for each surviving candidate, in a fixed finite
enumeration. No injectivity of the contour map is needed for its length. -/
noncomputable def collection (T : Finset ι) (C : T → SourceContour A h) :
    List (SourceContour A h) := (Finset.univ.toList : List T).map C

theorem collection_length (T : Finset ι) (C : T → SourceContour A h) :
    (collection T C).length = T.card := by
  simp only [collection, List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_coe]

theorem collection_mem (T : Finset ι) (C : T → SourceContour A h) (D : SourceContour A h) :
    D ∈ collection T C ↔ ∃ i : T, C i = D := by
  simp only [collection, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]

theorem collection_forall (T : Finset ι) (C : T → SourceContour A h)
    (P : SourceContour A h → Prop) (hP : ∀ i : T, P (C i)) :
    ∀ D ∈ collection T C, P D := by
  intro D hD
  obtain ⟨i, rfl⟩ := (collection_mem T C D).mp hD
  exact hP i

theorem collection_rows (T : Finset ι) (C : T → SourceContour A h) :
    sourceRows (collection T C) = (Finset.univ.toList : List T).flatMap (fun i => (C i).rows) := by
  simp only [sourceRows, collection, List.flatMap_map, Function.comp_def]

theorem collection_row_mem (T : Finset ι) (C : T → SourceContour A h) (row : Row Nat) :
    row ∈ sourceRows (collection T C) ↔ ∃ i : T, row ∈ (C i).rows := by
  rw [collection_rows]
  simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and]

/-- Any row property proved for each actual contour holds for the
concatenated source row list. -/
theorem collection_row_forall (T : Finset ι) (C : T → SourceContour A h)
    (P : Row Nat → Prop) (hP : ∀ i : T, ∀ row ∈ (C i).rows, P row) :
    ∀ row ∈ sourceRows (collection T C), P row := by
  intro row hrow
  obtain ⟨i, hi⟩ := (collection_row_mem T C row).mp hrow
  exact hP i row hi

theorem collection_insertion (T : Finset ι) (C : T → SourceContour A h)
    (controls old : List Nat)
    (hinsertion : ∀ i : T, ∀ row ∈ (C i).rows, InsertionAbove controls old row.base) :
    ∀ row ∈ sourceRows (collection T C), InsertionAbove controls old row.base :=
  collection_row_forall T C (fun row => InsertionAbove controls old row.base) hinsertion

/-- Within-contour and cross-candidate relations combine on the actual
flattened row list. The subtype enumeration has no repeated candidate. -/
theorem collection_pairwise (T : Finset ι) (C : T → SourceContour A h)
    (R : Row Nat → Row Nat → Prop)
    (hwithin : ∀ i : T, (C i).rows.Pairwise R)
    (hcross : ∀ i j : T, i ≠ j → ∀ row ∈ (C i).rows, ∀ other ∈ (C j).rows, R row other) :
    (sourceRows (collection T C)).Pairwise R := by
  rw [collection_rows]
  apply List.pairwise_flatMap.mpr
  refine ⟨fun i _ => hwithin i, ?_⟩
  have hindices : (Finset.univ.toList : List T).Pairwise (fun i j => i ≠ j) :=
    Finset.nodup_toList Finset.univ
  exact hindices.imp (fun {i j} hij => hcross i j hij)

/-- Original cyclic equality implies Mathlib's rotation relation. Empty
rows need no special case because original CyclicEq includes its index. -/
theorem cyclicEq_isRotated {a b : List Nat} (hab : CyclicEq a b) : a.IsRotated b := by
  obtain ⟨j, hj⟩ := hab
  exact ⟨j.val, by simpa only [SourceUniverse.rotateLeft_eq_rotate] using hj⟩

/-- This form accepts the actual local source builder's simplicity and
the geometric cross-candidate exclusion directly. -/
theorem collection_distinct (T : Finset ι) (C : T → SourceContour A h)
    (hwithin : ∀ i : T, (C i).rows.Pairwise (fun row other => ¬ row.base.IsRotated other.base))
    (hcross : ∀ i j : T, i ≠ j → ∀ row ∈ (C i).rows, ∀ other ∈ (C j).rows,
      ¬ row.base.IsRotated other.base) :
    (sourceRows (collection T C)).Pairwise (fun row other => ¬ CyclicEq row.base other.base) := by
  have hall := collection_pairwise T C (fun row other => ¬ row.base.IsRotated other.base) hwithin hcross
  exact hall.imp (fun hnot heq => hnot (cyclicEq_isRotated heq))

/-- Actual aggregate charge and connector count after choosing the finite
family. The right sides use the number of surviving candidates. -/
theorem collection_counts (T : Finset ι) (C : T → SourceContour A h) (r M : Nat)
    (hcharge : ∀ i : T, ((C i).rows.map Row.charge).sum = 2 * (r - 1) * M)
    (hg : ∀ i : T, portGcd (C i).rows h ≤ r - 1) :
    ((sourceRows (collection T C)).map Row.charge).sum = T.card * (2 * (r - 1) * M) ∧
      (circles (collection T C)).length ≤ T.card * (2 * (r - 1) ^ 2) := by
  have hcharge' := collection_forall T C
    (fun D => (D.rows.map Row.charge).sum = 2 * (r - 1) * M) hcharge
  have hg' := collection_forall T C (fun D => portGcd D.rows h ≤ r - 1) hg
  constructor
  · simpa only [collection_length] using uniform_charge (collection T C) r M hcharge'
  · simpa only [collection_length] using connector_bound (collection T C) r hg'

/-- The actual Nat-valued perturbation estimate from the source builder
implies the averaged relative error needed by the final factorization. -/
theorem collection_averaged_error (T : Finset ι) (C : T → SourceContour A h)
    (r m M W K : Nat) (hr : 6 ≤ r) (hm : 0 < m) (hmM : m ≤ M)
    (hK : K ≤ 52 * r ^ 4 * W ^ 2)
    (hperturb : ∀ i : T,
      |((C i).rows.length : ℚ) - ((M * ((r - 2) * M + r * (r - 1) + 1) : Nat) : ℚ)| ≤
        ((10 * r ^ 2 * K * M : Nat) : ℚ)) :
    ∃ u : ℚ,
      ((sourceRows (collection T C)).length : ℚ) =
        (T.card : ℚ) * (((r : ℚ) - 2) * (M : ℚ) ^ 2) * (1 + u) ∧
      |u| ≤ (2 * (r : ℚ) + 1040 * (r : ℚ) ^ 5 * (W : ℚ) ^ 2) / (m : ℚ) := by
  have hbase : ((M * ((r - 2) * M + r * (r - 1) + 1) : Nat) : ℚ) =
      ((r : ℚ) - 2) * (M : ℚ) ^ 2 + ((r : ℚ) * ((r : ℚ) - 1) + 1) * (M : ℚ) := by
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (show 2 ≤ r by omega),
      Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_ofNat, Nat.cast_one]
    ring
  have hlocal : ∀ D ∈ collection T C,
      |(D.rows.length : ℚ) - (((r : ℚ) - 2) * (M : ℚ) ^ 2 +
        ((r : ℚ) * ((r : ℚ) - 1) + 1) * (M : ℚ))| ≤
      10 * (r : ℚ) ^ 2 * (K : ℚ) * (M : ℚ) := by
    apply collection_forall T C
    intro i
    have hi := hperturb i
    rw [hbase] at hi
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hi
  simpa only [collection_length] using averaged_row_error (collection T C) r m M W K hr hm hmM hK hlocal

end CoefficientTwoPrecision.ContourCollection

#print axioms CoefficientTwoPrecision.ContourCollection.collection_length
#print axioms CoefficientTwoPrecision.ContourCollection.collection_distinct
#print axioms CoefficientTwoPrecision.ContourCollection.collection_counts
#print axioms CoefficientTwoPrecision.ContourCollection.collection_averaged_error
