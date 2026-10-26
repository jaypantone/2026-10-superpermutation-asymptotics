import ConstAsym.Bridge

/-! Declaration-preserving extraction of the shortest-length definitions from
the supplied ConstAsym.Main. The unrelated older upper theorem and Hunter.Paper
imports are omitted. The definitions and proofs below are unchanged. -/

namespace ConstAsym

open SuperpermutationBounds

/-- The least length of a word over `Fin n` that contains every permutation of `Fin n` as a factor. -/
noncomputable def L (n : ℕ) : ℕ :=
  sInf {m | ∃ w : List (Fin n), Covers w ∧ w.length = m}

theorem exists_covers (n : ℕ) : ∃ w : List (Fin n), Covers w := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    refine ⟨[], ?_⟩
    intro p hp _
    exact ⟨[], [], by simp [List.eq_nil_of_length_eq_zero hp]⟩
  · obtain ⟨w, hw, _⟩ := exists_covers_length_eq h
    exact ⟨w, hw⟩

/-- `L n` is attained. -/
theorem L_spec (n : ℕ) : ∃ w : List (Fin n), Covers w ∧ w.length = L n := by
  obtain ⟨w, hw⟩ := exists_covers n
  exact Nat.sInf_mem (s := {m | ∃ w : List (Fin n), Covers w ∧ w.length = m}) ⟨w.length, w, hw, rfl⟩

/-- No covering word is shorter than `L n`. -/
theorem L_le_length {n : ℕ} {w : List (Fin n)} (hw : Covers w) : L n ≤ w.length :=
  Nat.sInf_le ⟨w, hw, rfl⟩


end ConstAsym
