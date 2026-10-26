import Quantitative.LiteralTrail

/-!
# Validity, alphabet inventory, and exact charge of actual emitted rows

For a concrete suffix-valid schedule, every emitted base is a permutation
of the initial base. Thus nodup, satellite freshness, and the alphabet are
preserved. Every update emits exactly one short row of charge two; all
other rows have charge zero. These are statements about the original Row
type and the actual source-occurrence list.
-/

namespace CoefficientTwoPrecision.RowValidity

open JointStates LiteralState LiteralSchedule LiteralTrail
open SuperpermutationUpperBound

variable {α : Type}

theorem fullIterate_perm (stationary : List α) (mobile : α) (moves : Nat) :
    (fullIterate moves (stationary ++ [mobile])).Perm (stationary ++ [mobile]) := by
  rw [fullIterate_formula, LiteralState.rotateLeft_eq_rotate]
  exact (List.rotate_perm stationary moves).append_right [mobile]

theorem updateEnd_perm (base : List α) (moves : Nat)
    (hbase : ∃ stationary mobile, base = stationary ++ [mobile])
    (hsuffix : ∃ pre resident crossed token,
      fullIterate moves base = pre ++ [resident, crossed, token]) :
    (updateEnd moves base).Perm base := by
  obtain ⟨stationary, mobile, rfl⟩ := hbase
  obtain ⟨pre, resident, crossed, token, hpre⟩ := hsuffix
  have hp := fullIterate_perm stationary mobile moves
  rw [hpre] at hp
  exact (by simpa only [updateEnd, hpre] using
    (shortStep_perm pre resident crossed token).trans hp)

theorem updateRows_inventory (satellite : α) (stationary : List α) (mobile : α)
    (moves : Nat) (row : Row α)
    (hrow : row ∈ updateRows satellite moves (stationary ++ [mobile])) :
    row.base.Perm (stationary ++ [mobile]) ∧ row.satellite = satellite ∧
      (row.visible = row.base.length ∨ row.visible = row.base.length - 2) := by
  simp only [updateRows, List.mem_append, List.mem_map, List.mem_singleton] at hrow
  rcases hrow with ⟨i, _, rfl⟩ | rfl
  · exact ⟨fullIterate_perm stationary mobile i, rfl, Or.inl rfl⟩
  · exact ⟨fullIterate_perm stationary mobile moves, rfl, Or.inr rfl⟩

theorem updateRows_valid (satellite : α) (stationary : List α) (mobile : α)
    (moves : Nat) (hnodup : (stationary ++ [mobile]).Nodup)
    (hfresh : satellite ∉ stationary ++ [mobile])
    (hlen : 3 ≤ (stationary ++ [mobile]).length) :
    ∀ row ∈ updateRows satellite moves (stationary ++ [mobile]), row.Valid := by
  intro row hrow
  obtain ⟨hperm, hsat, hkind⟩ := updateRows_inventory satellite stationary mobile moves row hrow
  have hrowlen := hperm.length_eq
  refine ⟨hperm.nodup_iff.mpr hnodup, ?_, ?_, ?_⟩
  · rw [hsat]
    exact fun hmem => hfresh (hperm.mem_iff.mp hmem)
  · rcases hkind with hfull | hshort <;> omega
  · rcases hkind with hfull | hshort <;> omega

theorem updateRows_charge (satellite : α) (stationary : List α) (mobile : α)
    (moves : Nat) (hlen : 2 ≤ (stationary ++ [mobile]).length) :
    ((updateRows satellite moves (stationary ++ [mobile])).map Row.charge).sum = 2 := by
  have hshort : (shortRow (fullIterate moves (stationary ++ [mobile])) satellite).charge = 2 := by
    apply shortRow_charge
    rw [(fullIterate_perm stationary mobile moves).length_eq]
    exact hlen
  have hfull : ((List.range moves).map
      (fun i => (fullRow (fullIterate i (stationary ++ [mobile])) satellite).charge)).sum = 0 := by
    simp [fullRow, Row.charge]
  simp only [updateRows, List.map_append, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  rw [hfull, hshort]
  omega

/-- The complete literal endpoint has exactly the initial alphabet. -/
theorem scheduleEnd_perm (sweeps : List Nat) (base : List α)
    (hvalid : SuffixSchedule sweeps base) : (scheduleEnd sweeps base).Perm base := by
  induction sweeps generalizing base with
  | nil => exact List.Perm.refl base
  | cons moves sweeps ih =>
    obtain ⟨⟨stationary, mobile, hbase, _⟩, hsuffix, hrest⟩ := hvalid
    exact (ih _ hrest).trans (updateEnd_perm base moves ⟨stationary, mobile, hbase⟩ hsuffix)

/-- Every emitted occurrence has the initial alphabet, the fixed satellite,
and one of the two allowed visible lengths. -/
theorem scheduleRows_inventory (satellite : α) (sweeps : List Nat) (base : List α)
    (hvalid : SuffixSchedule sweeps base) :
    ∀ row ∈ scheduleRows satellite sweeps base,
      row.base.Perm base ∧ row.satellite = satellite ∧
        (row.visible = row.base.length ∨ row.visible = row.base.length - 2) := by
  induction sweeps generalizing base with
  | nil => simp [scheduleRows]
  | cons moves sweeps ih =>
    obtain ⟨⟨stationary, mobile, hbase, _⟩, hsuffix, hrest⟩ := hvalid
    have hend := updateEnd_perm base moves ⟨stationary, mobile, hbase⟩ hsuffix
    intro row hrow
    rcases List.mem_append.mp hrow with hfirst | hlater
    · rw [hbase] at hfirst ⊢
      exact updateRows_inventory satellite stationary mobile moves row hfirst
    · obtain ⟨hperm, hsat, hkind⟩ := ih _ hrest row hlater
      exact ⟨hperm.trans hend, hsat, hkind⟩

theorem scheduleRows_valid (satellite : α) (sweeps : List Nat) (base : List α)
    (hvalid : SuffixSchedule sweeps base) (hnodup : base.Nodup)
    (hfresh : satellite ∉ base) (hlen : 3 ≤ base.length) :
    ∀ row ∈ scheduleRows satellite sweeps base, row.Valid := by
  intro row hrow
  obtain ⟨hperm, hsat, hkind⟩ := scheduleRows_inventory satellite sweeps base hvalid row hrow
  have hrowlen := hperm.length_eq
  refine ⟨hperm.nodup_iff.mpr hnodup, ?_, ?_, ?_⟩
  · rw [hsat]
    exact fun hmem => hfresh (hperm.mem_iff.mp hmem)
  · rcases hkind with hfull | hshort <;> omega
  · rcases hkind with hfull | hshort <;> omega

/-- The exact charge counts actual short occurrences in the constructed list. -/
theorem scheduleRows_charge (satellite : α) (sweeps : List Nat) (base : List α)
    (hvalid : SuffixSchedule sweeps base) (hlen : 2 ≤ base.length) :
    ((scheduleRows satellite sweeps base).map Row.charge).sum = 2 * sweeps.length := by
  induction sweeps generalizing base with
  | nil => simp [scheduleRows]
  | cons moves sweeps ih =>
    obtain ⟨⟨stationary, mobile, hbase, _⟩, hsuffix, hrest⟩ := hvalid
    have hend := updateEnd_perm base moves ⟨stationary, mobile, hbase⟩ hsuffix
    have hnextlen : 2 ≤ (updateEnd moves base).length := by rw [hend.length_eq]; exact hlen
    have hfirst : ((updateRows satellite moves base).map Row.charge).sum = 2 := by
      rw [hbase] at hlen ⊢
      exact updateRows_charge satellite stationary mobile moves hlen
    change (((updateRows satellite moves base ++
      scheduleRows satellite sweeps (updateEnd moves base)).map Row.charge).sum) = _
    rw [List.map_append, List.sum_append, hfirst, ih _ hrest hnextlen]
    simp [Nat.mul_add, Nat.add_comm]

end CoefficientTwoPrecision.RowValidity

#print axioms CoefficientTwoPrecision.RowValidity.scheduleEnd_perm
#print axioms CoefficientTwoPrecision.RowValidity.scheduleRows_inventory
#print axioms CoefficientTwoPrecision.RowValidity.scheduleRows_valid
#print axioms CoefficientTwoPrecision.RowValidity.scheduleRows_charge
