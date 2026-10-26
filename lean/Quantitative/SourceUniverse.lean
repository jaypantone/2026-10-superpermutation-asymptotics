import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Actual finite lists of cyclic insertion representatives

Controls are listed newest first. Thus `sourceUniverse (v :: controls) d` adds
`v` after the controls already in `sourceUniverse controls d`. This convention
matches the ordinary alphabet `controls ++ d` used below.

The module constructs the lists, proves their exact lengths, and proves
that no two entries have the same cyclic class when the full alphabet is
nodup. It does not assume an injection of the constructed lists. The later
literal source-to-insertion-chain bridge is a separate obligation. The
finite list is proved exhaustive for arbitrary cyclic insertion chains.

The proof that a fresh last letter determines a cyclic representative uses
the same elementary last-position argument as the supplied core theorem
`Transport.append_satellite_eq_of_cyclicEq`, here over Mathlib's general
`List.IsRotated`. No source file in the supplied baseline is changed.
-/

namespace CoefficientTwoPrecision.SourceUniverse

variable {α : Type*}

/-- The two list-rotation definitions agree, including lengths zero and one. -/
theorem rotateLeft_eq_rotate (b : List α) (j : ℕ) : b.rotateLeft j = b.rotate j := by
  rw [List.rotate_eq_drop_append_take_mod]
  by_cases h : b.length ≤ 1
  · cases b with
    | nil => simp [List.rotateLeft]
    | cons a rest =>
      have hrest : rest = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at h
        omega
      subst rest
      simp [List.rotateLeft, Nat.mod_one]
  · simp [List.rotateLeft, h]

/-- Insert a fresh letter in every cyclic gap, with that letter displayed last. -/
def insertions (v : α) (b : List α) : List (List α) :=
  (List.range b.length).map (fun j => b.rotate j ++ [v])

@[simp] theorem insertions_length (v : α) (b : List α) :
    (insertions v b).length = b.length := by
  simp [insertions]

theorem mem_insertions {v : α} {b t : List α} :
    t ∈ insertions v b ↔ ∃ j < b.length, t = b.rotate j ++ [v] := by
  simp only [insertions, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩

theorem insertion_perm {v : α} {b t : List α} (ht : t ∈ insertions v b) :
    t.Perm (v :: b) := by
  obtain ⟨j, _, rfl⟩ := mem_insertions.mp ht
  exact List.perm_append_comm.trans ((List.rotate_perm b j).cons v)

/-- Iterated finite insertion, with the newest control at the head. -/
def sourceUniverse : List α → List α → List (List α)
  | [], d => [d]
  | v :: controls, d => (sourceUniverse controls d).flatMap (insertions v)

/-- The rising product `m (m+1) ... (m+W-1)`. -/
def risingCount (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | W + 1 => risingCount m W * (m + W)

theorem universe_perm (controls d : List α) {b : List α}
    (hb : b ∈ sourceUniverse controls d) : b.Perm (controls ++ d) := by
  induction controls generalizing b with
  | nil =>
    have hbd : b = d := by simpa [sourceUniverse] using hb
    subst b
    exact List.Perm.refl _
  | cons v controls ih =>
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
    exact (insertion_perm hb).trans ((ih ha).cons v)

theorem universe_entry_length (controls d : List α) {b : List α}
    (hb : b ∈ sourceUniverse controls d) : b.length = d.length + controls.length := by
  have h := (universe_perm controls d hb).length_eq
  simpa [List.length_append, Nat.add_comm] using h

private theorem length_flatMap_uniform {β : Type*} (xs : List α) (f : α → List β)
    (q : ℕ) (hf : ∀ x ∈ xs, (f x).length = q) :
    (xs.flatMap f).length = xs.length * q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, hf x (by simp),
      ih (fun y hy => hf y (by simp [hy])), List.length_cons, Nat.succ_mul]
    exact Nat.add_comm _ _

/-- An exact length formula for the actual recursively constructed list. -/
theorem universe_length (controls d : List α) :
    (sourceUniverse controls d).length = risingCount d.length controls.length := by
  induction controls with
  | nil => simp [sourceUniverse, risingCount]
  | cons v controls ih =>
    change ((sourceUniverse controls d).flatMap (insertions v)).length = _
    rw [length_flatMap_uniform _ _ (d.length + controls.length)
      (fun b hb => by rw [insertions_length, universe_entry_length controls d hb]), ih]
    rfl

/-- The product agrees with the relevant quotient of factorials without division. -/
theorem risingCount_mul_factorial (m W : ℕ) (hm : 0 < m) :
    risingCount m W * (m - 1).factorial = (m + W - 1).factorial := by
  induction W with
  | zero => simp [risingCount]
  | succ W ih =>
    calc
      risingCount m (W + 1) * (m - 1).factorial
          = (m + W) * (risingCount m W * (m - 1).factorial) := by
              simp only [risingCount]
              ac_rfl
      _ = (m + W) * (m + W - 1).factorial := by rw [ih]
      _ = (m + W).factorial := Nat.mul_factorial_pred (by omega)
      _ = (m + (W + 1) - 1).factorial := by congr 1

/-- Rotating words with the same fresh final letter cannot change their prefix. -/
theorem append_last_eq_of_isRotated {a b : List α} {v : α}
    (hv : v ∉ a) (h : (a ++ [v]).IsRotated (b ++ [v])) : a = b := by
  have hlen : a.length = b.length := by
    have hh := h.perm.length_eq
    simpa using hh
  obtain ⟨j, hj⟩ := h
  let k := j % (a ++ [v]).length
  have hk : k < (a ++ [v]).length := Nat.mod_lt _ (by simp)
  have he : (a ++ [v]).rotate k = b ++ [v] := by
    simpa only [k, List.rotate_mod] using hj
  have hk_le : k ≤ a.length := by simp only [List.length_append, List.length_singleton] at hk; omega
  have hlast : ((a ++ [v]).rotate k)[a.length]? = some v := by
    rw [he]
    simp [hlen]
  have hk0 : k = 0 := by
    by_contra hk0
    have hmod : (a.length + k) % (a ++ [v]).length = k - 1 := by
      simp only [List.length_append, List.length_singleton]
      have heq : a.length + k = (k - 1) + (a.length + 1) := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [List.getElem?_rotate (by simp), hmod,
      List.getElem?_append_left (by omega : k - 1 < a.length)] at hlast
    exact hv (List.mem_of_getElem? hlast)
  have hab : a ++ [v] = b ++ [v] := by simpa only [hk0, List.rotate_zero] using he
  exact List.append_cancel_right hab

/-- Different cyclic insertion gaps of a nodup word give different classes. -/
theorem insertion_class_injective {b : List α} {v : α} (hb : b.Nodup)
    (hv : v ∉ b) {i j : ℕ} (hi : i < b.length) (hj : j < b.length)
    (h : (b.rotate i ++ [v]).IsRotated (b.rotate j ++ [v])) : i = j := by
  have hvi : v ∉ b.rotate i := by simpa using hv
  have he := append_last_eq_of_isRotated hvi h
  have hne : b ≠ [] := by intro he; simp [he] at hi
  have hr := hb.rotate_congr hne i j he
  simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hr

/-- Distinct entries mean distinct cyclic classes, not only distinct words. -/
def CyclicDistinct (xs : List (List α)) : Prop :=
  xs.Pairwise (fun a b => ¬ a.IsRotated b)

theorem insertions_cyclicDistinct {b : List α} {v : α} (hb : b.Nodup)
    (hv : v ∉ b) : CyclicDistinct (insertions v b) := by
  unfold CyclicDistinct insertions
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ List.nodup_range
  intro i j hi hj hij he
  exact hij (insertion_class_injective hb hv (List.mem_range.mp hi) (List.mem_range.mp hj) he)

/-- Extending a list of distinct classes by one fresh letter preserves that property. -/
theorem extend_cyclicDistinct {xs : List (List α)} {v : α}
    (hx : CyclicDistinct xs) (hnd : ∀ b ∈ xs, b.Nodup)
    (hfresh : ∀ b ∈ xs, v ∉ b) : CyclicDistinct (xs.flatMap (insertions v)) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun b hb => insertions_cyclicDistinct (hnd b hb) (hfresh b hb), ?_⟩
  apply List.Pairwise.imp_of_mem _ hx
  intro a b ha hb hab x hx y hy hxy
  obtain ⟨i, _, rfl⟩ := mem_insertions.mp hx
  obtain ⟨j, _, rfl⟩ := mem_insertions.mp hy
  have hv : v ∉ a.rotate i := by simpa using hfresh a ha
  have he := append_last_eq_of_isRotated hv hxy
  have hrot : a.IsRotated (b.rotate j) := ⟨i, he⟩
  exact hab (hrot.trans (List.IsRotated.forall b j))

/-- The finite construction has no repeated cyclic classes on a nodup alphabet. -/
theorem universe_cyclicDistinct (controls d : List α) (hnd : (controls ++ d).Nodup) :
    CyclicDistinct (sourceUniverse controls d) := by
  induction controls with
  | nil => simp [sourceUniverse, CyclicDistinct]
  | cons v controls ih =>
    have hn := List.nodup_cons.mp hnd
    apply extend_cyclicDistinct (ih hn.2)
    · intro b hb
      exact (universe_perm controls d hb).nodup_iff.mpr hn.2
    · intro b hb hv
      exact hn.1 ((universe_perm controls d hb).mem_iff.mp hv)

theorem universe_nodup (controls d : List α) (hnd : (controls ++ d).Nodup) :
    (sourceUniverse controls d).Nodup := by
  apply List.Pairwise.imp _ (universe_cyclicDistinct controls d hnd)
  intro a b hab he
  subst b
  exact hab (List.IsRotated.refl a)

/-- The cyclic classes obtained by successive insertions. Rotation indices in
this relation are unrestricted, and intermediate representatives may be
arbitrary rotations. Controls again appear newest first. -/
def InsertionAbove : List α → List α → List α → Prop
  | [], d, y => d.IsRotated y
  | v :: controls, d, y => ∃ x, InsertionAbove controls d x ∧
      ∃ j : ℕ, (x.rotate j ++ [v]).IsRotated y

theorem insertionAbove_of_mem (controls d : List α) {b : List α}
    (hb : b ∈ sourceUniverse controls d) : InsertionAbove controls d b := by
  induction controls generalizing b with
  | nil =>
    have he : b = d := by simpa [sourceUniverse] using hb
    subst b
    exact List.IsRotated.refl d
  | cons v controls ih =>
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨j, _, rfl⟩ := mem_insertions.mp hb
    exact ⟨a, ih ha, j, List.IsRotated.refl _⟩

theorem insertionAbove_rotate (controls d : List α) {a b : List α}
    (ha : InsertionAbove controls d a) (hab : a.IsRotated b) :
    InsertionAbove controls d b := by
  cases controls with
  | nil => exact ha.trans hab
  | cons v controls =>
    obtain ⟨x, hx, j, hj⟩ := ha
    exact ⟨x, hx, j, hj.trans hab⟩

/-- Every cyclic insertion chain is represented in the actual finite list. -/
theorem universe_covers_insertionAbove (controls d : List α) (hd : 0 < d.length)
    {y : List α} (hy : InsertionAbove controls d y) :
    ∃ b ∈ sourceUniverse controls d, b.IsRotated y := by
  induction controls generalizing y with
  | nil => exact ⟨d, by simp [sourceUniverse], hy⟩
  | cons v controls ih =>
    obtain ⟨x, hx, j, hj⟩ := hy
    obtain ⟨a, ha, hax⟩ := ih hx
    obtain ⟨k, hk⟩ := hax
    let t := (k + j) % a.length
    have hapos : 0 < a.length := by
      rw [universe_entry_length controls d ha]
      omega
    have ht : t < a.length := Nat.mod_lt _ hapos
    have he : a.rotate t = x.rotate j := by
      dsimp [t]
      rw [List.rotate_mod, ← hk, List.rotate_rotate]
    refine ⟨a.rotate t ++ [v], List.mem_flatMap.mpr ⟨a, ha, ?_⟩, ?_⟩
    · exact mem_insertions.mpr ⟨t, ht, rfl⟩
    · rw [he]
      exact hj

/-- Exact enumeration of the cyclic classes of arbitrary insertion chains. -/
theorem insertionAbove_iff_mem (controls d : List α) (hd : 0 < d.length)
    (y : List α) : InsertionAbove controls d y ↔
      ∃ b ∈ sourceUniverse controls d, b.IsRotated y := by
  constructor
  · exact universe_covers_insertionAbove controls d hd
  · rintro ⟨b, hb, hby⟩
    exact insertionAbove_rotate controls d (insertionAbove_of_mem controls d hb) hby

end CoefficientTwoPrecision.SourceUniverse

#print axioms CoefficientTwoPrecision.SourceUniverse.universe_length
#print axioms CoefficientTwoPrecision.SourceUniverse.risingCount_mul_factorial
#print axioms CoefficientTwoPrecision.SourceUniverse.universe_cyclicDistinct

#print axioms CoefficientTwoPrecision.SourceUniverse.insertionAbove_iff_mem
