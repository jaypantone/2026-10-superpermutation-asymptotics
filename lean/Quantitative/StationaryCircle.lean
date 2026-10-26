import Quantitative.LiteralState

/-!
# A concrete stationary circle and existence of a target suffix

For each background cut, list its resident controls and then its background
symbol. Flattening these lists is an actual stationary word. Injective cuts
give exactly one resident at an occupied cut. Every target therefore occurs
immediately before its crossed background symbol, and fewer than one full
circuit of literal F moves reaches the required suffix from any mobile gap.

The next geometric obligations are preservation of this renderer by a
positive S update, nodup from distinct alphabets, robust-cut simplicity,
and containment of the full repaired schedule in the joint catalogue.
-/

namespace CoefficientTwoPrecision.StationaryCircle

open JointStates LiteralState

variable {M k : Nat} {α : Type}

/-- Stationary positions whose current cut is `cut`. -/
def controlsAt (cuts : Fin k → Fin M) (cut : Fin M) : List (Fin k) :=
  (List.finRange k).filter (fun j => decide (cuts j = cut))

/-- The literal symbols at one background cut. -/
def block (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (cut : Fin M) : List α :=
  (controlsAt cuts cut).map resident ++ [background cut]

/-- An actual anchored stationary word, before the mobile is inserted. -/
def render (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) : List α :=
  (List.finRange M).flatMap (block background resident cuts)

theorem controlsAt_target (cuts : Fin k → Fin M) (hinj : Function.Injective cuts)
    (j : Fin k) : controlsAt cuts (cuts j) = [j] := by
  have hpred : (fun i : Fin k => decide (cuts i = cuts j)) =
      (fun i : Fin k => decide (i = j)) := by
    funext i
    simp only [hinj.eq_iff]
  unfold controlsAt
  rw [hpred, List.filter_eq]
  have hcount : (List.finRange k).count j = 1 :=
    List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange j)
  simp [hcount]

theorem controlsAt_empty (cuts : Fin k → Fin M) (cut : Fin M)
    (hempty : ∀ j, cuts j ≠ cut) : controlsAt cuts cut = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro j _
  simpa using hempty j

theorem target_block (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hinj : Function.Injective cuts) (j : Fin k) :
    block background resident cuts (cuts j) = [resident j, background (cuts j)] := by
  simp [block, controlsAt_target cuts hinj j]

/-- A target resident and its crossed background symbol are adjacent in
the concrete stationary word. -/
theorem target_decomposition (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hinj : Function.Injective cuts) (j : Fin k) :
    ∃ before after : List α,
      render background resident cuts =
        before ++ [resident j, background (cuts j)] ++ after := by
  obtain ⟨before, after, hsplit, _⟩ :=
    List.eq_append_cons_of_mem (List.mem_finRange (cuts j))
  refine ⟨before.flatMap (block background resident cuts),
    after.flatMap (block background resident cuts), ?_⟩
  unfold render
  rw [hsplit, List.flatMap_append, List.flatMap_cons, target_block _ _ _ hinj j]
  simp only [List.append_assoc]

theorem rotate_to_suffix (before after : List α) (resident crossed : α) :
    (before ++ [resident, crossed] ++ after).rotateLeft (before.length + 2) =
      (after ++ before) ++ [resident, crossed] := by
  rw [rotateLeft_eq_rotate]
  simpa [List.length_append, List.append_assoc] using
    List.rotate_append_length_eq (before ++ [resident, crossed]) after

/-- Any desired rotation is reached from any initial rotation in fewer
than one full circuit. This is finite modular arithmetic, with no search. -/
theorem rotation_reachable (stationary : List α) (hlen : 0 < stationary.length)
    (gap desired : Nat) :
    ∃ moves < stationary.length,
      (stationary.rotateLeft gap).rotateLeft moves = stationary.rotateLeft desired := by
  let moves := (stationary.length - gap % stationary.length + desired) % stationary.length
  have hgap : gap % stationary.length < stationary.length := Nat.mod_lt gap hlen
  have hmod : (gap + moves) % stationary.length = desired % stationary.length := by
    calc
      (gap + moves) % stationary.length =
          (gap + (stationary.length - gap % stationary.length + desired)) %
            stationary.length := by simp only [moves, Nat.add_mod_mod]
      _ = (gap % stationary.length +
          (stationary.length - gap % stationary.length + desired)) %
            stationary.length := (Nat.mod_add_mod _ _ _).symm
      _ = (stationary.length + desired) % stationary.length := by
        congr 1
        omega
      _ = desired % stationary.length := Nat.add_mod_left _ _
  refine ⟨moves, Nat.mod_lt _ hlen, ?_⟩
  rw [rotateLeft_add, rotateLeft_eq_rotate, rotateLeft_eq_rotate]
  rw [← List.rotate_mod stationary (gap + moves), hmod, List.rotate_mod]

/-- The renderer supplies the actual literal suffix needed for every
positive update, starting from an arbitrary mobile insertion gap. -/
theorem target_suffix_exists (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hinj : Function.Injective cuts)
    (j : Fin k) (mobile : α) (gap : Nat) :
    ∃ moves < (render background resident cuts).length, ∃ pre : List α,
      fullIterate moves ((render background resident cuts).rotateLeft gap ++ [mobile]) =
        pre ++ [resident j, background (cuts j), mobile] := by
  obtain ⟨before, after, hsplit⟩ := target_decomposition background resident cuts hinj j
  have hlen : 0 < (render background resident cuts).length := by
    rw [hsplit]
    simp
  obtain ⟨moves, hmoves, hreach⟩ :=
    rotation_reachable (render background resident cuts) hlen gap (before.length + 2)
  refine ⟨moves, hmoves, after ++ before, ?_⟩
  rw [fullIterate_formula, hreach, hsplit, rotate_to_suffix]
  simp [List.append_assoc]

/-- Combining the actual target suffix with the literal short operation
exchanges the named resident and mobile at that occurrence. -/
theorem positive_update_exists (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hinj : Function.Injective cuts)
    (j : Fin k) (mobile : α) (gap : Nat) :
    ∃ moves < (render background resident cuts).length, ∃ pre : List α,
      fullIterate moves ((render background resident cuts).rotateLeft gap ++ [mobile]) =
        pre ++ [resident j, background (cuts j), mobile] ∧
      shortStep (fullIterate moves
        ((render background resident cuts).rotateLeft gap ++ [mobile])) =
        mobile :: (pre ++ [background (cuts j), resident j]) := by
  obtain ⟨moves, hmoves, pre, hpre⟩ :=
    target_suffix_exists background resident cuts hinj j mobile gap
  refine ⟨moves, hmoves, pre, hpre, ?_⟩
  rw [hpre, shortStep_suffix]

/-- Deleting all resident controls recovers the prescribed background word
exactly in its anchored order. -/
theorem delete_residents (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (keep : α → Bool)
    (hbackground : ∀ i, keep (background i) = true)
    (hresident : ∀ j, keep (resident j) = false) :
    (render background resident cuts).filter keep = (List.finRange M).map background := by
  have hcontrols (cut : Fin M) :
      ((controlsAt cuts cut).map resident).filter keep = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro symbol hsymbol
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hsymbol
    simp [hresident j]
  have hblock (cut : Fin M) :
      (block background resident cuts cut).filter keep = [background cut] := by
    simp [block, List.filter_append, hcontrols, List.filter_cons, hbackground]
  have hfun : (fun cut => (block background resident cuts cut).filter keep) =
      (fun cut => [background cut]) := by
    funext cut
    exact hblock cut
  simp only [render, List.filter_flatMap, hfun]
  have hmap (cuts : List (Fin M)) :
      (cuts.flatMap fun cut => [background cut]) = cuts.map background := by
    induction cuts with
    | nil => rfl
    | cons cut cuts ih => simp [ih]
  exact hmap _

end CoefficientTwoPrecision.StationaryCircle

#print axioms CoefficientTwoPrecision.StationaryCircle.controlsAt_target
#print axioms CoefficientTwoPrecision.StationaryCircle.target_decomposition
#print axioms CoefficientTwoPrecision.StationaryCircle.target_suffix_exists
#print axioms CoefficientTwoPrecision.StationaryCircle.positive_update_exists
#print axioms CoefficientTwoPrecision.StationaryCircle.delete_residents
