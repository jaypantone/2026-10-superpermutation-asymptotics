import Quantitative.StationaryCircle

/-!
# Alphabet inventory and updates of the concrete stationary renderer

Distinct background and resident labels from disjoint alphabets make the
rendered word nodup. Its exact inventory is every background and resident
label once, so its length is `M + k`.

Moving one target to an unoccupied cut changes exactly two rendered blocks.
This file treats an arbitrary unoccupied destination. Identifying the
destination with the cyclic successor cut, and comparing the resulting
rotated renderer with the literal short move across the seam, is a further
obligation; it is not assumed as part of a structure here.
-/

namespace CoefficientTwoPrecision.StationaryUpdate

open StationaryCircle

variable {M k : Nat} {α : Type}

theorem mem_controlsAt (cuts : Fin k → Fin M) (cut : Fin M) (j : Fin k) :
    j ∈ controlsAt cuts cut ↔ cuts j = cut := by
  simp [controlsAt, List.mem_finRange]

theorem mem_block (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (cut : Fin M) (symbol : α) :
    symbol ∈ block background resident cuts cut ↔
      (∃ j, cuts j = cut ∧ resident j = symbol) ∨ symbol = background cut := by
  simp [block, mem_controlsAt]

theorem mem_render (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (symbol : α) :
    symbol ∈ render background resident cuts ↔
      (∃ i, background i = symbol) ∨ (∃ j, resident j = symbol) := by
  constructor
  · intro h
    obtain ⟨cut, _, hcut⟩ := List.mem_flatMap.mp h
    rcases (mem_block background resident cuts cut symbol).mp hcut with
      ⟨j, _, hj⟩ | hbg
    · exact Or.inr ⟨j, hj⟩
    · exact Or.inl ⟨cut, hbg.symm⟩
  · rintro (⟨cut, rfl⟩ | ⟨j, rfl⟩)
    · apply List.mem_flatMap.mpr
      exact ⟨cut, List.mem_finRange cut,
        (mem_block background resident cuts cut _).mpr (Or.inr rfl)⟩
    · apply List.mem_flatMap.mpr
      exact ⟨cuts j, List.mem_finRange (cuts j),
        (mem_block background resident cuts (cuts j) _).mpr (Or.inl ⟨j, rfl, rfl⟩)⟩

theorem block_nodup (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hresident : Function.Injective resident)
    (hcross : ∀ j i, resident j ≠ background i) (cut : Fin M) :
    (block background resident cuts cut).Nodup := by
  have hcontrols : (controlsAt cuts cut).Nodup :=
    List.Nodup.filter _ (List.nodup_finRange k)
  have hlabels : ((controlsAt cuts cut).map resident).Nodup := hcontrols.map hresident
  have hfresh : background cut ∉ (controlsAt cuts cut).map resident := by
    intro h
    obtain ⟨j, _, hj⟩ := List.mem_map.mp h
    exact hcross j cut hj
  simpa [block, List.concat_eq_append] using
    (List.nodup_concat ((controlsAt cuts cut).map resident) (background cut)).mpr
      ⟨hfresh, hlabels⟩

theorem blocks_disjoint (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hbackground : Function.Injective background)
    (hresident : Function.Injective resident) (hcross : ∀ j i, resident j ≠ background i)
    (first second : Fin M) (hne : first ≠ second) :
    List.Disjoint (block background resident cuts first) (block background resident cuts second) := by
  intro symbol hfirst hsecond
  rcases (mem_block background resident cuts first symbol).mp hfirst with
    ⟨i, hci, hri⟩ | hbi
  · rcases (mem_block background resident cuts second symbol).mp hsecond with
      ⟨j, hcj, hrj⟩ | hbj
    · have hij : i = j := hresident (hri.trans hrj.symm)
      apply hne
      exact hci.symm.trans ((congrArg cuts hij).trans hcj)
    · exact hcross i second (hri.trans hbj)
  · rcases (mem_block background resident cuts second symbol).mp hsecond with
      ⟨j, _, hrj⟩ | hbj
    · exact hcross j first (hrj.trans hbi)
    · exact hne (hbackground (hbi.symm.trans hbj))

theorem render_nodup (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hbackground : Function.Injective background)
    (hresident : Function.Injective resident) (hcross : ∀ j i, resident j ≠ background i) :
    (render background resident cuts).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun cut _ => block_nodup background resident cuts hresident hcross cut, ?_⟩
  exact (List.nodup_finRange M).imp
    (fun {first second} hne => blocks_disjoint background resident cuts
      hbackground hresident hcross first second hne)

theorem render_inventory (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hbackground : Function.Injective background)
    (hresident : Function.Injective resident) (hcross : ∀ j i, resident j ≠ background i) :
    (render background resident cuts).Perm
      ((List.finRange M).map background ++ (List.finRange k).map resident) := by
  have hcanonical :
      ((List.finRange M).map background ++ (List.finRange k).map resident).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨(List.nodup_finRange M).map hbackground,
      (List.nodup_finRange k).map hresident, ?_⟩
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    exact hcross j i hxy.symm
  apply (List.perm_ext_iff_of_nodup
    (render_nodup background resident cuts hbackground hresident hcross) hcanonical).mpr
  intro symbol
  rw [mem_render]
  simp [List.mem_finRange]

theorem render_length (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hbackground : Function.Injective background)
    (hresident : Function.Injective resident) (hcross : ∀ j i, resident j ≠ background i) :
    (render background resident cuts).length = M + k := by
  have h := (render_inventory background resident cuts hbackground hresident hcross).length_eq
  simpa using h

theorem base_nodup (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hbackground : Function.Injective background)
    (hresident : Function.Injective resident) (hcross : ∀ j i, resident j ≠ background i)
    (mobile : α) (hmb : ∀ i, background i ≠ mobile) (hmr : ∀ j, resident j ≠ mobile) :
    (render background resident cuts ++ [mobile]).Nodup := by
  have hfresh : mobile ∉ render background resident cuts := by
    intro h
    rcases (mem_render background resident cuts mobile).mp h with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact hmb i hi
    · exact hmr j hj
  simpa [List.concat_eq_append] using
    (List.nodup_concat (render background resident cuts) mobile).mpr
      ⟨hfresh, render_nodup background resident cuts hbackground hresident hcross⟩

def moveCut (cuts : Fin k → Fin M) (target : Fin k) (destination : Fin M) : Fin k → Fin M :=
  fun j => if j = target then destination else cuts j

def moveResident (resident : Fin k → α) (target : Fin k) (mobile : α) : Fin k → α :=
  fun j => if j = target then mobile else resident j

theorem moveCut_injective (cuts : Fin k → Fin M) (hcuts : Function.Injective cuts)
    (target : Fin k) (destination : Fin M) (hfree : ∀ j, cuts j ≠ destination) :
    Function.Injective (moveCut cuts target destination) := by
  intro i j hij
  by_cases hi : i = target
  · subst i
    by_cases hj : j = target
    · exact hj.symm
    · simp only [moveCut, if_pos rfl, if_neg hj] at hij
      exact False.elim (hfree j hij.symm)
  · by_cases hj : j = target
    · subst j
      simp only [moveCut, if_neg hi, if_pos rfl] at hij
      exact False.elim (hfree i hij)
    · simp only [moveCut, if_neg hi, if_neg hj] at hij
      exact hcuts hij

theorem moved_old_block (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : Function.Injective cuts)
    (target : Fin k) (destination : Fin M) (mobile : α)
    (hfree : ∀ j, cuts j ≠ destination) :
    block background (moveResident resident target mobile)
      (moveCut cuts target destination) (cuts target) = [background (cuts target)] := by
  have hempty : ∀ j, moveCut cuts target destination j ≠ cuts target := by
    intro j
    by_cases hj : j = target
    · subst j
      simpa [moveCut] using (hfree target).symm
    · simp only [moveCut, if_neg hj]
      exact fun h => hj (hcuts h)
  simp [block, controlsAt_empty _ _ hempty]

theorem moved_destination_block (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : Function.Injective cuts)
    (target : Fin k) (destination : Fin M) (mobile : α)
    (hfree : ∀ j, cuts j ≠ destination) :
    block background (moveResident resident target mobile)
      (moveCut cuts target destination) destination = [mobile, background destination] := by
  have h := target_block background (moveResident resident target mobile)
    (moveCut cuts target destination) (moveCut_injective cuts hcuts target destination hfree) target
  simpa [moveCut, moveResident] using h

theorem moved_other_block (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (target : Fin k) (destination cut : Fin M) (mobile : α)
    (hold : cuts target ≠ cut) (hnew : destination ≠ cut) :
    block background (moveResident resident target mobile)
      (moveCut cuts target destination) cut = block background resident cuts cut := by
  have hpred : (fun j => decide (moveCut cuts target destination j = cut)) =
      (fun j => decide (cuts j = cut)) := by
    funext j
    by_cases hj : j = target
    · subst j
      simp [moveCut, hold, hnew]
    · simp [moveCut, hj]
  have hat : controlsAt (moveCut cuts target destination) cut = controlsAt cuts cut := by
    unfold controlsAt
    rw [hpred]
  unfold block
  rw [hat]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hcut : cuts j = cut := (mem_controlsAt cuts cut j).mp hj
  have hne : j ≠ target := by
    intro heq
    subst j
    exact hold hcut
  simp [moveResident, hne]

/-- Exact finite-list change of the whole renderer. The destination may
be any currently unoccupied cut; cyclic succession is imposed later. -/
theorem render_move (background : Fin M → α) (resident : Fin k → α)
    (cuts : Fin k → Fin M) (hcuts : Function.Injective cuts)
    (target : Fin k) (destination : Fin M) (mobile : α)
    (hfree : ∀ j, cuts j ≠ destination) :
    render background (moveResident resident target mobile) (moveCut cuts target destination) =
      (List.finRange M).flatMap (fun cut =>
        if cut = cuts target then [background cut]
        else if cut = destination then [mobile, background cut]
        else block background resident cuts cut) := by
  unfold render
  congr 1
  funext cut
  by_cases hold : cut = cuts target
  · subst cut
    simp only [if_pos rfl]
    exact moved_old_block background resident cuts hcuts target destination mobile hfree
  · by_cases hnew : cut = destination
    · subst cut
      simp only [if_neg hold, if_pos rfl]
      exact moved_destination_block background resident cuts hcuts target destination mobile hfree
    · simp only [if_neg hold, if_neg hnew]
      exact moved_other_block background resident cuts target destination cut mobile
        (Ne.symm hold) (Ne.symm hnew)

end CoefficientTwoPrecision.StationaryUpdate

#print axioms CoefficientTwoPrecision.StationaryUpdate.render_nodup
#print axioms CoefficientTwoPrecision.StationaryUpdate.render_inventory
#print axioms CoefficientTwoPrecision.StationaryUpdate.render_length
#print axioms CoefficientTwoPrecision.StationaryUpdate.base_nodup
#print axioms CoefficientTwoPrecision.StationaryUpdate.moveCut_injective
#print axioms CoefficientTwoPrecision.StationaryUpdate.render_move
