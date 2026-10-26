import Quantitative.RowValidity
import Quantitative.StationaryUpdate

/-!
# Recovering a stationary cut from a cyclic source base

For a chosen stationary control, delete every other control while retaining
all background symbols. Its next symbol in this projected circle is the
background symbol at its cut. The projection is invariant under cyclic
rotation, so equal cyclic source bases give equal cuts for every control
that is stationary in both. The mobile may occupy any insertion gap.
-/

namespace CoefficientTwoPrecision.CutExtraction

open LiteralState StationaryCircle StationaryUpdate

variable {M k : Nat} {α : Type} [DecidableEq α]

def retain (backgroundTest : α → Bool) (tracked : α) (symbol : α) : Bool :=
  backgroundTest symbol || decide (symbol = tracked)

def projection (backgroundTest : α → Bool) (tracked : α) (base : List α) : List α :=
  base.filter (retain backgroundTest tracked)

/-- Filtering symbols commutes with cyclic equivalence. -/
theorem filter_rotate (base : List α) (keep : α → Bool) (n : Nat) :
    (base.filter keep).IsRotated ((base.rotate n).filter keep) := by
  have hsource : base.filter keep =
      (base.take (n % base.length)).filter keep ++ (base.drop (n % base.length)).filter keep := by
    rw [← List.filter_append, List.take_append_drop]
  rw [hsource, List.rotate_eq_drop_append_take_mod, List.filter_append]
  exact List.isRotated_append

theorem filter_isRotated (first second : List α) (keep : α → Bool)
    (h : first.IsRotated second) : (first.filter keep).IsRotated (second.filter keep) := by
  obtain ⟨n, rfl⟩ := h
  exact filter_rotate first keep n

/-- The next retained symbol after a control is its background cut. -/
def AtCut (backgroundTest : α → Bool) (base : List α) (tracked background : α) : Prop :=
  ∃ rest : List α, (projection backgroundTest tracked base).IsRotated (tracked :: background :: rest)

theorem atCut_of_isRotated (backgroundTest : α → Bool) (first second : List α)
    (tracked background : α) (h : first.IsRotated second)
    (hcut : AtCut backgroundTest first tracked background) :
    AtCut backgroundTest second tracked background := by
  obtain ⟨rest, hrest⟩ := hcut
  exact ⟨rest, (filter_isRotated first second (retain backgroundTest tracked) h).symm.trans hrest⟩

/-- A nodup cyclic list has a unique rotation with a prescribed first symbol. -/
theorem isRotated_same_head_eq (first second : List α) (hnd : first.Nodup)
    (hrot : first.IsRotated second) (hhead : first.head? = second.head?) : first = second := by
  by_cases hnil : first = []
  · subst first
    simpa using List.isRotated_nil_iff'.mp hrot
  obtain ⟨n, hn⟩ := hrot
  have hheads : (first.rotateLeft 0).head? = (first.rotateLeft n).head? := by
    simpa only [List.rotateLeft_zero, LiteralState.rotateLeft_eq_rotate, List.rotate_zero, hn] using hhead
  have heq := rotateLeft_eq_of_head_eq first hnd hnil 0 n hheads
  simpa only [List.rotateLeft_zero, LiteralState.rotateLeft_eq_rotate, List.rotate_zero, hn] using heq

theorem atCut_unique (backgroundTest : α → Bool) (base : List α) (hnd : base.Nodup)
    (tracked first second : α) (hfirst : AtCut backgroundTest base tracked first)
    (hsecond : AtCut backgroundTest base tracked second) : first = second := by
  obtain ⟨rest, hrest⟩ := hfirst
  obtain ⟨rest', hrest'⟩ := hsecond
  have hproj : (projection backgroundTest tracked base).Nodup :=
    List.Nodup.filter _ hnd
  have hndfirst : (tracked :: first :: rest).Nodup := hrest.nodup_iff.mp hproj
  have heq := isRotated_same_head_eq (tracked :: first :: rest) (tracked :: second :: rest')
    hndfirst (hrest.symm.trans hrest') rfl
  exact (List.cons.inj (List.cons.inj heq).2).1

theorem projected_residents (backgroundTest : α → Bool) (resident : Fin k → α)
    (hresident : Function.Injective resident) (hcontrols : ∀ j, backgroundTest (resident j) = false)
    (cuts : Fin k → Fin M) (tracked : Fin k) (cut : Fin M) :
    (((controlsAt cuts cut).map resident).filter (retain backgroundTest (resident tracked))) =
      if cuts tracked = cut then [resident tracked] else [] := by
  have hfilter : ∀ (slots : List (Fin k)),
      (slots.map resident).filter (retain backgroundTest (resident tracked)) =
        (slots.filter (fun j => decide (j = tracked))).map resident := by
    intro slots
    induction slots with
    | nil => rfl
    | cons j slots ih =>
      simp only [List.map_cons, List.filter_cons, retain, hcontrols, Bool.false_or,
        hresident.eq_iff, ih]
      split <;> simp_all
  rw [hfilter]
  have hsingle : (controlsAt cuts cut).filter (fun j => decide (j = tracked)) =
      if cuts tracked = cut then [tracked] else [] := by
    rw [List.filter_eq]
    by_cases hcut : cuts tracked = cut
    · have hc : (controlsAt cuts cut).count tracked = 1 :=
        List.count_eq_one_of_mem (List.Nodup.filter _ (List.nodup_finRange k))
          ((mem_controlsAt cuts cut tracked).mpr hcut)
      simp [hcut, hc]
    · have hnot : tracked ∉ controlsAt cuts cut := by simpa only [mem_controlsAt] using hcut
      simp [hcut, List.count_eq_zero.mpr hnot]
  rw [hsingle]
  split <;> simp

theorem projected_block (backgroundTest : α → Bool) (background : Fin M → α)
    (resident : Fin k → α) (hresident : Function.Injective resident)
    (hbackground : ∀ i, backgroundTest (background i) = true)
    (hcontrols : ∀ j, backgroundTest (resident j) = false)
    (cuts : Fin k → Fin M) (tracked : Fin k) (cut : Fin M) :
    (block background resident cuts cut).filter (retain backgroundTest (resident tracked)) =
      (if cuts tracked = cut then [resident tracked] else []) ++ [background cut] := by
  simp only [block, List.filter_append,
    projected_residents backgroundTest resident hresident hcontrols cuts tracked cut,
    List.filter_cons, List.filter_nil, retain, hbackground, Bool.true_or, Bool.true_eq,
    ↓reduceIte]

/-- The projected rendered circle displays each stationary control directly
before the background symbol at its cut. -/
theorem render_atCut (backgroundTest : α → Bool) (background : Fin M → α)
    (resident : Fin k → α) (hresident : Function.Injective resident)
    (hbackground : ∀ i, backgroundTest (background i) = true)
    (hcontrols : ∀ j, backgroundTest (resident j) = false)
    (cuts : Fin k → Fin M) (tracked : Fin k) :
    AtCut backgroundTest (render background resident cuts) (resident tracked)
      (background (cuts tracked)) := by
  obtain ⟨before, after, hsplit, _⟩ := List.eq_append_cons_of_mem (List.mem_finRange (cuts tracked))
  have hnodup : (before ++ cuts tracked :: after).Nodup := by
    rw [← hsplit]
    exact List.nodup_finRange M
  have hnotbefore : cuts tracked ∉ before := by
    intro hmem
    exact (List.nodup_append.mp hnodup).2.2 _ hmem _ (by simp) rfl
  have hnotafter : cuts tracked ∉ after :=
    (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1
  have hpart (order : List (Fin M)) (hnot : cuts tracked ∉ order) :
      (order.flatMap (block background resident cuts)).filter (retain backgroundTest (resident tracked)) =
        order.map background := by
    induction order with
    | nil => rfl
    | cons cut order ih =>
      have hne : cuts tracked ≠ cut := fun h => hnot (by simp [h])
      have htail : cuts tracked ∉ order := fun h => hnot (by simp [h])
      simp only [List.flatMap_cons, List.filter_append,
        projected_block backgroundTest background resident hresident hbackground hcontrols cuts tracked cut,
        if_neg hne, List.nil_append, List.singleton_append, List.map_cons, ih htail]
  refine ⟨after.map background ++ before.map background, ?_⟩
  have hprojection : projection backgroundTest (resident tracked) (render background resident cuts) =
      before.map background ++ [resident tracked, background (cuts tracked)] ++ after.map background := by
    unfold projection render
    rw [hsplit, List.flatMap_append, List.flatMap_cons, List.filter_append, List.filter_append]
    rw [hpart before hnotbefore, hpart after hnotafter,
      projected_block backgroundTest background resident hresident hbackground hcontrols cuts tracked (cuts tracked)]
    simp
  rw [hprojection]
  have h := List.isRotated_append (l := before.map background)
    (l' := [resident tracked, background (cuts tracked)] ++ after.map background)
  simpa [List.append_assoc] using h

/-- Inserting an untracked mobile at any gap does not change the cut
extracted for a stationary control. -/
theorem mobile_base_atCut (backgroundTest : α → Bool) (stationary : List α)
    (mobile tracked background : α) (hcontrol : backgroundTest mobile = false)
    (hne : mobile ≠ tracked) (gap : Nat)
    (hcut : AtCut backgroundTest stationary tracked background) :
    AtCut backgroundTest (stationary.rotateLeft gap ++ [mobile]) tracked background := by
  obtain ⟨rest, hrest⟩ := hcut
  refine ⟨rest, ?_⟩
  have hproj : projection backgroundTest tracked (stationary.rotateLeft gap ++ [mobile]) =
      (stationary.rotate gap).filter (retain backgroundTest tracked) := by
    simp [projection, List.filter_append, List.filter_cons, retain, hcontrol, hne,
      LiteralState.rotateLeft_eq_rotate]
  rw [hproj]
  exact (filter_rotate stationary (retain backgroundTest tracked) gap).symm.trans hrest

/-- Equal cyclic source bases force equal background cuts for a control
that is stationary in both. The two mobile symbols may differ. -/
theorem common_stationary_cut (backgroundTest : α → Bool) (first second : List α)
    (hnd : first.Nodup) (hcyclic : first.IsRotated second)
    (tracked leftCut rightCut : α)
    (hleft : AtCut backgroundTest first tracked leftCut)
    (hright : AtCut backgroundTest second tracked rightCut) : leftCut = rightCut := by
  apply atCut_unique backgroundTest first hnd tracked leftCut rightCut hleft
  exact atCut_of_isRotated backgroundTest second first tracked rightCut hcyclic.symm hright

end CoefficientTwoPrecision.CutExtraction

#print axioms CoefficientTwoPrecision.CutExtraction.render_atCut
#print axioms CoefficientTwoPrecision.CutExtraction.mobile_base_atCut
#print axioms CoefficientTwoPrecision.CutExtraction.common_stationary_cut
