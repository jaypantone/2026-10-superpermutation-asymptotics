import Quantitative.TraceRowBounds
import Quantitative.CyclicRepairSchedule

/-!
# The actual row-count perturbation of the compiled repair program

We split the same bounded trace into its untouched normal segments and its
parking-plus-cleanup segments. A clean segment has its exact translated
normal count. Each changed segment and its normal replacement both have
counts between zero and the common batch bound. Their difference therefore
uses one batch bound, not the sum of two bounds. The recursion follows the
actual compiler and counts every cleanup batch as changed.
-/

namespace CoefficientTwoPrecision.RepairRowCounts

open SuperpermutationUpperBound PositiveParking LiteralState StationaryCircle
open LiteralSchedule PositiveSchedule TargetTrace TraceComposition TraceSteps
open RobustMatching BatchSafety ActualCyclicMatching NormalSegments TraceRowBounds
open MacroCatalogue FiniteProgram RepairIntervals RepairGroups RepairProgram CyclicRepairSchedule

variable {M k : ℕ} {α Label : Type}

def normalRows (M k : ℕ) : ℕ := (k - 1) * M + k * (k + 1) + 1

def batchBound (M k : ℕ) : ℕ := k * (M + k)

private theorem combine_errors (a b c E changed rest normal bound : ℕ)
    (hchanged : changed ≤ b * bound) (hnormal : normal ≤ bound)
    (hrest : |(rest : ℚ) - ((c * normal : ℕ) : ℚ)| ≤ ((E * bound : ℕ) : ℚ)) :
    |((a * normal + changed + rest : ℕ) : ℚ) - (((a + b + c) * normal : ℕ) : ℚ)| ≤
      (((b + E) * bound : ℕ) : ℚ) := by
  have hc : (changed : ℚ) ≤ ((b * bound : ℕ) : ℚ) := by exact_mod_cast hchanged
  have hn : ((b * normal : ℕ) : ℚ) ≤ ((b * bound : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_le_mul_left b hnormal
  have hc0 : (0 : ℚ) ≤ changed := Nat.cast_nonneg _
  have hn0 : (0 : ℚ) ≤ ((b * normal : ℕ) : ℚ) := Nat.cast_nonneg _
  have hlocal : |(changed : ℚ) - ((b * normal : ℕ) : ℚ)| ≤ ((b * bound : ℕ) : ℚ) := by
    apply abs_le.mpr
    constructor <;> linarith only [hc, hn, hc0, hn0]
  calc
    |((a * normal + changed + rest : ℕ) : ℚ) - (((a + b + c) * normal : ℕ) : ℚ)| =
        |((changed : ℚ) - ((b * normal : ℕ) : ℚ)) +
          ((rest : ℚ) - ((c * normal : ℕ) : ℚ))| := by
      congr 1
      push_cast
      ring
    _ ≤ |(changed : ℚ) - ((b * normal : ℕ) : ℚ)| +
        |(rest : ℚ) - ((c * normal : ℕ) : ℚ)| := abs_add_le _ _
    _ ≤ ((b * bound : ℕ) : ℚ) + ((E * bound : ℕ) : ℚ) := add_le_add hlocal hrest
    _ = (((b + E) * bound : ℕ) : ℚ) := by push_cast; ring

/-- Direct induction over the actual compiled intervals. The trace, its
initial row, and every split sweep list refer to the same constructed word. -/
theorem compiled_row_error [NeZero M] [DecidableEq α]
    (r stop cursor : ℕ) (groups : List (EventGroup (2 * r + 1) Label))
    (hr : 0 < r) (hk : 0 < k) (hM : k + 1 ≤ M)
    (phase : Label → ℕ) (hphase : ∀ label, phase label < r) (choice : Label → Bool)
    (hfirst : ∀ G ∈ groups, r ≤ G.first)
    (hcursor : ∀ G ∈ groups, cursor ≤ groupStart r (fun H => phase H.label) G)
    (hfit : ∀ G ∈ groups, groupEnd r (fun H => phase H.label) G ≤ stop)
    (hbefore : groups.Pairwise Before)
    (q : Fin k → Fin M) (hmono : StrictMono q)
    (hrobust : Robust (fun i => cutValue (q i))) (hzero : q ⟨0, hk⟩ = 0)
    (background : Fin M → α) (labels : Option ℕ → α) (translation : Fin M)
    (gap : ℕ) (sweeps : List ℕ) (finalGap : ℕ)
    (htrace : Trace (by omega) background
      (FiniteProgram.word k (compile r (fun G => phase G.label) (fun G => choice G.label) stop cursor groups))
      labels (fun rank => q rank.rev + translation) gap sweeps finalGap)
    (hnd : (renderedBase background labels (fun rank => q rank.rev + translation) gap).Nodup)
    (hlen : (renderedBase background labels (fun rank => q rank.rev + translation) gap).length = M + k + 1)
    (hhead : ((render background (residents labels) (fun rank => q rank.rev + translation)).rotateLeft gap).head? =
      some (residents (k := k) labels ⟨k - 1, by omega⟩)) (satellite : α) :
    |((scheduleRows satellite sweeps
        (renderedBase background labels (fun rank => q rank.rev + translation) gap)).length : ℚ) -
      (((stop - cursor) * normalRows M k : ℕ) : ℚ)| ≤
      ((changedBatches r phase groups * batchBound M k : ℕ) : ℚ) := by
  have hM2 : 2 ≤ M := by omega
  have hnormal : normalRows M k ≤ batchBound M k := normal_batch_le M k hk hM
  induction groups generalizing cursor labels translation gap sweeps with
  | nil =>
    have ht : Trace (by omega) background (repeatWord (stop - cursor) (List.finRange k))
        labels (fun rank => q rank.rev + translation) gap sweeps finalGap := by
      simpa only [compile, word_replicate_normal] using htrace
    have hc := (translated_counts hM2 hk q hmono hrobust hzero background (stop - cursor)
      labels translation gap sweeps finalGap ht hnd hlen hhead satellite).1
    change (scheduleRows satellite sweeps _).length = (stop - cursor) * normalRows M k at hc
    rw [hc]
    simp only [changedBatches, Nat.zero_mul, sub_self, abs_zero, Nat.cast_zero, le_refl]
  | cons G groups ih =>
    let phases : EventGroup (2 * r + 1) Label → ℕ := fun H => phase H.label
    let start := groupStart r phases G
    let parking := groupParking r phases G
    let finish := groupEnd r phases G
    let a := start - cursor
    let b := parking + 1
    let firstProgram : List Macro := List.replicate a Macro.normal
    let repairProgram : List Macro := List.replicate (parking / 2) (Macro.parking (choice G.label)) ++ [Macro.normal]
    let tailProgram := compile r phases (fun H => choice H.label) stop finish groups
    have hcG : cursor ≤ start := hcursor G (by simp)
    have hfG : finish ≤ stop := hfit G (by simp)
    have hfinish : finish = start + parking + 1 := rfl
    have hindex : stop - cursor = a + b + (stop - finish) := by
      dsimp only [a, b]
      omega
    have hhalf : 2 * (parking / 2) = parking := Nat.mul_div_cancel' (groupParking_even r phases G)
    have hbatches : batchCount repairProgram = b := by
      simp only [repairProgram, batchCount_append, batchCount_replicate_parking,
        batchCount, Nat.add_zero, hhalf, b]
    have hprogram : compile r (fun H => phase H.label) (fun H => choice H.label) stop cursor (G :: groups) =
        firstProgram ++ repairProgram ++ tailProgram := by
      simp only [compile, firstProgram, repairProgram, tailProgram, a, start, parking,
        finish, phases, List.append_assoc, List.singleton_append]
    have hword : FiniteProgram.word k
        (compile r (fun H => phase H.label) (fun H => choice H.label) stop cursor (G :: groups)) =
        FiniteProgram.word k firstProgram ++ (FiniteProgram.word k repairProgram ++ FiniteProgram.word k tailProgram) := by
      rw [hprogram, FiniteProgram.word_append, FiniteProgram.word_append, List.append_assoc]
    rw [hword] at htrace
    obtain ⟨s1, s23, gap1, hsweeps, ht1, ht23⟩ := split_append (show 0 < M by omega) background
      (FiniteProgram.word k firstProgram) (FiniteProgram.word k repairProgram ++ FiniteProgram.word k tailProgram)
      labels (fun rank => q rank.rev + translation) gap sweeps finalGap htrace
    let labels1 := executeLabels (FiniteProgram.word k firstProgram) labels
    let translation1 := translationCut (a : ZMod M) + translation
    have hcuts1 : executeCuts (show 0 < M by omega) (FiniteProgram.word k firstProgram)
        (fun rank => q rank.rev + translation) = fun rank => q rank.rev + translation1 := by
      simpa only [firstProgram, batchCount_replicate_normal, translation1] using
        program_cuts (show 0 < M by omega) firstProgram (fun rank => q rank.rev) translation
    rw [hcuts1] at ht23
    change Trace (show 0 < M by omega) background
      (FiniteProgram.word k repairProgram ++ FiniteProgram.word k tailProgram)
      labels1 (fun rank => q rank.rev + translation1) gap1 s23 finalGap at ht23
    obtain ⟨s2, s3, gap2, hs23, ht2, ht3⟩ := split_append (show 0 < M by omega) background
      (FiniteProgram.word k repairProgram) (FiniteProgram.word k tailProgram)
      labels1 (fun rank => q rank.rev + translation1) gap1 s23 finalGap ht23
    have hm1 := endpoint_properties hM2 background (FiniteProgram.word k firstProgram) labels
      (fun rank => q rank.rev + translation) gap s1 gap1 ht1 hnd hlen
    rw [hcuts1] at hm1
    change (renderedBase background labels1 (fun rank => q rank.rev + translation1) gap1).Nodup ∧
      (renderedBase background labels1 (fun rank => q rank.rev + translation1) gap1).length = M + k + 1 at hm1
    let labels2 := executeLabels (FiniteProgram.word k repairProgram) labels1
    let translation2 := translationCut (b : ZMod M) + translation1
    have hcuts2 : executeCuts (show 0 < M by omega) (FiniteProgram.word k repairProgram)
        (fun rank => q rank.rev + translation1) = fun rank => q rank.rev + translation2 := by
      simpa only [hbatches, translation2] using
        program_cuts (show 0 < M by omega) repairProgram (fun rank => q rank.rev) translation1
    rw [hcuts2] at ht3
    change Trace (show 0 < M by omega) background (FiniteProgram.word k tailProgram)
      labels2 (fun rank => q rank.rev + translation2) gap2 s3 finalGap at ht3
    have hm2 := endpoint_properties hM2 background (FiniteProgram.word k repairProgram) labels1
      (fun rank => q rank.rev + translation1) gap1 s2 gap2 ht2 hm1.1 hm1.2
    rw [hcuts2] at hm2
    change (renderedBase background labels2 (fun rank => q rank.rev + translation2) gap2).Nodup ∧
      (renderedBase background labels2 (fun rank => q rank.rev + translation2) gap2).length = M + k + 1 at hm2
    have hlast : (FiniteProgram.word k repairProgram).getLast? =
        some (⟨k - 1, by omega⟩ : Fin k) :=
      word_last_normal k hk (List.replicate (parking / 2) (Macro.parking (choice G.label)))
    have hhead2 := ClosedTrace.trace_last_head (show 0 < M by omega) background
      (FiniteProgram.word k repairProgram) labels1 (fun rank => q rank.rev + translation1)
      gap1 s2 gap2 ht2 ⟨k - 1, by omega⟩ hlast
    rw [hcuts2] at hhead2
    obtain ⟨hGbefore, htailBefore⟩ := List.pairwise_cons.mp hbefore
    have hcTail : ∀ H ∈ groups, finish ≤ groupStart r (fun J => phase J.label) H := by
      intro H hH
      exact groupEnd_le_next r phases G H hr (hphase G.label) (hphase H.label)
        (hfirst G (by simp)) (hfirst H (by simp [hH])) (hGbefore H hH)
    have hrest := ih (cursor := finish) (labels := labels2) (translation := translation2)
      (gap := gap2) (sweeps := s3)
      (fun H hH => hfirst H (by simp [hH])) hcTail
      (fun H hH => hfit H (by simp [hH])) htailBefore ht3 hm2.1 hm2.2 hhead2
    have ht1normal : Trace (by omega) background (repeatWord a (List.finRange k))
        labels (fun rank => q rank.rev + translation) gap s1 gap1 := by
      simpa only [firstProgram, word_replicate_normal] using ht1
    have hfirstRows := (translated_counts hM2 hk q hmono hrobust hzero background a labels translation
      gap s1 gap1 ht1normal hnd hlen hhead satellite).1
    have hchangedRows := trace_rows_le hM2 background (FiniteProgram.word k repairProgram) labels1
      (fun rank => q rank.rev + translation1) gap1 s2 gap2 ht2 hm1.2 satellite
    rw [program_word_length, hbatches] at hchangedRows
    have hchangedRows' :
        (scheduleRows satellite s2 (renderedBase background labels1
          (fun rank => q rank.rev + translation1) gap1)).length ≤ b * batchBound M k := by
      simpa only [batchBound, Nat.mul_assoc] using hchangedRows
    have hrows1 := rows_append_length (show 0 < M by omega) background (FiniteProgram.word k firstProgram)
      labels (fun rank => q rank.rev + translation) gap s1 s23 gap1 ht1 satellite
    rw [hcuts1] at hrows1
    have hrows2 := rows_append_length (show 0 < M by omega) background (FiniteProgram.word k repairProgram)
      labels1 (fun rank => q rank.rev + translation1) gap1 s2 s3 gap2 ht2 satellite
    rw [hcuts2] at hrows2
    have hrows : (scheduleRows satellite sweeps
        (renderedBase background labels (fun rank => q rank.rev + translation) gap)).length =
        a * normalRows M k +
          (scheduleRows satellite s2 (renderedBase background labels1 (fun rank => q rank.rev + translation1) gap1)).length +
          (scheduleRows satellite s3 (renderedBase background labels2 (fun rank => q rank.rev + translation2) gap2)).length := by
      rw [hsweeps, hrows1, hs23, hrows2, hfirstRows]
      simp only [normalRows, Nat.add_assoc, labels2]
    have hchanged : changedBatches r phase (G :: groups) = b + changedBatches r phase groups := rfl
    rw [hrows, hindex, hchanged]
    exact combine_errors a b (stop - finish) (changedBatches r phase groups) _ _
      (normalRows M k) (batchBound M k) hchangedRows' hnormal hrest

/-- The checked changed-batch count gives exactly the stated perturbation
allowance when k=r-1 and M>=r. -/
theorem perturbation_budget (r M K changed : ℕ) (hr : 6 ≤ r) (hM : r ≤ M)
    (hchanged : changed ≤ 2 * (2 * r + 1) * K) :
    changed * batchBound M (r - 1) ≤ 10 * r ^ 2 * K * M := by
  have hc : changed ≤ 5 * r * K := hchanged.trans
    (Nat.mul_le_mul_right K (show 2 * (2 * r + 1) ≤ 5 * r by omega))
  have hb : batchBound M (r - 1) ≤ 2 * r * M := by
    change (r - 1) * (M + (r - 1)) ≤ 2 * r * M
    calc
      (r - 1) * (M + (r - 1)) ≤ r * (M + M) :=
        Nat.mul_le_mul (Nat.sub_le r 1)
          (Nat.add_le_add (le_refl M) ((Nat.sub_le r 1).trans hM))
      _ = 2 * r * M := by ring
  calc
    changed * batchBound M (r - 1) ≤ (5 * r * K) * (2 * r * M) := Nat.mul_le_mul hc hb
    _ = 10 * r ^ 2 * K * M := by ring

/-- The full actual repaired trace differs from its exact normal row count
by at most 10r^2 K M. The event allowance K bounds the events in the actual
groups, and cleanup batches are included in the derived changed count. -/
theorem repaired_row_error [NeZero M] [DecidableEq α]
    (r K : ℕ) (groups : List (EventGroup (2 * r + 1) Label))
    (hr : 6 ≤ r) (hM : r ≤ M)
    (phase : Label → ℕ) (hphase : ∀ label, phase label < r) (choice : Label → Bool)
    (hfirst : ∀ G ∈ groups, r ≤ G.first)
    (hfit : ∀ G ∈ groups, groupEnd r (fun H => phase H.label) G ≤ M)
    (hbefore : groups.Pairwise Before)
    (hcount : (groups.flatMap EventGroup.events).length ≤ K)
    (q : Fin (r - 1) → Fin M) (hmono : StrictMono q)
    (hrobust : Robust (fun i => cutValue (q i))) (hzero : q ⟨0, by omega⟩ = 0)
    (background : Fin M → α) (labels : Option ℕ → α) (translation : Fin M)
    (gap : ℕ) (sweeps : List ℕ) (finalGap : ℕ)
    (htrace : Trace (by omega) background
      (FiniteProgram.word (r - 1) (compile r (fun G => phase G.label) (fun G => choice G.label) M 0 groups))
      labels (fun rank => q rank.rev + translation) gap sweeps finalGap)
    (hnd : (renderedBase background labels (fun rank => q rank.rev + translation) gap).Nodup)
    (hlen : (renderedBase background labels (fun rank => q rank.rev + translation) gap).length = M + (r - 1) + 1)
    (hhead : ((render background (residents labels) (fun rank => q rank.rev + translation)).rotateLeft gap).head? =
      some (residents (k := r - 1) labels ⟨r - 1 - 1, by omega⟩)) (satellite : α) :
    |((scheduleRows satellite sweeps
        (renderedBase background labels (fun rank => q rank.rev + translation) gap)).length : ℚ) -
      ((M * ((r - 2) * M + r * (r - 1) + 1) : ℕ) : ℚ)| ≤
      ((10 * r ^ 2 * K * M : ℕ) : ℚ) := by
  classical
  have h := compiled_row_error (M := M) (k := r - 1) r M 0 groups (by omega) (by omega) (by omega)
    phase hphase choice hfirst (fun G _ => Nat.zero_le _) hfit hbefore
    q hmono hrobust hzero background labels translation gap sweeps finalGap
    htrace hnd hlen hhead satellite
  have hc := (changedBatches_bound r phase groups (by omega) hphase hfirst).trans
    (Nat.mul_le_mul_left (2 * (2 * r + 1)) hcount)
  have hb := perturbation_budget r M K (changedBatches r phase groups) hr hM hc
  have hbQ : ((changedBatches r phase groups * batchBound M (r - 1) : ℕ) : ℚ) ≤
      ((10 * r ^ 2 * K * M : ℕ) : ℚ) := by exact_mod_cast hb
  have hnormal : M * normalRows M (r - 1) = M * ((r - 2) * M + r * (r - 1) + 1) := by
    simp only [normalRows, show r - 1 - 1 = r - 2 by omega,
      Nat.sub_add_cancel (show 1 ≤ r by omega)]
    ring
  simpa only [Nat.sub_zero, hnormal] using h.trans hbQ

end CoefficientTwoPrecision.RepairRowCounts

#print axioms CoefficientTwoPrecision.RepairRowCounts.compiled_row_error
#print axioms CoefficientTwoPrecision.RepairRowCounts.repaired_row_error
