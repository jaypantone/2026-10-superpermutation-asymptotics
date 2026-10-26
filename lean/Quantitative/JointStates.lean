import PositiveParking
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith

/-!
# Joint role and phase states for a two-order parking menu

Stationary targets are numbered by their ranks in the normal order. Thus
the canonical order is `List.range k`; physical sorted position `i` has
normal-order rank `k - 1 - i` in the manuscript. `none` is the mobile role.

This module proves exact prefix-count resets, the complete role action at
the midpoint, reversal cancellation, and the cardinality of the joint
catalogue. Phase coordinates are natural numbers; `phase_le_one` proves
that they are zero or one for a target order without repetitions.

The final literal lemma proves what the full map does to a base presented
with its mobile last. Reconstructing the stationary circle from actual cut
coordinates, proving the short-map reconstruction, and deducing containment
for every emitted literal row remain separate obligations. No structure in
this file assumes that missing containment statement.
-/

namespace CoefficientTwoPrecision.JointStates

open PositiveParking

abbrev Role := Option Nat
abbrev Assignment := Role → Role

/-- The first `ell` updates of an order followed by its reverse. -/
def pairPrefix (order : List Nat) (ell : Nat) : List Nat :=
  (order ++ order.reverse).take ell

/-- Canonical phase after a prefix. Each completed batch is absorbed in
the common translation, including the midpoint of a parking pair. -/
def phase (order : List Nat) (ell a : Nat) : Nat :=
  if ell < order.length then (order.take ell).count a
  else if ell < 2 * order.length then
    (order.reverse.take (ell - order.length)).count a
  else 0

theorem phase_initial (order : List Nat) (a : Nat) : phase order 0 a = 0 := by
  simp [phase]

theorem phase_midpoint (order : List Nat) (a : Nat) :
    phase order order.length a = 0 := by
  simp [phase]

theorem phase_endpoint (order : List Nat) (a : Nat) :
    phase order (2 * order.length) a = 0 := by
  have hnot : ¬ 2 * order.length < order.length := by omega
  simp [phase, hnot]

/-- Proper prefixes have genuinely binary cut increments. -/
theorem phase_le_one (order : List Nat) (horder : order.Nodup) (ell a : Nat) :
    phase order ell a ≤ 1 := by
  unfold phase
  split
  · exact List.nodup_iff_count_le_one.mp
      (List.Nodup.sublist (List.take_sublist _ _) horder) a
  · split
    · exact List.nodup_iff_count_le_one.mp
        (List.Nodup.sublist (List.take_sublist _ _)
          (List.nodup_reverse.mpr horder)) a
    · omega

theorem pairPrefix_first_half (order : List Nat) (ell : Nat)
    (hell : ell ≤ order.length) : pairPrefix order ell = order.take ell := by
  exact List.take_append_of_le_length hell

theorem pairPrefix_second_half (order : List Nat) (j : Nat) :
    pairPrefix order (order.length + j) = order ++ order.reverse.take j := by
  exact List.take_length_add_append j

theorem midpoint_role_action (order : List Nat) (initial : Assignment) :
    execute updateLabels (pairPrefix order order.length) initial =
      execute updateLabels order initial := by
  rw [pairPrefix_first_half order _ (by omega), List.take_length]

theorem endpoint_role_action (order : List Nat) (initial : Assignment) :
    execute updateLabels (pairPrefix order (2 * order.length)) initial = initial := by
  have hlen : (order ++ order.reverse).length = 2 * order.length := by
    simp [Nat.two_mul]
  rw [pairPrefix, ← hlen, List.take_length]
  exact parking_restores_all_labels order initial

/-- A concrete six-role example shows why the role action must be retained
at the midpoint even though the cut-phase vector is already zero. -/
theorem midpoint_role_is_not_reset :
    (execute updateLabels (pairPrefix [0, 1, 2, 3, 4] 5) (id : Assignment)) none =
      some 4 := by
  rfl

/-- The midpoint reset is an equality of actual cumulative cut increments. -/
theorem midpoint_cut_reset (order : List Nat) (a q t : Nat)
    (ha : order.count a = 1) :
    q + t + (pairPrefix order order.length).count a =
      q + (t + 1) + phase order order.length a := by
  rw [pairPrefix_first_half order _ (by omega), List.take_length, ha, phase_midpoint]
  omega

/-- During the second batch the first complete batch contributes to the
translation, and only the reverse-order proper prefix contributes a phase. -/
theorem second_half_cut_reset (order : List Nat) (a q t j : Nat)
    (ha : order.count a = 1) (hj : j < order.length) :
    q + t + (pairPrefix order (order.length + j)).count a =
      q + (t + 1) + phase order (order.length + j) a := by
  have hfirst : ¬ order.length + j < order.length := by omega
  have hsecond : order.length + j < 2 * order.length := by omega
  rw [pairPrefix_second_half, List.count_append, ha]
  simp only [phase, hfirst, ↓reduceIte, hsecond, Nat.add_sub_cancel_left]
  omega

theorem endpoint_cut_reset (order : List Nat) (a q t : Nat)
    (ha : order.count a = 1) :
    q + t + (pairPrefix order (2 * order.length)).count a =
      q + (t + 2) + phase order (2 * order.length) a := by
  have hlen : (order ++ order.reverse).length = 2 * order.length := by
    simp [Nat.two_mul]
  rw [pairPrefix, ← hlen, List.take_length, List.count_append, List.count_reverse, ha]
  rw [hlen, phase_endpoint]
  omega

/-- Exchange just the first two targets of an order. -/
def swapFirstTwo : List Nat → List Nat
  | a :: b :: rest => b :: a :: rest
  | order => order

theorem swapFirstTwo_perm (order : List Nat) : (swapFirstTwo order).Perm order := by
  cases order with
  | nil => exact List.Perm.refl []
  | cons a rest =>
    cases rest with
    | nil => exact List.Perm.refl [a]
    | cons b tail => exact List.Perm.swap a b tail

theorem swapFirstTwo_length (order : List Nat) :
    (swapFirstTwo order).length = order.length :=
  (swapFirstTwo_perm order).length_eq

def menu (normal : List Nat) : Bool → List Nat
  | false => normal
  | true => swapFirstTwo normal

theorem menu_length (normal : List Nat) (choice : Bool) :
    (menu normal choice).length = normal.length := by
  cases choice
  · rfl
  · exact swapFirstTwo_length normal

/-- Two distinct first targets suffice for every forbidden stationary slot. -/
theorem menu_has_safe_first (a b forbidden : Nat) (rest : List Nat) (hab : a ≠ b) :
    ∃ choice : Bool,
      (menu (a :: b :: rest) choice).head? ≠ some forbidden := by
  by_cases h : a = forbidden
  · refine ⟨true, ?_⟩
    simp only [menu, swapFirstTwo, List.head?_cons, ne_eq, Option.some.injEq]
    intro hb
    exact hab (h.trans hb.symm)
  · refine ⟨false, ?_⟩
    simpa [menu] using h

/-- Actual label assignment after the indicated number of normal batches. -/
def normalBoundary (normal : List Nat) (s : Nat) : Assignment :=
  execute updateLabels (repeatWord s normal) id

theorem normalBoundary_period (k s : Nat) :
    normalBoundary (List.range k) (s + (k + 1)) =
      normalBoundary (List.range k) s := by
  unfold normalBoundary
  rw [repeatWord_add, execute_append, normal_labels_period]

structure State where
  labels : Assignment
  phases : Nat → Nat

/-- The joint pair, with the phase and role prefix kept correlated. -/
def joint (normal : List Nat) (s : Nat) (order : List Nat) (ell : Nat) : State where
  labels := execute updateLabels (pairPrefix order ell) (normalBoundary normal s)
  phases := phase order ell

abbrev Index (k : Nat) := Fin (k + 1) × (Bool × Fin (2 * k + 1))

def interpret (k : Nat) (normal : List Nat) (i : Index k) : State :=
  joint normal i.1.val (menu normal i.2.1) i.2.2.val

/-- The catalogue is the actual finite image of the prefix index set. -/
noncomputable def catalogue (k : Nat) (normal : List Nat) : Finset State := by
  classical
  exact Finset.univ.image (interpret k normal)

theorem catalogue_card_le (k : Nat) (normal : List Nat) :
    (catalogue k normal).card ≤ (k + 1) * 2 * (2 * k + 1) := by
  classical
  have h := Finset.card_image_le
    (s := (Finset.univ : Finset (Index k))) (f := interpret k normal)
  simpa [catalogue, Index, Fintype.card_prod, Nat.mul_assoc] using h

theorem catalogue_card_lt (k : Nat) (normal : List Nat) :
    (catalogue k normal).card < 4 * (k + 1)^2 := by
  have h := catalogue_card_le k normal
  nlinarith

/-- Each actual target-update prefix is represented by one catalogue index. -/
theorem pair_prefix_mem (k : Nat) (normal : List Nat) (s ell : Nat) (choice : Bool)
    (hs : s < k + 1) (hell : ell ≤ 2 * k) :
    joint normal s (menu normal choice) ell ∈ catalogue k normal := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(⟨s, hs⟩, choice, ⟨ell, by omega⟩), Finset.mem_univ _, ?_⟩
  rfl

/-- Normal and cleanup proper prefixes are first-half prefixes of menu zero. -/
theorem normal_prefix_mem (k : Nat) (normal : List Nat) (s ell : Nat)
    (hlen : normal.length = k) (hs : s < k + 1) (hell : ell < k) :
    ({ labels := execute updateLabels (normal.take ell) (normalBoundary normal s)
       phases := fun a => (normal.take ell).count a } : State) ∈ catalogue k normal := by
  have hm := pair_prefix_mem k normal s ell false hs (by omega)
  have hlt : ell < normal.length := by omega
  have heq : pairPrefix normal ell = normal.take ell :=
    pairPrefix_first_half normal ell (by omega)
  have hphase : phase normal ell = fun a => (normal.take ell).count a := by
    funext a
    simp [phase, hlt]
  simpa only [menu, joint, heq, hphase] using hm

/-- Executing the role updates preserves injectivity of an assignment. -/
theorem execute_labels_injective (word : List Nat) (initial : Assignment)
    (hinj : Function.Injective initial) :
    Function.Injective (execute updateLabels word initial) := by
  induction word generalizing initial with
  | nil => exact hinj
  | cons a word ih =>
    apply ih
    intro p q hpq
    have hstar : star a p = star a q := hinj hpq
    have h := congrArg (star a) hstar
    simpa only [star_involutive] using h

/-- Executing the role updates preserves surjectivity of an assignment. -/
theorem execute_labels_surjective (word : List Nat) (initial : Assignment)
    (hsurj : Function.Surjective initial) :
    Function.Surjective (execute updateLabels word initial) := by
  induction word generalizing initial with
  | nil => exact hsurj
  | cons a word ih =>
    apply ih
    intro value
    obtain ⟨p, hp⟩ := hsurj value
    refine ⟨star a p, ?_⟩
    simpa only [updateLabels, star_involutive] using hp

theorem joint_labels_bijective (normal : List Nat) (s : Nat)
    (order : List Nat) (ell : Nat) :
    Function.Bijective (joint normal s order ell).labels := by
  refine ⟨execute_labels_injective _ _ ?_, execute_labels_surjective _ _ ?_⟩
  · exact execute_labels_injective _ _ (fun _ _ h => h)
  · exact execute_labels_surjective _ _ (fun value => ⟨value, rfl⟩)

/-- The literal full map rotates all symbols except the final mobile. -/
def literalFullStep {α : Type} (base : List α) : List α :=
  base.dropLast.rotateLeft 1 ++ base.getLast?.toList

theorem literalFullStep_mobile_last {α : Type} (stationary : List α) (mobile : α) :
    literalFullStep (stationary ++ [mobile]) = stationary.rotateLeft 1 ++ [mobile] := by
  simp [literalFullStep]

end CoefficientTwoPrecision.JointStates

#print axioms CoefficientTwoPrecision.JointStates.second_half_cut_reset
#print axioms CoefficientTwoPrecision.JointStates.endpoint_role_action
#print axioms CoefficientTwoPrecision.JointStates.catalogue_card_lt
#print axioms CoefficientTwoPrecision.JointStates.normal_prefix_mem
#print axioms CoefficientTwoPrecision.JointStates.joint_labels_bijective
#print axioms CoefficientTwoPrecision.JointStates.literalFullStep_mobile_last
