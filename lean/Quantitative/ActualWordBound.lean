import Quantitative.ActualStageAssembly
import Quantitative.AsymptoticTransfer

/-!
# Covering words from the actual assembled Stages

The finite theorem constructs a word satisfying the original `Covers`
predicate and the coefficient `2 + 74/r`. Its only geometric hypothesis is
`SparseFamilySupplier`, which supplies actual source families. Initial
padding, all Stage iterations, the dense tail, pending closure, and word
spelling are proved constructions.

The final theorem connects this supplier interface to the real asymptotic
theorem for the original minimum length. MainTheorems applies it to the
proved construction and gives the unconditional result.
-/

namespace CoefficientTwoPrecision.ActualWordBound

open SuperpermutationUpperBound SuperpermutationUpperBound43586371
open StageState SparseStageIteration Asymptotics

/-- Spell an actual Stage and bound the complete joining cost. -/
theorem word_of_bounded_stage {m : ℕ} (S : BuiltStage m) (r : ℕ) (hr : 0 < r)
    (hbound : ((m + 3 : ℕ) : ℚ) * S.X + ((m + 3 : ℕ) : ℚ) * S.zmass +
      2 * ((m + 3 : ℕ) : ℚ) * S.p ≤ 2 + 74 / (r : ℚ)) :
    ∃ w : List (Fin (m + 3)), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * F3 (m + 3) + (2 * r + 74) * (m - 1).factorial := by
  have hm : 2 ≤ m := by simpa only [S.size] using S.valid.two
  have hmass : S.R + S.P * S.A0.length = S.A0.length.factorial := by
    simpa only [S.size, Nat.mul_comm S.P] using S.mass
  have H := StageEndpoints.word_of_stage S.valid hmass S.labels 2 (by decide)
    (by rw [S.size]; omega)
  rw [S.size] at H
  obtain ⟨w, hw, hlength⟩ := H
  have hindex : m + 1 - 2 = m - 1 := by omega
  simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero, hindex] at hlength
  have hjoin : w.length ≤ F3 (m + 3) + S.Q + (2 * m - 1) * (S.c + S.P) := by
    calc
      w.length ≤ F3 (m + 3) + S.Q + m * (S.c + S.P) +
          (m - 1) * (S.c + S.P) :=
        hlength.trans (Nat.add_le_add_left
          (Nat.mul_le_mul_left (m - 1) (min_le_left _ _)) _)
      _ = F3 (m + 3) + S.Q + (2 * m - 1) * (S.c + S.P) := by
        rw [Nat.add_assoc, ← Nat.add_mul, show m + (m - 1) = 2 * m - 1 by omega]
  have hjoinQ : (w.length : ℚ) ≤ SuperpermutationBounds.F3 (m + 3) + (S.Q : ℚ) +
      (2 * (m : ℚ) - 1) * ((S.c : ℚ) + (S.P : ℚ)) := by
    have hcast : (w.length : ℚ) ≤
        ((F3 (m + 3) + S.Q + (2 * m - 1) * (S.c + S.P) : ℕ) : ℚ) := by
      exact_mod_cast hjoin
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show 1 ≤ 2 * m by omega),
      Nat.cast_ofNat, Nat.cast_one, cast_F3] using hcast
  have hmQ : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hfac : (0 : ℚ) < ((m - 1).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos (m - 1)
  have hfactorial : (m.factorial : ℚ) = (m : ℚ) * ((m - 1).factorial : ℚ) := by
    exact_mod_cast (Nat.mul_factorial_pred (show m ≠ 0 by omega)).symm
  have hscale :
      ((m : ℚ) * S.y + (2 * (m : ℚ) - 1) * (S.zmass + S.p)) *
          ((m - 1).factorial : ℚ) =
        (S.Q : ℚ) + (2 * (m : ℚ) - 1) * ((S.c : ℚ) + (S.P : ℚ)) := by
    simp only [BuiltStage.y, BuiltStage.zmass, BuiltStage.p]
    rw [hfactorial]
    field_simp [ne_of_gt hmQ, ne_of_gt hfac] <;> ring
  have hcompletion : ((w.length : ℚ) - SuperpermutationBounds.F3 (m + 3)) /
      ((m - 1).factorial : ℚ) ≤
        (m : ℚ) * S.y + (2 * (m : ℚ) - 1) * (S.zmass + S.p) := by
    apply (div_le_iff₀ hfac).2
    rw [hscale]
    linarith only [hjoinQ]
  have hcost := completion_coefficient_le ((m + 3 : ℕ) : ℚ) (m : ℚ)
    S.y S.zmass S.p S.X (by exact_mod_cast (show m ≤ m + 3 by omega))
    S.X_nonneg S.zmass_nonneg S.p_nonneg rfl
  have hnormal := hcompletion.trans (hcost.trans hbound)
  have hword : (w.length : ℚ) ≤ SuperpermutationBounds.F3 (m + 3) +
      (2 + 74 / (r : ℚ)) * ((m - 1).factorial : ℚ) := by
    have h := (div_le_iff₀ hfac).1 hnormal
    linarith only [h]
  refine ⟨w, (covers_iff_isSuperpermutation w).mpr hw, ?_⟩
  have hindex' : m + 3 - 4 = m - 1 := by omega
  have h := (integer_bound_iff (m + 3) r hr w).2 (by simpa only [hindex'] using hword)
  simpa only [hindex'] using h

/-- The finite word theorem from a sparse-family supplier.
MainTheorems applies the proved supplier construction. -/
theorem finite_word (n r : ℕ) (hr : 6 ≤ r)
    (hn : transferConstant * r ^ 61 ≤ n) (supplier : SparseFamilySupplier r) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * F3 n + (2 * r + 74) * (n - 4).factorial := by
  obtain ⟨S, hS⟩ := ActualStageAssembly.final_stage n r hr hn supplier
  have hm : 2 ≤ n - 3 := by simpa only [S.size] using S.valid.two
  have hsize : n - 3 + 3 = n := Nat.sub_add_cancel (by omega)
  have hindex : n - 3 - 1 = n - 4 := by omega
  let Claim : ℕ → Prop := fun N =>
    ∃ w : List (Fin N), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * F3 N + (2 * r + 74) * (n - 4).factorial
  have H : Claim (n - 3 + 3) := by
    obtain ⟨w, hw, hlength⟩ := word_of_bounded_stage S r (by omega)
      (by simpa only [hsize] using hS)
    exact ⟨w, hw, by simpa only [hindex] using hlength⟩
  exact Eq.mp (congrArg Claim hsize) H

/-- Supplying the constructed geometric families establishes the finite
original-word input used by the already proved real asymptotic bridge. -/
theorem original_word_bound
    (suppliers : ∀ r : ℕ, 6 ≤ r → 6 ∣ r → SparseFamilySupplier r) :
    OriginalWordFiniteBound61 := by
  intro r hr hdiv n hn
  exact finite_word n r hr hn (suppliers r hr hdiv)

/-- The real error estimate for the original shortest length follows from
the sparse geometric supplier theorem. -/
theorem asymptotic_61
    (suppliers : ∀ r : ℕ, 6 ≤ r → 6 ∣ r → SparseFamilySupplier r) :
    (fun n : ℕ => (ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ) -
      2 * ((n - 4).factorial : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 61 : ℝ)) :=
  conditional_asymptotic_61 (original_word_bound suppliers)

end CoefficientTwoPrecision.ActualWordBound

#print axioms CoefficientTwoPrecision.ActualWordBound.word_of_bounded_stage
#print axioms CoefficientTwoPrecision.ActualWordBound.finite_word
#print axioms CoefficientTwoPrecision.ActualWordBound.original_word_bound
#print axioms CoefficientTwoPrecision.ActualWordBound.asymptotic_61
