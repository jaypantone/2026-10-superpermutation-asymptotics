import Quantitative.InitialNormalRun
import Quantitative.ActualMonodromy

/-!
# A numerical connector grid inside the proved normal run

The grid spacing is the actual monodromy gcd g. Taking floor(R/g) grid
intervals loses fewer than g positions. The normal-batch average and
g<=k leave enough room for two copies of this grid to cover every port.
-/

namespace CoefficientTwoPrecision.ConnectorGrid

theorem normal_run_margin (M k R : Nat) (hk : 4 ≤ k) (hM : 2 * k ≤ M)
    (hrun : (k - 1) * M + k * k + 1 ≤ k * R) :
    M + k + 2 * k ≤ 2 * R := by
  have hk1 : k - 1 + 1 = k := by omega
  have hk2 : k - 2 + 2 = k := by omega
  have hproduct := Nat.mul_le_mul_left (k - 2) hM
  have hquadratic := Nat.mul_le_mul_left k hk
  have hscaled : k * (M + k + 2 * k) ≤ k * (2 * R) := by
    nlinarith
  by_contra hnot
  have hstrict := Nat.mul_lt_mul_of_pos_left (show 2 * R < M + k + 2 * k by omega)
    (show 0 < k by omega)
  exact (Nat.not_lt_of_ge hscaled) hstrict

theorem grid_choice (M k R g : Nat) (hk : 4 ≤ k) (hM : 2 * k ≤ M)
    (hrun : (k - 1) * M + k * k + 1 ≤ k * R)
    (hg : 0 < g) (hgle : g ≤ k) :
    0 < R / g ∧ g * (R / g) ≤ R ∧ M + k ≤ 2 * (g * (R / g)) := by
  have hmargin := normal_run_margin M k R hk hM hrun
  have hrem := Nat.mod_lt R hg
  have hdivide := Nat.mod_add_div R g
  have hfit : g * (R / g) ≤ R := by omega
  have hcover : M + k ≤ 2 * (g * (R / g)) := by omega
  refine ⟨?_, hfit, hcover⟩
  by_contra hnot
  have hz : R / g = 0 := Nat.eq_zero_of_not_pos hnot
  rw [hz, Nat.mul_zero, Nat.mul_zero] at hcover
  omega

end CoefficientTwoPrecision.ConnectorGrid

#print axioms CoefficientTwoPrecision.ConnectorGrid.grid_choice
