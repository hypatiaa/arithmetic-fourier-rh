import Verified

open Filter Asymptotics
namespace RHConnections.ArithmeticFourierInversion
open MertensCriterion PoleCompensation

theorem mertens_eq_natural_M (x : ℝ) : mertens x = (M ⌊x⌋₊ : ℂ) := by
  have hrange : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [mertens, hrange, M, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [moebiusCoeff, muR]

theorem mertensCancellation_of_natural_power_bounds
    (hM : ∀ ε : ℝ, 0 < ε → NaturalPowerBound M (1/2+ε)) : MertensCancellation := by
  intro ε hε
  obtain ⟨C,hC,hM⟩ := hM ε hε
  apply isBigO_iff.mpr
  refine ⟨C,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have h0 : 0 ≤ x := by linarith
  have hn : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  rw [mertens_eq_natural_M, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.rpow_nonneg h0 _)]
  exact (hM ⌊x⌋₊ hn).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le h0) (by linarith)) hC)

theorem coherent_energy_growth_iff_natural_mertens (B : ℕ) :
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ, 1 ≤ X → CoherentEnergyBounds.energy (S B) B X ≤ C*(X:ℝ)^(1+δ)) ↔
      ∀ ε : ℝ, 0 < ε → NaturalPowerBound M (1/2+ε) :=
  (CoherentEnergyBounds.all_epsilon_iff (S B) B).symm.trans (M_all_epsilon_iff_S B).symm

theorem coherent_energy_growth_implies_line_residual (B : ℕ)
    (hE : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ, 1 ≤ X → CoherentEnergyBounds.energy (S B) B X ≤ C*(X:ℝ)^(1+δ))
    {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) : ZetaLineEulerResidual z₀ :=
  line_euler_residual_of_mertens (mertensCancellation_of_natural_power_bounds
    ((coherent_energy_growth_iff_natural_mertens B).mp hE)) hz₀

end RHConnections.ArithmeticFourierInversion
