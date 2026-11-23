import Verified

noncomputable section
namespace RHConnections.MertensCriterion
open PerronRamp ArithmeticFourierInversion

theorem mertens_power_bound_of_RH (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ‖mertens X‖ ≤ C*X^(1/2+ε) := by
  let d := min (ε/2) (1/4)
  let b := 1/2+d
  have hd : 0 < d := lt_min (by linarith) (by norm_num)
  have hd₁ : d ≤ ε/2 := min_le_left _ _
  have hd₂ : d ≤ 1/4 := min_le_right _ _
  have hb : 1/2 < b := by dsimp [b]; linarith
  have hb₁ : b < 1 := by dsimp [b]; linarith
  obtain ⟨C,hC,hB⟩ := smoothedMertens_bound_of_RH hRH hb hb₁ hd (by linarith : d < 1)
  refine ⟨C+6,by linarith,?_⟩
  intro X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  let h := X^(-(1/2:ℝ))
  have hh : 0 < h := Real.rpow_pos_of_pos hXp _
  have hh₁ : h ≤ 1 := by
    have he := Real.rpow_le_rpow_of_exponent_le hX (show -(1/2:ℝ) ≤ 0 by norm_num)
    simpa only [h,Real.rpow_zero] using he
  have hE := smoothedMertens_error hX hh hh₁
  have hS := hB X h hX hh hh₁
  have hmul : X*h = X^(1/2:ℝ) := by
    calc
      _ = X^(1:ℝ)*X^(-(1/2:ℝ)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hXp, show (1:ℝ)+ -(1/2)=1/2 by ring]
  have hp : h^(-d) = X^(d/2) := by
    dsimp only [h]
    rw [← Real.rpow_mul hXp.le, show -(1/2:ℝ)*(-d)=d/2 by ring]
  have hs : ‖smoothedMertens h X‖ ≤ C*X^(1/2+ε) := by
    rw [hp, mul_assoc, ← Real.rpow_add hXp] at hS
    exact hS.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by dsimp [b]; linarith)) hC)
  have he : ‖smoothedMertens h X - mertens X‖ ≤ 6*X^(1/2+ε) := by
    rw [hmul] at hE
    have hstep := Real.rpow_le_rpow_of_exponent_le hX (show (1/2:ℝ) ≤ 1/2+ε by linarith)
    have h1 := Real.one_le_rpow hX (show 0 ≤ 1/2+ε by linarith)
    linarith
  calc
    _ = ‖smoothedMertens h X - (smoothedMertens h X - mertens X)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖smoothedMertens h X‖ + ‖smoothedMertens h X - mertens X‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

theorem natural_mertens_bounds_of_RH (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε → NaturalPowerBound M (1/2+ε) := by
  intro ε hε
  obtain ⟨C,hC,h⟩ := mertens_power_bound_of_RH hRH hε
  refine ⟨C,hC,fun n hn => ?_⟩
  simpa [mertens_eq_natural_M,Complex.norm_real,Real.norm_eq_abs] using
    h (n:ℝ) (by exact_mod_cast hn)

theorem mertens_cancellation_iff_RH : MertensCancellation ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_mertens, fun h => mertensCancellation_of_natural_power_bounds
    (natural_mertens_bounds_of_RH h)⟩

end RHConnections.MertensCriterion

namespace RHConnections.ArithmeticFourierInversion
open MertensCriterion PoleCompensation

theorem coherent_energy_growth_iff_RH (B : ℕ) :
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ, 1 ≤ X → CoherentEnergyBounds.energy (S B) B X ≤ C*(X:ℝ)^(1+δ)) ↔
    RiemannHypothesis :=
  ⟨fun h => riemannHypothesis_of_mertens (mertensCancellation_of_natural_power_bounds
    ((coherent_energy_growth_iff_natural_mertens B).mp h)),
    fun h => (coherent_energy_growth_iff_natural_mertens B).mpr (natural_mertens_bounds_of_RH h)⟩

theorem coherent_energy_growth_iff_line_residual (B : ℕ) {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) :
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ, 1 ≤ X → CoherentEnergyBounds.energy (S B) B X ≤ C*(X:ℝ)^(1+δ)) ↔
    ZetaLineEulerResidual z₀ :=
  (coherent_energy_growth_iff_RH B).trans (riemannHypothesis_iff_line_euler_residual hz₀)

end RHConnections.ArithmeticFourierInversion
