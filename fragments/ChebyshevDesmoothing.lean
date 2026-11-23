import Verified

noncomputable section
namespace RHConnections.ChebyshevCriterion
open Filter Asymptotics PerronRamp

theorem chebyshev_cancellation_of_smoothed_power {P : ℝ → ℝ → ℂ}
    (hPole : ∀ X h : ℝ, 1 ≤ X → 0 < h → h ≤ 1 →
      ‖P h X - ((X:ℂ)-1)‖ ≤ 3*X*h)
    (hS : ∀ d : ℝ, 0 < d → d < 1/2 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ X h : ℝ, 1 ≤ X → 0 < h → h ≤ 1 →
      ‖smoothedChebyshev h X - P h X‖ ≤ C*X^(1/2+d)*h^(-d)) :
    ChebyshevCancellation := by
  intro ε hε
  let d := min (ε/2) (1/4)
  have hd : 0 < d := lt_min (by linarith) (by norm_num)
  have hd₁ : d ≤ ε/2 := min_le_left _ _
  have hd₂ : d ≤ 1/4 := min_le_right _ _
  obtain ⟨C,hC,hB⟩ := hS d hd (by linarith)
  refine isBigO_iff.mpr ⟨C+6*(1+d⁻¹)+4,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  let h := X^(-(1/2:ℝ))
  have hh : 0 < h := Real.rpow_pos_of_pos hXp _
  have hh₁ : h ≤ 1 := by
    have he := Real.rpow_le_rpow_of_exponent_le hX (show -(1/2:ℝ) ≤ 0 by norm_num)
    simpa only [h,Real.rpow_zero] using he
  have hmul : X*h = X^(1/2:ℝ) := by
    calc
      _ = X^(1:ℝ)*X^(-(1/2:ℝ)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hXp, show (1:ℝ)+ -(1/2)=1/2 by ring]
  have hp : h^(-d) = X^(d/2) := by
    dsimp only [h]
    rw [← Real.rpow_mul hXp.le, show -(1/2:ℝ)*(-d)=d/2 by ring]
  have hS' := hB X h hX hh hh₁
  rw [hp,mul_assoc,← Real.rpow_add hXp] at hS'
  have hS'' : ‖smoothedChebyshev h X-P h X‖ ≤ C*X^(1/2+ε) :=
    hS'.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) hC)
  have hlog : Real.log X ≤ d⁻¹*X^d := by
    have hEst := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hXp d)
    rw [Real.log_rpow hXp] at hEst
    rw [mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hd).2 (by linarith)
  have hOne : 1 ≤ X^d := Real.one_le_rpow hX hd.le
  have hLogNonneg : 0 ≤ Real.log X := Real.log_nonneg hX
  have hLog' : 1+Real.log X ≤ (1+d⁻¹)*X^d := by
    linarith only [hlog,hOne,show (1+d⁻¹)*X^d = X^d+d⁻¹*X^d by ring]
  have hPow : X^(1/2:ℝ) ≤ X^(1/2+ε) :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hOne' : 1 ≤ X^(1/2:ℝ) := Real.one_le_rpow hX (by norm_num)
  have hApprox := smoothedChebyshev_error hX hh hh₁
  rw [hmul] at hApprox
  have hSmoothErr : ‖smoothedChebyshev h X-psi X‖ ≤
      6*(1+d⁻¹)*X^(1/2+ε) := by
    change ‖smoothedChebyshev h X-sharpChebyshev X‖ ≤ _
    calc
      _ ≤ 3*(X^(1/2:ℝ)+1)*(1+Real.log X) := hApprox
      _ ≤ (6*X^(1/2:ℝ))*((1+d⁻¹)*X^d) := by
        apply mul_le_mul (by linarith) hLog' (by linarith) (by positivity)
      _ = 6*(1+d⁻¹)*X^(1/2+d) := by rw [Real.rpow_add hXp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) (by positivity)
  have hPoleErr := hPole X h hX hh hh₁
  rw [mul_assoc,hmul] at hPoleErr
  have hdecomp : psiError X = (psi X-smoothedChebyshev h X) +
      (smoothedChebyshev h X-P h X) + (P h X-((X:ℂ)-1)) - 1 := by
    unfold psiError
    ring
  rw [hdecomp,Real.norm_of_nonneg (Real.rpow_nonneg hXp.le _)]
  calc
    _ ≤ (‖psi X-smoothedChebyshev h X‖+‖smoothedChebyshev h X-P h X‖) +
        ‖P h X-((X:ℂ)-1)‖ + ‖(1:ℂ)‖ := by
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
      rw [norm_sub_rev (psi X),norm_one]
      nlinarith only [hS'',hSmoothErr,hPoleErr,hPow,hOne'.trans hPow]

end RHConnections.ChebyshevCriterion
