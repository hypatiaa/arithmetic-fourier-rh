import Verified

open Filter
open scoped Topology
namespace RHConnections.CanonicalFactor
open AffineFromRealPart SpectralTail

theorem subquadratic_mean_of_three_halves_bound
    {G : ℂ → ℂ} (C : ℝ)
    (hg : ∀ R : ℝ, 3 ≤ R → meanAbsRe G R ≤ C * (R * Real.sqrt R)) :
    Tendsto (fun R : ℝ => meanAbsRe G R / R^2) atTop (𝓝 0) := by
  have hsqrt : Tendsto Real.sqrt atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop ((max b 0)^2)] with R hR
    calc
      b ≤ max b 0 := le_max_left _ _
      _ = Real.sqrt ((max b 0)^2) := (Real.sqrt_sq (le_max_right _ _)).symm
      _ ≤ Real.sqrt R := Real.sqrt_le_sqrt hR
  have hu : Tendsto (fun R : ℝ => C * (Real.sqrt R)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (tendsto_inv_atTop_zero.comp hsqrt).const_mul C
  apply squeeze_zero' _ _ hu
  · exact Eventually.of_forall fun R => div_nonneg
      (Real.circleAverage_nonneg_of_nonneg (by intro z hz; exact abs_nonneg _))
      (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop (3:ℝ)] with R hR
    have hp : 0 < R := by linarith
    have hsp := Real.sqrt_pos.2 hp
    calc
      _ ≤ (C*(R*Real.sqrt R))/R^2 := div_le_div_of_nonneg_right (hg R hR) (sq_nonneg _)
      _ = _ := by
        field_simp [hp.ne', hsp.ne']
        rw [Real.sq_sqrt hp.le]

theorem zeta_hadamard_of_quotient_mean_bound
    (h : ∀ G : ℂ → ℂ, (∀ s, AnalyticAt ℂ G s) → G 0 = 0 →
      (∀ s, Complex.exp (G s) = xiProductQuotient s) →
      ∃ C : ℝ, ∀ R : ℝ, 3 ≤ R → meanAbsRe G R ≤ C*(R*Real.sqrt R)) :
    ZetaHadamardFactorization := by
  obtain ⟨G,hG,hG₀,hExp⟩ := exists_normalized_entire_log_quotient
  obtain ⟨C,hC⟩ := h G hG hG₀ hExp
  have ha := affine_of_subquadratic_meanAbsRe (fun z => (hG z).differentiableAt)
    (subquadratic_mean_of_three_halves_bound C hC)
  refine ⟨deriv G 0, fun s => ?_⟩
  rw [← xiProductQuotient_mul s, ← hExp s, ha s, hG₀, zero_add]

end RHConnections.CanonicalFactor
