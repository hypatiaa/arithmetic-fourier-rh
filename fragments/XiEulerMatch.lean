import Verified

namespace RHConnections.PoleCompensation
open SpectralTail CanonicalFactor RelativeResolvent

theorem entireXi_logDerivative_euler {s : ℂ} (hs : 1 < s.re) :
    logDeriv entireXi s = 1/s + 1/(s-1) + logDeriv Complex.Gammaℝ s +
      logDeriv riemannZeta s := by
  have hs' : 0 < s.re := zero_lt_one.trans hs
  have h0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have h1 : s ≠ 1 := by intro h; simp [h] at hs
  have hZ := riemannZeta_ne_zero_of_one_le_re hs.le
  have hG := gamma_real_nonzero_of_re_pos hs'
  have hGA := (gamma_real_analytic_of_re_pos hs').differentiableAt
  have hD := differentiableAt_riemannZeta h1
  have hg := entireXi_zeta_germ hs' h1
  have he : logDeriv entireXi s =
      logDeriv (fun t => (t*(t-1)*Complex.Gammaℝ t)*riemannZeta t) s := by
    rw [logDeriv_apply, logDeriv_apply, hg.deriv_eq, hg.eq_of_nhds]
  have hc : HasDerivAt (fun t : ℂ => t-1) 1 s := (hasDerivAt_id s).sub_const 1
  have h01 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
  have hab : DifferentiableAt ℂ (fun t : ℂ => t*(t-1)) s :=
    differentiableAt_id.mul hc.differentiableAt
  rw [he, logDeriv_fun_mul (f := fun t : ℂ => t*(t-1)*Complex.Gammaℝ t)
      (g := riemannZeta) s (mul_ne_zero h01 hG) hZ (hab.mul hGA) hD,
    logDeriv_fun_mul (f := fun t : ℂ => t*(t-1)) (g := Complex.Gammaℝ) s h01 hG hab hGA,
    logDeriv_fun_mul (f := fun t : ℂ => t) (g := fun t : ℂ => t-1) s
      h0 (sub_ne_zero.mpr h1) differentiableAt_id hc.differentiableAt,
    logDeriv_id', logDeriv_apply (fun t : ℂ => t-1), hc.deriv]

theorem compensated_zeta_spectral_euler_match (hH : ZetaHadamardFactorization)
    (z z₀ : ℂ) (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re)
    (hA : realPlaceRelative z z₀ =
      logDeriv Complex.Gammaℝ (z₀+1/2) - logDeriv Complex.Gammaℝ (z+1/2)) :
    compensatedLogDerivative (z+1/2) - compensatedLogDerivative (z₀+1/2) =
      relative z z₀ ((-1/2:ℝ):ℂ) - zetaSpectralRelative z z₀ - realPlaceRelative z z₀ := by
  have hs : 1 < (z+(1/2:ℂ)).re := by norm_num [Complex.add_re, Complex.div_re]; linarith
  have hs₀ : 1 < (z₀+(1/2:ℂ)).re := by norm_num [Complex.add_re, Complex.div_re]; linarith
  rw [hA, zetaSpectralRelative_eq_logDerivative hH hz hz₀,
    entireXi_logDerivative_euler hs, entireXi_logDerivative_euler hs₀]
  rw [show ((-1/2 : ℝ) : ℂ) = -(1/2:ℂ) by norm_num]
  simp only [compensatedLogDerivative, logDeriv_apply, relative, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat, sub_neg_eq_add, one_div,
    neg_div]
  ring

end RHConnections.PoleCompensation
