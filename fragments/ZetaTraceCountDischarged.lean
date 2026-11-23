import Verified

namespace RHConnections.PoleCompensation
open SpectralTail RelativeResolvent

theorem zeta_spectral_test_limit (z z₀ : ℂ) (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    (∀ n, Summable (fun r : NontrivialZetaZero =>
      ‖(analyticOrderNatAt riemannZeta r.val : ℂ) *
        FourierDecay.angularTransform
          (WeightedConvolution.weighted (r.val-(1/2:ℂ)).re (Mollifier.fullCandidate n z z₀))
          (r.val-(1/2:ℂ)).im‖)) ∧
    Summable (fun r : NontrivialZetaZero => ‖(analyticOrderNatAt riemannZeta r.val : ℂ) *
      relative z z₀ (r.val-(1/2:ℂ))‖) ∧
    Filter.Tendsto (fun n => zetaSpectralTest n z z₀) Filter.atTop
      (nhds (zetaSpectralRelative z z₀)) := by
  obtain ⟨C, hC, hcount⟩ := zeta_quantitative_zero_count
  exact (zeta_spectral_sum_limit C hC hcount z z₀ hz hz₀).2

theorem compensated_zeta_limit_of_full_finite_trace {z₀ : ℂ}
    (hfull : ZetaFullFiniteTrace z₀) (z : ℂ) (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    Filter.Tendsto (fun n => primeTest n z z₀ - poleTest (1/2) n z z₀) Filter.atTop
      (nhds (relative z z₀ ((-1/2 : ℝ) : ℂ) -
        zetaSpectralRelative z z₀ - realPlaceRelative z z₀)) := by
  obtain ⟨C, hC, hcount⟩ := zeta_quantitative_zero_count
  exact compensated_zeta_limit_from_explicit_formula C hC hcount z z₀ hz hz₀ (hfull z)

theorem riemannHypothesis_of_cofinal_zeta_traces {z₀ : ℂ} (hz₀ : 1/2 < z₀.re)
    (htrace : ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ a < ε ∧ a < 1/2 ∧
      ZetaRestrictedTrace a z₀) : RiemannHypothesis := by
  obtain ⟨C, hC, hcount⟩ := zeta_quantitative_zero_count
  exact riemannHypothesis_of_zeta_restricted_traces C hC hcount hz₀ htrace

theorem cofinal_zeta_traces_iff_RH {z₀ : ℂ} (hz₀ : 1/2 < z₀.re)
    (hfull : ZetaFullFiniteTrace z₀) :
    (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ a < ε ∧ a < 1/2 ∧ ZetaRestrictedTrace a z₀)
      ↔ RiemannHypothesis := by
  obtain ⟨C, hC, hcount⟩ := zeta_quantitative_zero_count
  exact zeta_restricted_traces_iff_RH C hC hcount hz₀ hfull

end RHConnections.PoleCompensation
