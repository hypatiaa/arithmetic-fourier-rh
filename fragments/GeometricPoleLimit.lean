import Verified

namespace RHConnections.PoleCompensation
open FourierDecay WeightedConvolution RelativeResolvent

noncomputable def poleTest (sigma : ℝ) (n : ℕ) (z z₀ : ℂ) : ℂ :=
  angularTransform (weighted sigma (Mollifier.fullCandidate n z z₀)) 0

theorem poleTest_limit {sigma : ℝ} {z z₀ : ℂ}
    (hz : sigma < z.re) (hz₀ : sigma < z₀.re) :
    Filter.Tendsto (fun n => poleTest sigma n z z₀) Filter.atTop
      (nhds (relative z z₀ (sigma : ℂ))) := by
  simpa only [poleTest, Complex.ofReal_re, Complex.ofReal_im] using
    fullCandidate_weighted_angular_limit z z₀ (sigma : ℂ)
      (by simpa only [Complex.ofReal_re] using hz)
      (by simpa only [Complex.ofReal_re] using hz₀)

theorem compensated_limit_from_finite_trace
    {prime archimedean positivePole negativePole spectral : ℕ → ℂ}
    {A P S : ℂ}
    (trace : ∀ n, prime n + archimedean n =
      positivePole n + negativePole n - spectral n)
    (hA : Filter.Tendsto archimedean Filter.atTop (nhds A))
    (hP : Filter.Tendsto negativePole Filter.atTop (nhds P))
    (hS : Filter.Tendsto spectral Filter.atTop (nhds S)) :
    Filter.Tendsto (fun n => prime n - positivePole n) Filter.atTop
      (nhds (P - S - A)) := by
  have heq : (fun n => prime n - positivePole n) =
      (fun n => negativePole n - spectral n - archimedean n) :=
    funext fun n => trace_rearrangement (trace n)
  rw [heq]
  exact (hP.sub hS).sub hA

end RHConnections.PoleCompensation
