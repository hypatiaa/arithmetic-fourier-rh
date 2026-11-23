import Verified

namespace RHConnections.PoleCompensation
open SpectralTail AnalyticObligations RelativeResolvent FourierDecay WeightedConvolution

noncomputable def restrictedTraceLimit {ι : Type*} (xi : ι → ℂ) (mult : ι → ℕ)
    (z₀ z : ℂ) : ℂ :=
  relative z z₀ ((-1/2 : ℝ) : ℂ) -
    (∑' i, (mult i : ℂ)*relative z z₀ (xi i)) - realPlaceRelative z z₀

theorem restrictedTraceLimit_analytic {ι : Type*} (xi : ι → ℂ) (mult : ι → ℕ)
    (N : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ (T : ℝ) (s : Finset ι), (∀ i ∈ s, |(xi i).im| ≤ T) →
      (∑ i ∈ s, (mult i : ℝ)) ≤ N T)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → N T ≤ C * (T+2) * Real.log (T+2))
    {a : ℝ} (ha : 0 ≤ a) (hstrip : ∀ i, |(xi i).re| ≤ a)
    {z₀ : ℂ} (hz₀ : a < z₀.re) :
    AnalyticOnNhd ℂ (restrictedTraceLimit xi mult z₀) (halfPlane a) := by
  have hS := relative_spectral_analytic xi mult (8*C*Real.log 2)
    (fun j s hs => (hcount _ s (fun i hi => (hs i hi).le)).trans
      (cumulative_count_dyadic N C hC hgrowth j)) ha hstrip hz₀
  have hA := (realPlaceRelative_differentiableOn (ha.trans hz₀.le)).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  have hz' : 0 < z.re := ha.trans_lt hz
  have hne : z - ((-1/2 : ℝ) : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re (sub_eq_zero.mp he)
    norm_num at hh
    linarith
  have hP : AnalyticAt ℂ (fun w => relative w z₀ ((-1/2 : ℝ) : ℂ)) z :=
    ((analyticAt_id.sub analyticAt_const).inv hne).sub analyticAt_const
  exact (hP.sub (hS z hz)).sub (hA z hz')

theorem restrictedTrace_compensated_limit {ι : Type*} (xi : ι → ℂ) (mult : ι → ℕ)
    (N : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ (T : ℝ) (s : Finset ι), (∀ i ∈ s, |(xi i).im| ≤ T) →
      (∑ i ∈ s, (mult i : ℝ)) ≤ N T)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → N T ≤ C * (T+2) * Real.log (T+2))
    {a : ℝ} (ha : 0 ≤ a) (hstrip : ∀ i, |(xi i).re| ≤ a)
    {z z₀ : ℂ} (hz : a < z.re) (hz₀ : a < z₀.re)
    (trace : ∀ n, primeTest n z z₀ + realPlaceTest n z z₀ =
      poleTest (1/2) n z z₀ + poleTest (-1/2) n z z₀ -
      (∑' i, (mult i : ℂ) * angularTransform
        (weighted (xi i).re (Mollifier.fullCandidate n z z₀)) (xi i).im)) :
    Filter.Tendsto (fun n => primeTest n z z₀ - poleTest (1/2) n z z₀) Filter.atTop
      (nhds (restrictedTraceLimit xi mult z₀ z)) := by
  apply compensated_limit_from_finite_trace trace
  · exact ArchimedeanLimit.realPlaceKernel_limit (ha.trans hz.le) (ha.trans hz₀.le)
  · exact poleTest_limit (lt_of_lt_of_le (by norm_num) (ha.trans hz.le))
      (lt_of_lt_of_le (by norm_num) (ha.trans hz₀.le))
  · exact (weighted_spectral_sum_limit xi mult N C hC hcount hgrowth ha hstrip z z₀ hz hz₀).2.2

end RHConnections.PoleCompensation
