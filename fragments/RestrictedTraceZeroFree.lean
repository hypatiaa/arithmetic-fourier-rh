import Verified

namespace RHConnections.PoleCompensation
open FourierDecay WeightedConvolution

def RestrictedFiniteTrace {ι : Type*} (xi : ι → ℂ) (mult : ι → ℕ)
    (a : ℝ) (z₀ : ℂ) : Prop :=
  ∀ (z : ℂ), a < z.re → ∀ n,
    primeTest n z z₀ + realPlaceTest n z z₀ =
      poleTest (1/2) n z z₀ + poleTest (-1/2) n z z₀ -
        (∑' i, (mult i : ℂ)*angularTransform
          (weighted (xi i).re (Mollifier.fullCandidate n z z₀)) (xi i).im)

theorem zero_free_from_restricted_finite_trace {ι : Type*} (xi : ι → ℂ) (mult : ι → ℕ)
    (N : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ (T : ℝ) (s : Finset ι), (∀ i ∈ s, |(xi i).im| ≤ T) →
      (∑ i ∈ s, (mult i : ℝ)) ≤ N T)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → N T ≤ C * (T+2) * Real.log (T+2))
    {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1/2)
    (hstrip : ∀ i, |(xi i).re| ≤ a)
    {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) (trace : RestrictedFiniteTrace xi mult a z₀)
    {s : ℂ} (hs : a+1/2 < s.re) : riemannZeta s ≠ 0 := by
  let F := fun t : ℂ => restrictedTraceLimit xi mult z₀ (t-1/2) +
    compensatedLogDerivative (z₀+1/2)
  have hA := restrictedTraceLimit_analytic xi mult N C hC hcount hgrowth ha hstrip (ha₁.trans hz₀)
  have hre (t : ℂ) : (t-(1/2:ℂ)).re = t.re-1/2 := by norm_num [Complex.sub_re, Complex.div_re]
  have hF : AnalyticOnNhd ℂ F {t : ℂ | a+1/2 < t.re} := by
    intro t ht
    have ht' : t-1/2 ∈ AnalyticObligations.halfPlane a := by
      change a+1/2 < t.re at ht
      change a < (t-1/2).re
      rw [hre]
      linarith
    have htA : AnalyticAt ℂ (fun w : ℂ => w-(1/2:ℂ)) t := analyticAt_id.sub analyticAt_const
    exact ((hA _ ht').comp (f := fun w : ℂ => w-(1/2:ℂ)) (x := t) htA).add analyticAt_const
  have hEuler (t : ℂ) (ht : 1 < t.re) : F t = compensatedLogDerivative t := by
    let z := t-(1/2:ℂ)
    have hz : 1/2 < z.re := by change 1/2 < (t-(1/2:ℂ)).re; rw [hre]; linarith
    have h₁ := compensated_zeta_limit_euler z z₀ hz hz₀
    have h₂ := restrictedTrace_compensated_limit xi mult N C hC hcount hgrowth ha
      hstrip (ha₁.trans hz) (ha₁.trans hz₀) (trace z (ha₁.trans hz))
    have he := tendsto_nhds_unique h₂ h₁
    have ht' : z+(1/2:ℂ) = t := by dsimp [z]; ring
    change restrictedTraceLimit xi mult z₀ z + compensatedLogDerivative (z₀+1/2) = _
    rw [he, sub_add_cancel, ht']
  exact zeta_zero_free_above_compensated_extension (by linarith) hF hEuler hs

end RHConnections.PoleCompensation
