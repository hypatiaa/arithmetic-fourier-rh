import Verified
import Mathlib.Analysis.Analytic.Order

namespace RHConnections.SpectralTail
open FourierDecay WeightedConvolution RelativeResolvent

def ZerosIn (f : ℂ → ℂ) (region : Set ℂ) := {rho : ℂ // rho ∈ region ∧ f rho = 0}

theorem zero_order_positive {f : ℂ → ℂ} {rho : ℂ} (hz : f rho = 0)
    (ha : AnalyticAt ℂ f rho) (hfin : analyticOrderAt f rho ≠ ⊤) :
    0 < analyticOrderNatAt f rho := by
  have hn : analyticOrderAt f rho ≠ 0 := by
    intro he
    exact (analyticOrderAt_eq_zero.mp he).elim (fun h => h ha) (fun h => h hz)
  apply Nat.pos_of_ne_zero
  intro he
  apply hn
  rw [← Nat.cast_analyticOrderNatAt hfin, he, Nat.cast_zero]

theorem centered_zero_sum_limit (f : ℂ → ℂ) (region : Set ℂ)
    (ha : ∀ r : ZerosIn f region, AnalyticAt ℂ f r.val)
    (hf : ∀ r : ZerosIn f region, analyticOrderAt f r.val ≠ ⊤)
    (N : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ (T : ℝ) (s : Finset (ZerosIn f region)), (∀ r ∈ s, |r.val.im| ≤ T) →
      (∑ r ∈ s, (analyticOrderNatAt f r.val : ℝ)) ≤ N T)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → N T ≤ C * (T+2) * Real.log (T+2))
    {a : ℝ} (ha₀ : 0 ≤ a) (hstrip : ∀ r : ZerosIn f region, |r.val.re - 1/2| ≤ a)
    (z z₀ : ℂ) (hz : a < z.re) (hz₀ : a < z₀.re) :
    let m := fun r : ZerosIn f region => analyticOrderNatAt f r.val
    let xi := fun r : ZerosIn f region => r.val - (1/2 : ℂ)
    let F := fun n r => angularTransform
      (weighted (xi r).re (Mollifier.fullCandidate n z z₀)) (xi r).im
    (∀ r, 0 < m r) ∧ (∀ n, Summable (fun r => ‖(m r : ℂ) * F n r‖)) ∧
      Summable (fun r => ‖(m r : ℂ) * relative z z₀ (xi r)‖) ∧
      Filter.Tendsto (fun n => ∑' r, (m r : ℂ) * F n r) Filter.atTop
        (nhds (∑' r, (m r : ℂ) * relative z z₀ (xi r))) := by
  dsimp only
  refine ⟨fun r => zero_order_positive r.property.2 (ha r) (hf r), ?_⟩
  apply weighted_spectral_sum_limit (fun r : ZerosIn f region => r.val - (1/2 : ℂ))
    (fun r : ZerosIn f region => analyticOrderNatAt f r.val) N C hC
    (fun T s hs => hcount T s (fun r hr => ?_)) hgrowth ha₀ (fun r => ?_) z z₀ hz hz₀
  · have h := hs r hr
    norm_num [Complex.sub_im, Complex.div_im] at h
    exact h
  · simpa [Complex.sub_re, Complex.div_re] using hstrip r

end RHConnections.SpectralTail
