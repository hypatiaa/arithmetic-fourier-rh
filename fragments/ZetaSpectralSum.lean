import Verified
import Mathlib.NumberTheory.LSeries.ZetaZeros

namespace RHConnections.SpectralTail
open FourierDecay WeightedConvolution RelativeResolvent

abbrev NontrivialZetaZero :=
  ZerosIn riemannZeta {rho : ℂ | 0 < rho.re ∧ rho.re < 1}

theorem zeta_nontrivial_zero_finite_order (r : NontrivialZetaZero) :
    AnalyticAt ℂ riemannZeta r.val ∧ analyticOrderAt riemannZeta r.val ≠ ⊤ := by
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    analyticOn_riemannZeta
  have hr : r.val ∈ ({1}ᶜ : Set ℂ) := by
    have hlt := r.property.1.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro he
    rw [he, Complex.one_re] at hlt
    exact (lt_irrefl _) hlt
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hne := riemannZeta_ne_zero_of_one_le_re (s := 2) (by norm_num)
  have hf2 : analyticOrderAt riemannZeta (2 : ℂ) ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hne)]
    exact WithTop.zero_ne_top
  exact ⟨hA _ hr, hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected h2 hr hf2⟩

theorem zeta_spectral_sum_limit (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ (T : ℝ) (s : Finset NontrivialZetaZero), 1 ≤ T →
      (∀ r ∈ s, |r.val.im| ≤ T) →
      (∑ r ∈ s, (analyticOrderNatAt riemannZeta r.val : ℝ)) ≤ C * (T+2) * Real.log (T+2))
    (z z₀ : ℂ) (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    let m := fun r : NontrivialZetaZero => analyticOrderNatAt riemannZeta r.val
    let xi := fun r : NontrivialZetaZero => r.val - (1/2 : ℂ)
    let F := fun n r => angularTransform
      (weighted (xi r).re (Mollifier.fullCandidate n z z₀)) (xi r).im
    (∀ r, 0 < m r) ∧ (∀ n, Summable (fun r => ‖(m r : ℂ) * F n r‖)) ∧
      Summable (fun r => ‖(m r : ℂ) * relative z z₀ (xi r)‖) ∧
      Filter.Tendsto (fun n => ∑' r, (m r : ℂ) * F n r) Filter.atTop
        (nhds (∑' r, (m r : ℂ) * relative z z₀ (xi r))) := by
  let N (T : ℝ) := C * (max T 1+2) * Real.log (max T 1+2)
  apply centered_zero_sum_limit riemannZeta _ (fun r => (zeta_nontrivial_zero_finite_order r).1)
    (fun r => (zeta_nontrivial_zero_finite_order r).2) N C hC _ _
    (by norm_num : (0 : ℝ) ≤ 1/2) _ z z₀ hz hz₀
  · intro T s hs
    exact hcount (max T 1) s (le_max_right _ _) (fun r hr => (hs r hr).trans (le_max_left _ _))
  · intro T hT
    simp [N, max_eq_left hT]
  · intro r
    have hr := r.property.1
    exact abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩

end RHConnections.SpectralTail
