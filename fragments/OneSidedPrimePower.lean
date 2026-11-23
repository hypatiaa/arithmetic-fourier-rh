import Verified
import PositiveSummatoryPower

noncomputable section
namespace RHConnections.PrimeErrorPower
open PoleCompensation PrimeErrorLaplace PositiveSummatory

theorem zero_free_of_signed_prime_power {a σ C : ℝ} (ha : 0≤a) (ha1 : a<1)
    (hσ : σ=1 ∨ σ= -1)
    (hC : ∀ x>1, 0≤σ*realPrimeError x*x^(-a)+C) :
    ∀ s : ℂ, a<s.re → riemannZeta s≠0 := by
  let G := fun s : ℂ => regularizedLogDerivative s-1
  have hG (b : ℝ) (hb : 0<b) : AnalyticAt ℂ G (b:ℂ) :=
    (regularizedLogDerivative_analytic (regularized_zeta_ne_zero_positive_real hb)).sub analyticAt_const
  obtain ⟨A,hA,hEq⟩ := signed_power_mellin_extension (G := G)
    real_prime_error_measurable hG (fun s hs => by
      refine ⟨prime_error_weighted_integrable hs,?_⟩
      have hn : s≠1 := by intro h; simp [h] at hs
      rw [prime_error_euler_integral hs]
      dsimp [G]
      rw [regularizedLogDerivative_eq hn (riemannZeta_ne_zero_of_one_le_re hs.le)])
    ha ha1 hσ hC
  have hAnalytic : AnalyticOnNhd ℂ (fun s => A s+1) {s : ℂ | a<s.re} :=
    fun s hs => (hA s hs).add analyticAt_const
  intro s hs
  apply zeta_zero_free_above_compensated_extension ha1 hAnalytic _ hs
  intro w hw
  have hn : w≠1 := by intro h; simp [h] at hw
  rw [hEq w hw]
  dsimp [G]
  rw [regularizedLogDerivative_eq hn (riemannZeta_ne_zero_of_one_le_re hw.le),sub_add_cancel]

end RHConnections.PrimeErrorPower
