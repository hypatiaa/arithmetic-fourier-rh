import Verified

open MeasureTheory
noncomputable section
namespace RHConnections.PoleCompensation
open EulerGeometricLimit FourierDecay ArchimedeanLimit SpectralTail
open RelativeResolvent WeightedConvolution Mollifier

def primeTest (n : ℕ) (z z₀ : ℂ) : ℂ :=
  ∑' k : ℕ, halfWeight k * fullCandidate n z z₀ (Real.log k)

def realPlaceTest (n : ℕ) (z z₀ : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), (realPlaceKernel x : ℂ) * fullCandidate n z z₀ x

def realPlaceRelative (z z₀ : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), (realPlaceKernel x : ℂ) * logTest z z₀ x

def zetaSpectralTest (n : ℕ) (z z₀ : ℂ) : ℂ :=
  ∑' r : NontrivialZetaZero, (analyticOrderNatAt riemannZeta r.val : ℂ) *
    angularTransform (weighted (r.val-(1/2 : ℂ)).re (fullCandidate n z z₀))
      (r.val-(1/2 : ℂ)).im

def zetaSpectralRelative (z z₀ : ℂ) : ℂ :=
  ∑' r : NontrivialZetaZero, (analyticOrderNatAt riemannZeta r.val : ℂ) *
    relative z z₀ (r.val-(1/2 : ℂ))

def compensatedLogDerivative (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s - 1/(s-1)

theorem compensated_zeta_limit_euler (z z₀ : ℂ)
    (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    Filter.Tendsto (fun n => primeTest n z z₀ - poleTest (1/2) n z z₀) Filter.atTop
      (nhds (compensatedLogDerivative (z+1/2) - compensatedLogDerivative (z₀+1/2))) := by
  have h := (vonMangoldt_candidate_limit z z₀ hz hz₀).2.sub (poleTest_limit hz hz₀)
  change Filter.Tendsto (fun n => primeTest n z z₀ - poleTest (1/2) n z z₀)
    Filter.atTop (nhds _) at h
  convert h using 2
  simp only [compensatedLogDerivative, relative, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [show z+(1/2:ℂ)-1=z-1/2 by ring, show z₀+(1/2:ℂ)-1=z₀-1/2 by ring]
  ring

theorem compensated_zeta_limit_from_explicit_formula (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ (T : ℝ) (s : Finset NontrivialZetaZero), 1 ≤ T →
      (∀ r ∈ s, |r.val.im| ≤ T) →
      (∑ r ∈ s, (analyticOrderNatAt riemannZeta r.val : ℝ)) ≤ C * (T+2) * Real.log (T+2))
    (z z₀ : ℂ) (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re)
    (trace : ∀ n, primeTest n z z₀ + realPlaceTest n z z₀ =
      poleTest (1/2) n z z₀ + poleTest (-1/2) n z z₀ - zetaSpectralTest n z z₀) :
    Filter.Tendsto (fun n => primeTest n z z₀ - poleTest (1/2) n z z₀) Filter.atTop
      (nhds (relative z z₀ ((-1/2 : ℝ) : ℂ) -
        zetaSpectralRelative z z₀ - realPlaceRelative z z₀)) := by
  apply compensated_limit_from_finite_trace trace
  · exact realPlaceKernel_limit (by linarith) (by linarith)
  · exact poleTest_limit (by linarith) (by linarith)
  · exact (zeta_spectral_sum_limit C hC hcount z z₀ hz hz₀).2.2.2

end RHConnections.PoleCompensation
