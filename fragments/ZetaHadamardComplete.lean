import Verified

open Filter
namespace RHConnections.CanonicalFactor
open SpectralTail

theorem zeta_hadamard_factorization : ZetaHadamardFactorization := by
  obtain ⟨Cx,hCx,hX⟩ := entireXi_posLog_growth
  obtain ⟨Cp,hCp,hP⟩ := zetaCanonicalProduct_posLog_growth
  apply zeta_hadamard_of_quotient_mean_bound
  intro G hG _ he
  refine ⟨2*(Cx+Cp), ?_⟩
  intro R hR
  have hR₀ : 0 < R := by linarith
  have hx (s : ℂ) (hs : s ∈ Metric.sphere (0:ℂ) R) :
      Real.log ‖entireXi s‖ ≤ Cx*(R*Real.sqrt R) := by
    calc
      _ ≤ Real.posLog ‖entireXi s‖ := le_max_right _ _
      _ ≤ _ := by simpa only [mul_assoc] using hX R hR s hs
  have hp (s : ℂ) (hs : s ∈ Metric.sphere (0:ℂ) R) :
      Real.log ‖zetaCanonicalProduct s‖ ≤ Cp*(R*Real.sqrt R) :=
    (le_max_right _ _).trans (hP R hR₀.le s hs)
  refine (quotient_meanAbsRe_le (fun s => (hG s).differentiableAt) he hR₀ hx hp).trans ?_
  have h := max_le (le_add_of_nonneg_right (show 0 ≤ Cp*(R*Real.sqrt R) by positivity))
    (le_add_of_nonneg_left (show 0 ≤ Cx*(R*Real.sqrt R) by positivity))
  calc
    _ ≤ 2*(Cx*(R*Real.sqrt R) + Cp*(R*Real.sqrt R)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring
end RHConnections.CanonicalFactor

namespace RHConnections.PoleCompensation
open CanonicalFactor SpectralTail RelativeResolvent

theorem compensated_zeta_euler_spectral_limit
    (z z₀ : ℂ) (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    Tendsto (fun n => primeTest n z z₀ - poleTest (1/2) n z z₀) atTop
      (nhds (relative z z₀ ((-1/2:ℝ):ℂ) - zetaSpectralRelative z z₀ -
        realPlaceRelative z z₀)) :=
  compensated_zeta_euler_spectral_limit_of_hadamard zeta_hadamard_factorization z z₀ hz hz₀

end RHConnections.PoleCompensation
