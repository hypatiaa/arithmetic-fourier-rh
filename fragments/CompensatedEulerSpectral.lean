import Verified

namespace RHConnections.PoleCompensation
open SpectralTail CanonicalFactor RelativeResolvent

theorem compensated_zeta_euler_spectral_limit_of_hadamard
    (hH : ZetaHadamardFactorization)
    (z z₀ : ℂ) (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    Filter.Tendsto (fun n => primeTest n z z₀ - poleTest (1/2) n z z₀) Filter.atTop
      (nhds (relative z z₀ ((-1/2:ℝ):ℂ) - zetaSpectralRelative z z₀ -
        realPlaceRelative z z₀)) := by
  rw [← compensated_zeta_spectral_euler_match hH z z₀ hz hz₀
    (realPlaceRelative_eq_gammaDifference (by linarith) (by linarith))]
  exact compensated_zeta_limit_euler z z₀ hz hz₀

end RHConnections.PoleCompensation
