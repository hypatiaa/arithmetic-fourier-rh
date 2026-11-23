import Verified

open MeasureTheory
namespace RHConnections.AnalyticObligations

theorem fullCandidate_compact_derivative_bounds {a : ℝ} {z₀ : ℂ}
    (ha : 0 ≤ a) (hz₀ : a < z₀.re)
    (K : Set ℂ) (hK : IsCompact K) (hsub : K ⊆ halfPlane a) :
    ∃ B : Fin 3 → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ n z, z ∈ K → ∀ sigma : ℝ, |sigma| ≤ a → ∀ j : Fin 3,
        Integrable (fun x : ℝ => Real.exp (sigma*x) *
          ‖iteratedDeriv j.val (Mollifier.fullCandidate n z z₀) x‖) ∧
        weightedDerivativeMass sigma j.val (Mollifier.fullCandidate n z z₀) ≤ B j := by
  obtain ⟨beta, L, hgap, _, hb₀, hL₀, hpar⟩ := compact_parameter_gap hz₀ hK hsub
  obtain ⟨B, hB, hbound⟩ := Mollifier.fullCandidate_weighted_derivative_bounds ha hgap
  refine ⟨B, hB, ?_⟩
  intro n z hz sigma hsigma j
  exact hbound n z z₀ (hpar z hz).1 hb₀ (hpar z hz).2 hL₀ sigma hsigma j

end RHConnections.AnalyticObligations
