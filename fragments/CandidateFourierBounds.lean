import Verified

open MeasureTheory
namespace RHConnections.FourierDecay
open AnalyticObligations

theorem fullCandidate_uniform_angular_decay {a : ℝ} {z₀ : ℂ}
    (ha : 0 ≤ a) (hz₀ : a < z₀.re)
    (K : Set ℂ) (hK : IsCompact K) (hsub : K ⊆ halfPlane a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n z, z ∈ K → ∀ tau : ℝ,
      ‖angularTransform (Mollifier.fullCandidate n z z₀) tau‖ ≤ C/(1+tau^2) := by
  obtain ⟨B, hB, hb⟩ := fullCandidate_compact_derivative_bounds ha hz₀ K hK hsub
  refine ⟨4*Real.pi^2*B 0+B 2,
    add_nonneg (mul_nonneg (by positivity) (hB 0)) (hB 2), ?_⟩
  intro n z hz tau
  have hbound (j : Fin 3) :
      (∫ x : ℝ, ‖iteratedDeriv j.val (Mollifier.fullCandidate n z z₀) x‖) ≤ B j := by
    simpa only [zero_mul, Real.exp_zero, one_mul, weightedDerivativeMass] using
      (hb n z hz 0 (by simpa using ha) j).2
  exact uniform_angular_quadratic_decay
    (fun m : ℕ => Mollifier.fullCandidate m z z₀) (B 0) (B 2)
    (fun m => (Mollifier.fullCandidate_smooth m z z₀).of_le (by simp))
    (fun m k _ => Mollifier.fullCandidate_iteratedDeriv_integrable k m z z₀)
    (fun m => by
      simpa only [iteratedDeriv_zero] using
        (show (∫ x : ℝ, ‖iteratedDeriv 0 (Mollifier.fullCandidate m z z₀) x‖) ≤ B 0 from
          by simpa [weightedDerivativeMass] using
            (hb m z hz 0 (by simpa using ha) 0).2))
    (fun m => by
      simpa [weightedDerivativeMass] using
        (hb m z hz 0 (by simpa using ha) 2).2) n tau

end RHConnections.FourierDecay
