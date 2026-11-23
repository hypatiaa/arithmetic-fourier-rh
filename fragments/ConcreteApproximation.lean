import Verified

open MeasureTheory
noncomputable section
namespace RHConnections.AnalyticObligations

def concreteApproximation (a : ℝ) (z₀ : ℂ) (ha : 0 < a)
    (hz₀ : a < z₀.re) (heuler : 1 < z₀.re) :
    SmoothRelativeApproximation a z₀ where
  strip_positive := ha
  reference_right := hz₀
  reference_euler := heuler
  test := fun n z => Mollifier.fullCandidate n z z₀
  smooth := fun n z => Mollifier.fullCandidate_smooth n z z₀
  compact := fun n z => Mollifier.fullCandidate_compact n z z₀
  endpoint := by
    intro n z
    refine ⟨Mollifier.epsilon n, Mollifier.epsilon_pos n, ?_⟩
    intro x hx
    exact Mollifier.fullCandidate_vanishes_left n z z₀
      ((le_abs_self x).trans (le_of_lt hx))
  parameter_holomorphic := by
    intro n x
    exact (Mollifier.fullCandidate_parameter_differentiable n z₀ x).differentiableOn
  limit := by
    intro z _ x
    exact Mollifier.fullCandidate_limit z z₀ x
  derivative_bounds := fun K hK hsub =>
    fullCandidate_compact_derivative_bounds ha.le hz₀ K hK hsub

theorem concreteApproximation_test (a : ℝ) (z₀ : ℂ) (ha : 0 < a)
    (hz₀ : a < z₀.re) (heuler : 1 < z₀.re) (n : ℕ) (z : ℂ) :
    (concreteApproximation a z₀ ha hz₀ heuler).test n z =
      Mollifier.fullCandidate n z z₀ := rfl

end RHConnections.AnalyticObligations
