import RelativeResolvent
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Support

open MeasureTheory Set Filter
open scoped ContDiff
noncomputable section
namespace RHConnections.AnalyticObligations

def halfPlane (a : ℝ) : Set ℂ := {z | a < z.re}

def weightedDerivativeMass (sigma : ℝ) (j : ℕ) (f : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, Real.exp (sigma*x) * ‖iteratedDeriv j f x‖

structure SmoothRelativeApproximation (a : ℝ) (z₀ : ℂ) where
  strip_positive : 0 < a
  reference_right : a < z₀.re
  reference_euler : 1 < z₀.re
  test : ℕ → ℂ → ℝ → ℂ
  smooth : ∀ n z, ContDiff ℝ ∞ (test n z)
  compact : ∀ n z, HasCompactSupport (test n z)
  endpoint : ∀ n z, ∃ epsilon : ℝ, 0 < epsilon ∧
    ∀ x : ℝ, |x| < epsilon → test n z x = 0
  parameter_holomorphic : ∀ n x,
    DifferentiableOn ℂ (fun z => test n z x) (halfPlane a)
  limit : ∀ z ∈ halfPlane a, ∀ x,
    Tendsto (fun n => test n z x) atTop
      (nhds (RelativeResolvent.logTest z z₀ x))
  derivative_bounds : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane a →
    ∃ B : Fin 3 → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ n z, z ∈ K → ∀ sigma : ℝ, |sigma| ≤ a → ∀ j : Fin 3,
        Integrable (fun x : ℝ => Real.exp (sigma*x) *
          ‖iteratedDeriv j.val (test n z) x‖) ∧
        weightedDerivativeMass sigma j.val (test n z) ≤ B j

structure SpectralDomination (ι : Type*) (transform : ℕ → ι → ℂ)
    (multiplicity : ι → ℕ) where
  bound : ι → ℝ
  summable_bound : Summable bound
  uniform_bound : ∀ n i, ‖(multiplicity i : ℂ) * transform n i‖ ≤ bound i

end RHConnections.AnalyticObligations
