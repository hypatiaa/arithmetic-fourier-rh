import Verified
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory
open scoped ContDiff

namespace RHConnections.Mollifier

theorem iteratedDeriv_hasCompactSupport (j : ℕ) {h : ℝ → ℂ}
    (hc : HasCompactSupport h) : HasCompactSupport (iteratedDeriv j h) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem iteratedDeriv_integrable (j : ℕ) {h : ℝ → ℂ}
    (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    Integrable (iteratedDeriv j h) :=
  (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport
    (iteratedDeriv_hasCompactSupport j hc)

theorem fullCandidate_iteratedDeriv_hasCompactSupport (j n : ℕ) (z z₀ : ℂ) :
    HasCompactSupport (iteratedDeriv j (fullCandidate n z z₀)) :=
  iteratedDeriv_hasCompactSupport j (fullCandidate_compact n z z₀)

theorem fullCandidate_iteratedDeriv_integrable (j n : ℕ) (z z₀ : ℂ) :
    Integrable (iteratedDeriv j (fullCandidate n z z₀)) :=
  iteratedDeriv_integrable j (fullCandidate_smooth n z z₀) (fullCandidate_compact n z z₀)

theorem fullCandidate_weighted_iteratedDeriv_integrable (σ : ℝ) (j n : ℕ) (z z₀ : ℂ) :
    Integrable (fun x : ℝ => Real.exp (σ * x) * ‖iteratedDeriv j (fullCandidate n z z₀) x‖) := by
  have hderiv : Continuous (iteratedDeriv j (fullCandidate n z z₀)) :=
    (fullCandidate_smooth n z z₀).continuous_iteratedDeriv j (by simp)
  have hweight : Continuous (fun x : ℝ => Real.exp (σ * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact (hweight.mul hderiv.norm).integrable_of_hasCompactSupport
    (fullCandidate_iteratedDeriv_hasCompactSupport j n z z₀).norm.mul_left

#print axioms iteratedDeriv_hasCompactSupport
#print axioms iteratedDeriv_integrable
#print axioms fullCandidate_iteratedDeriv_hasCompactSupport
#print axioms fullCandidate_iteratedDeriv_integrable
#print axioms fullCandidate_weighted_iteratedDeriv_integrable

end RHConnections.Mollifier
