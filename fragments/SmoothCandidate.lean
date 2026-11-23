import RelativeResolvent
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory
noncomputable section
namespace RHConnections.SmoothCandidate
open RelativeResolvent

def delayed (z z₀ : ℂ) (rho : ℝ → ℂ) (epsilon x : ℝ) : ℂ :=
  ∫ y : ℝ, logTest z z₀ y * rho (x - 2*epsilon - y)

def candidate (z z₀ : ℂ) (rho kappa : ℝ → ℂ) (epsilon R x : ℝ) : ℂ :=
  kappa (x/R) * delayed z z₀ rho epsilon x

theorem delayed_vanishes_left (z z₀ : ℂ) (rho : ℝ → ℂ)
    {epsilon x : ℝ} (hSupport : ∀ t, epsilon < |t| → rho t = 0)
    (hx : x ≤ epsilon) : delayed z z₀ rho epsilon x = 0 := by
  unfold delayed
  have hi : (fun y : ℝ => logTest z z₀ y * rho (x-2*epsilon-y)) = 0 := by
    funext y
    by_cases hy : y ≤ 0
    · simp [vanishes_left z z₀ hy]
    · have hypos : 0 < y := lt_of_not_ge hy
      have ht : epsilon < |x-2*epsilon-y| := by
        have hh := neg_le_abs (x-2*epsilon-y)
        linarith
      simp [hSupport _ ht]
  rw [hi]
  simp

theorem candidate_vanishes_left (z z₀ : ℂ) (rho kappa : ℝ → ℂ)
    {epsilon R x : ℝ} (hSupport : ∀ t, epsilon < |t| → rho t = 0)
    (hx : x ≤ epsilon) : candidate z z₀ rho kappa epsilon R x = 0 := by
  simp [candidate, delayed_vanishes_left z z₀ rho hSupport hx]

theorem candidate_norm_one (z z₀ : ℂ) (rho kappa : ℝ → ℂ)
    {epsilon R : ℝ} (hepsilon : 0 < epsilon)
    (hSupport : ∀ t, epsilon < |t| → rho t = 0) :
    candidate z z₀ rho kappa epsilon R (Real.log 1) = 0 := by
  simpa using candidate_vanishes_left z z₀ rho kappa
    (R := R) hSupport hepsilon.le

theorem candidate_vanishes_right (z z₀ : ℂ) (rho kappa : ℝ → ℂ)
    {epsilon R x : ℝ} (hR : 0 < R)
    (hSupport : ∀ t, 2 < t → kappa t = 0) (hx : 2*R < x) :
    candidate z z₀ rho kappa epsilon R x = 0 := by
  have ht : 2 < x/R := (lt_div_iff₀ hR).mpr hx
  simp [candidate, hSupport _ ht]

#print axioms delayed_vanishes_left
#print axioms candidate_vanishes_left
#print axioms candidate_norm_one
#print axioms candidate_vanishes_right
end RHConnections.SmoothCandidate
