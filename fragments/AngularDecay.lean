import Verified
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory

namespace RHConnections.FourierDecay

theorem uniform_angular_quadratic_decay {ι : Type*} (f : ι → ℝ → ℂ) (M₀ M₂ : ℝ)
    (hs : ∀ i, ContDiff ℝ 2 (f i))
    (hi : ∀ i, ∀ k ≤ 2, Integrable (iteratedDeriv k (f i)))
    (h₀ : ∀ i, (∫ x : ℝ, ‖f i x‖) ≤ M₀)
    (h₂ : ∀ i, (∫ x : ℝ, ‖iteratedDeriv 2 (f i) x‖) ≤ M₂) (i : ι) (tau : ℝ) :
    ‖angularTransform (f i) tau‖ ≤ (4 * Real.pi ^ 2 * M₀ + M₂) / (1 + tau ^ 2) := by
  let p : ℝ := 4 * Real.pi ^ 2
  let u : ℝ := -tau / (2 * Real.pi)
  have hp : 1 ≤ p := by
    dsimp [p]
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  have hp₀ : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hsq : p * u ^ 2 = tau ^ 2 := by
    dsimp [p, u]
    field_simp [Real.pi_ne_zero] <;> ring
  have hfreq : 1 + tau ^ 2 ≤ p * (1 + u ^ 2) := by
    rw [mul_add, mul_one, hsq]
    exact add_le_add hp le_rfl
  have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + u ^ 2)).mp
    (uniform_quadratic_decay f M₀ M₂ hs hi h₀ h₂ i u)
  change ‖angularTransform (f i) tau‖ * (1 + u ^ 2) ≤ M₀ + p⁻¹ * M₂ at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + tau ^ 2)).mpr
  change ‖angularTransform (f i) tau‖ * (1 + tau ^ 2) ≤ p * M₀ + M₂
  calc
    ‖angularTransform (f i) tau‖ * (1 + tau ^ 2) ≤
        ‖angularTransform (f i) tau‖ * (p * (1 + u ^ 2)) :=
      mul_le_mul_of_nonneg_left hfreq (norm_nonneg _)
    _ = p * (‖angularTransform (f i) tau‖ * (1 + u ^ 2)) := by ac_rfl
    _ ≤ p * (M₀ + p⁻¹ * M₂) := mul_le_mul_of_nonneg_left h hp₀.le
    _ = p * M₀ + M₂ := by
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hp₀.ne', one_mul]

#print axioms uniform_angular_quadratic_decay

end RHConnections.FourierDecay
