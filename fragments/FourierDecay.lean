import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped FourierTransform
noncomputable section
namespace RHConnections.FourierDecay

theorem uniform_quadratic_decay {ι : Type*} (f : ι → ℝ → ℂ) (M₀ M₂ : ℝ)
    (hs : ∀ i, ContDiff ℝ 2 (f i))
    (hi : ∀ i, ∀ k ≤ 2, Integrable (iteratedDeriv k (f i)))
    (h₀ : ∀ i, (∫ x : ℝ, ‖f i x‖) ≤ M₀)
    (h₂ : ∀ i, (∫ x : ℝ, ‖iteratedDeriv 2 (f i) x‖) ≤ M₂) (i : ι) (u : ℝ) :
    ‖𝓕 (f i) u‖ ≤ (M₀+(4*Real.pi^2)⁻¹*M₂)/(1+u^2) := by
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 1+u^2)).mpr
  have h := Real.one_add_sq_mul_norm_fourier_le (hs i) (hi i) u
  have hbound := add_le_add (h₀ i)
    (mul_le_mul_of_nonneg_left (h₂ i) (by positivity : (0:ℝ) ≤ (4*Real.pi^2)⁻¹))
  simpa only [mul_comm] using h.trans hbound

def angularTransform (f : ℝ → ℂ) (tau : ℝ) : ℂ := 𝓕 f (-tau/(2*Real.pi))

theorem angular_integral (f : ℝ → ℂ) (tau : ℝ) :
    angularTransform f tau = ∫ x : ℝ, Complex.exp ((tau*x : ℝ)*Complex.I)*f x := by
  unfold angularTransform
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  have hp : -2*Real.pi*x*(-tau/(2*Real.pi)) = tau*x := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [hp]
  rfl

#print axioms uniform_quadratic_decay
#print axioms angular_integral
end RHConnections.FourierDecay
