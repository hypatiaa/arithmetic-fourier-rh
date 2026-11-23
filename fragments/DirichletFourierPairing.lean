import Verified
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

open MeasureTheory ArithmeticFunction
noncomputable section
namespace RHConnections.DirichletFourierPairing
open FourierTestInversion DirichletGeometricLimit DirichletCharacter
open scoped LSeries.notation
variable {N : ℕ} (χ : DirichletCharacter ℂ N)

private abbrev primeCoeff : ℕ → ℂ := ↗χ * ↗vonMangoldt

private theorem prime_shift_term (m : ℕ) (z : ℂ) :
    halfWeight χ m * Complex.exp (-z * (Real.log m : ℂ)) =
      LSeries.term (primeCoeff χ) (z+1/2) m := by
  by_cases hm : m = 0
  · subst m
    simp [halfWeight]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  simp only [halfWeight, LSeries.term_of_ne_zero hm, Complex.cpow_def_of_ne_zero hm',
    div_eq_mul_inv, ← Complex.exp_neg, mul_assoc, ← Complex.exp_add, ← Complex.natCast_log]
  congr 2 <;> ring

private def primeAmplitude (m : ℕ) := LSeries.term (primeCoeff χ) (3/2) m

private theorem primeAmplitude_eq (m : ℕ) :
    primeAmplitude χ m = halfWeight χ m * Complex.exp (-(Real.log m : ℂ)) := by
  have h := prime_shift_term χ m 1
  rw [show (1 : ℂ)+1/2=3/2 by norm_num, neg_one_mul] at h
  simpa only [primeAmplitude] using h.symm

private theorem primeProbe_term (m : ℕ) (v : ℝ) :
    LSeries.term (primeCoeff χ) (verticalProbe v+1/2) m =
      primeAmplitude χ m * phase v (Real.log m) := by
  rw [← prime_shift_term χ, verticalProbe_exp, primeAmplitude_eq χ, mul_assoc]

private theorem primeProbe_re (v : ℝ) : 1 < (verticalProbe v+1/2).re := by
  norm_num [verticalProbe, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re]

private theorem primeProbe_series (v : ℝ) :
    (-deriv (LSeries ↗χ) (verticalProbe v+1/2)/(LSeries ↗χ) (verticalProbe v+1/2)) +
      deriv (LSeries ↗χ) (3/2)/(LSeries ↗χ) (3/2) =
    ∑' m : ℕ, primeAmplitude χ m * (phase v (Real.log m) - 1) := by
  have h₀ : 1 < (3/2 : ℂ).re := by norm_num
  have h₁ := primeProbe_re v
  have hs : Summable (LSeries.term (primeCoeff χ) (verticalProbe v+1/2)) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h₁
  have hs₀ : Summable (LSeries.term (primeCoeff χ) (3/2)) := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h₀
  have h := hs.tsum_sub hs₀
  change (∑' m : ℕ, (LSeries.term (primeCoeff χ) (verticalProbe v+1/2) m - primeAmplitude χ m)) =
    LSeries (primeCoeff χ) (verticalProbe v+1/2) - LSeries (primeCoeff χ) (3/2) at h
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ h₁,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ h₀] at h
  calc
    _ = _ := (show (-deriv (LSeries ↗χ) (verticalProbe v+1/2)/(LSeries ↗χ) (verticalProbe v+1/2)) +
        deriv (LSeries ↗χ) (3/2)/(LSeries ↗χ) (3/2) =
        (-deriv (LSeries ↗χ) (verticalProbe v+1/2)/(LSeries ↗χ) (verticalProbe v+1/2)) -
        (-deriv (LSeries ↗χ) (3/2)/(LSeries ↗χ) (3/2)) by ring)
    _ = _ := h.symm
    _ = _ := tsum_congr fun m => by rw [primeProbe_term χ]; ring

theorem twisted_prime_fourier_pairing {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hzero : f 0 = 0) :
    Integrable (fun v : ℝ => testFourier f v *
      ((-deriv (LSeries ↗χ) (verticalProbe v+1/2)/(LSeries ↗χ) (verticalProbe v+1/2)) +
        deriv (LSeries ↗χ) (3/2)/(LSeries ↗χ) (3/2))) ∧
    (∫ v : ℝ, testFourier f v *
      ((-deriv (LSeries ↗χ) (verticalProbe v+1/2)/(LSeries ↗χ) (verticalProbe v+1/2)) +
        deriv (LSeries ↗χ) (3/2)/(LSeries ↗χ) (3/2))) =
      ∑' m : ℕ, halfWeight χ m * f (Real.log m) := by
  let F := testFourier f
  let G (m : ℕ) (v : ℝ) := primeAmplitude χ m * (F v * (phase v (Real.log m)-1))
  have hiF := testFourier_integrable hf hc
  have hi (m : ℕ) : Integrable (G m) := by
    have h := (testFourier_phase_integrable hf hc (Real.log m)).sub hiF
    apply (h.const_mul (primeAmplitude χ m)).congr
    exact ae_of_all _ fun v => by dsimp [G,F]; ring
  have hcoef : Summable (primeAmplitude χ) := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by norm_num : 1 < (3/2 : ℂ).re)
  have hsum : Summable (fun m : ℕ => ∫ v : ℝ, ‖G m v‖) := by
    apply (hcoef.norm.mul_right (2 * ∫ v : ℝ, ‖F v‖)).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    intro m
    calc
      _ ≤ ∫ v : ℝ, (‖primeAmplitude χ m‖*2)*‖F v‖ := by
        apply integral_mono (hi m).norm (hiF.norm.const_mul _)
        intro v
        have hp : ‖phase v (Real.log m)-1‖ ≤ 2 := by
          simpa only [phase_norm, norm_one, one_add_one_eq_two] using (norm_sub_le (phase v (Real.log m)) (1:ℂ))
        simp only [G, norm_mul]
        calc
          _ ≤ ‖primeAmplitude χ m‖ * (‖F v‖*2) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) (norm_nonneg _)
          _ = _ := by ring
      _ = _ := by rw [integral_const_mul]; ring
  have heq (v : ℝ) : testFourier f v *
      ((-deriv (LSeries ↗χ) (verticalProbe v+1/2)/(LSeries ↗χ) (verticalProbe v+1/2)) +
        deriv (LSeries ↗χ) (3/2)/(LSeries ↗χ) (3/2)) = ∑' m : ℕ, G m v := by
    rw [primeProbe_series χ, ← tsum_mul_left]
    exact tsum_congr fun m => by dsimp [G,F]; ring
  constructor
  · simp_rw [heq]
    apply (hiF.norm.const_mul (2 * ∑' m, ‖primeAmplitude χ m‖)).mono'
      (AEStronglyMeasurable.tsum fun m => (hi m).aestronglyMeasurable)
    exact ae_of_all _ fun v => by
      have hM := hcoef.norm.mul_right (2 * ‖F v‖)
      have hp (m : ℕ) : ‖G m v‖ ≤ ‖primeAmplitude χ m‖*(2*‖F v‖) := by
        have hh : ‖phase v (Real.log m)-1‖ ≤ 2 := by
          simpa only [phase_norm, norm_one, one_add_one_eq_two] using norm_sub_le (phase v (Real.log m)) (1:ℂ)
        simp only [G, norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [mul_comm 2]
        exact mul_le_mul_of_nonneg_left hh (norm_nonneg _)
      have hN := hM.of_nonneg_of_le (fun m => norm_nonneg (G m v)) hp
      calc
        _ ≤ ∑' m, ‖G m v‖ := norm_tsum_le_tsum_norm hN
        _ ≤ ∑' m, ‖primeAmplitude χ m‖*(2*‖F v‖) := hN.tsum_le_tsum hp hM
        _ = _ := by rw [tsum_mul_right]; change _ = (2 * ∑' m, ‖primeAmplitude χ m‖) * ‖F v‖; ring
  · calc
      _ = ∫ v : ℝ, ∑' m : ℕ, G m v := integral_congr_ae (ae_of_all _ heq)
      _ = ∑' m : ℕ, ∫ v : ℝ, G m v := (integral_tsum_of_summable_integral_norm hi hsum).symm
      _ = _ := by
        apply tsum_congr
        intro m
        change (∫ v : ℝ, primeAmplitude χ m * (testFourier f v * (phase v (Real.log m)-1))) = _
        rw [integral_const_mul, testFourier_compensated_inversion hf hc hzero, primeAmplitude_eq χ]
        simp only [twistedTest, Complex.real_smul, Complex.ofReal_exp]
        rw [mul_assoc, ← mul_assoc (Complex.exp _) (Complex.exp _), ← Complex.exp_add, neg_add_cancel,
          Complex.exp_zero, one_mul]

#print axioms twisted_prime_fourier_pairing
theorem LFunction_prime_fourier_pairing [NeZero N] {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hzero : f 0 = 0) :
    Integrable (fun v : ℝ => testFourier f v *
      (logDeriv (LFunction χ) (3/2) - logDeriv (LFunction χ) (verticalProbe v+1/2))) ∧
    (∫ v : ℝ, testFourier f v *
      (logDeriv (LFunction χ) (3/2) - logDeriv (LFunction χ) (verticalProbe v+1/2))) =
      ∑' m : ℕ, halfWeight χ m * f (Real.log m) := by
  have hD (s : ℂ) (hs : 1 < s.re) : logDeriv (LFunction χ) s =
      deriv (LSeries ↗χ) s / LSeries ↗χ s := by
    rw [logDeriv_apply, deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
  have heq (v : ℝ) : logDeriv (LFunction χ) (3/2) - logDeriv (LFunction χ) (verticalProbe v+1/2) =
      -deriv (LSeries ↗χ) (verticalProbe v+1/2) / LSeries ↗χ (verticalProbe v+1/2) +
      deriv (LSeries ↗χ) (3/2) / LSeries ↗χ (3/2) := by
    rw [hD _ (by norm_num), hD _ (primeProbe_re v)]
    ring
  simp_rw [heq]
  exact twisted_prime_fourier_pairing χ hf hc hzero
end RHConnections.DirichletFourierPairing
