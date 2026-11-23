import Verified

open MeasureTheory ContinuousLinearMap
open scoped Convolution
noncomputable section
namespace RHConnections.Mollifier
open WeightedBulk WeightedConvolution RelativeResolvent

def smoothedBulk (n j : ℕ) (z z₀ : ℂ) (x : ℝ) : ℂ :=
  ((bump n).normed volume ⋆[lsmul ℝ ℝ, volume] bulk j z z₀) (x-2*epsilon n)

theorem bulk_zero (z z₀ : ℂ) : bulk 0 z z₀ = logTest z z₀ := by
  funext x
  simp only [bulk, positiveFormula, pow_zero, one_mul, logTest]

theorem smoothedBulk_zero (n : ℕ) (z z₀ : ℂ) : smoothedBulk n 0 z z₀ = smoothDelayed n z z₀ := by
  unfold smoothedBulk smoothDelayed
  rw [bulk_zero]

theorem smoothedBulk_weighted_integrable (n j : ℕ) (z z₀ : ℂ) {sigma beta a : ℝ}
    (hz : beta ≤ z.re) (hz₀ : beta ≤ z₀.re) (hgap : a < beta)
    (ha : 0 ≤ a) (hsigma : |sigma| ≤ a) :
    Integrable (fun x : ℝ => Real.exp (sigma*x)*‖smoothedBulk n j z z₀ x‖) := by
  have hs : sigma < beta := lt_of_le_of_lt ((le_abs_self sigma).trans hsigma) hgap
  have hk := (bump_weighted_mass n ha hsigma).1
  have hg := weighted_bulk_complex_integrable j z z₀ hz hz₀ hs
  have hc := weighted_convolution_integrable sigma ((bump n).normed volume) (bulk j z z₀) hk hg
  have hd := weighted_shift_integrable sigma (2*epsilon n)
    ((bump n).normed volume ⋆[lsmul ℝ ℝ, volume] bulk j z z₀) hc
  simpa only [norm_weighted, smoothedBulk] using hd.norm

theorem smoothedBulk_mass_bound (n j : ℕ) (z z₀ : ℂ) {sigma beta a L : ℝ}
    (hz : beta ≤ z.re) (hz₀ : beta ≤ z₀.re) (hgap : a < beta)
    (ha : 0 ≤ a) (hsigma : |sigma| ≤ a) (hLz : ‖z‖ ≤ L) (hLz₀ : ‖z₀‖ ≤ L) :
    (∫ x : ℝ, Real.exp (sigma*x)*‖smoothedBulk n j z z₀ x‖) ≤
      Real.exp (3*a)*(2*L^j/(beta-a)) := by
  have hs : sigma < beta := lt_of_le_of_lt ((le_abs_self sigma).trans hsigma) hgap
  obtain ⟨hki, hkm⟩ := bump_weighted_mass n ha hsigma
  have hgi := weighted_bulk_complex_integrable j z z₀ hz hz₀ hs
  have hgm := weighted_bulk_uniform j z z₀ hz hz₀ hgap hsigma hLz hLz₀
  have hconv := weighted_convolution_mass_bound sigma ((bump n).normed volume)
    (bulk j z z₀) (bump n).nonneg_normed hki hgi
  have hmass : (∫ x : ℝ, Real.exp (sigma*x)*
      ‖((bump n).normed volume ⋆[lsmul ℝ ℝ, volume] bulk j z z₀) x‖) ≤
      Real.exp a*(2*L^j/(beta-a)) :=
    hconv.trans (mul_le_mul hkm hgm
      (integral_nonneg (fun x => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)))
      (Real.exp_pos _).le)
  have heps : epsilon n ≤ 1 := by
    unfold epsilon
    exact div_le_self zero_le_one (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have heps0 : 0 ≤ epsilon n := (epsilon_pos n).le
  have hsx : sigma*(2*epsilon n) ≤ 2*a := by
    calc
      _ ≤ a*(2*epsilon n) := mul_le_mul_of_nonneg_right
        ((le_abs_self sigma).trans hsigma) (by positivity)
      _ ≤ a*2 := mul_le_mul_of_nonneg_left (by linarith) ha
      _ = _ := by ring
  have hL : 0 ≤ L := (norm_nonneg z).trans hLz
  calc
    _ = Real.exp (sigma*(2*epsilon n))*(∫ x : ℝ, Real.exp (sigma*x)*
        ‖((bump n).normed volume ⋆[lsmul ℝ ℝ, volume] bulk j z z₀) x‖) :=
      weighted_shift_mass _ _ _
    _ ≤ Real.exp (sigma*(2*epsilon n))*(Real.exp a*(2*L^j/(beta-a))) :=
      mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
    _ = Real.exp (sigma*(2*epsilon n)+a)*(2*L^j/(beta-a)) := by
      rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)

#print axioms bulk_zero
#print axioms smoothedBulk_zero
#print axioms smoothedBulk_weighted_integrable
#print axioms smoothedBulk_mass_bound
end RHConnections.Mollifier
