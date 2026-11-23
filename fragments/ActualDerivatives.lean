import Verified
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.IntervalCases

open MeasureTheory ContinuousLinearMap
open scoped Convolution

noncomputable section
namespace RHConnections.Mollifier
open RelativeResolvent ConvolutionTransfer WeightedBulk WeightedConvolution

def smoothDelayedEndpoint (n : ℕ) (z z₀ : ℂ) (x : ℝ) : ℂ :=
  ((bump n).normed volume (x - 2 * epsilon n) : ℂ) * (z₀ - z)

theorem smoothDelayed_derivatives (n : ℕ) (z z₀ : ℂ) (x : ℝ) :
    deriv (smoothDelayed n z z₀) x = smoothedBulk n 1 z z₀ x ∧
      deriv (deriv (smoothDelayed n z z₀)) x =
        smoothDelayedEndpoint n z z₀ x + smoothedBulk n 2 z z₀ x := by
  let f : ℝ → ℂ := (bump n).normed volume ⋆[lsmul ℝ ℝ, volume] logTest z z₀
  have hf : smoothDelayed n z z₀ = fun y => f (y - 2 * epsilon n) := rfl
  have hshift (g : ℝ → ℂ) :
      deriv (fun y => g (y - 2 * epsilon n)) = fun y => deriv g (y - 2 * epsilon n) :=
    funext fun y => deriv_comp_sub_const g (2 * epsilon n) y
  have hconv := deriv_convolution_logTest (x - 2 * epsilon n) z z₀
    ((bump n).hasCompactSupport_normed (μ := volume)) (bump n).contDiff_normed
  constructor
  · rw [hf, hshift f]
    exact hconv.1
  · rw [hf, hshift f, hshift (deriv f)]
    exact hconv.2

theorem smoothDelayedEndpoint_weighted_bound (n : ℕ) (z z₀ : ℂ) {sigma a : ℝ}
    (ha : 0 ≤ a) (hsigma : |sigma| ≤ a) :
    Integrable (fun x : ℝ => Real.exp (sigma * x) * ‖smoothDelayedEndpoint n z z₀ x‖) ∧
      (∫ x : ℝ, Real.exp (sigma * x) * ‖smoothDelayedEndpoint n z z₀ x‖) ≤
        Real.exp (3 * a) * ‖z₀ - z‖ := by
  let g : ℝ → ℂ := fun x => ((bump n).normed volume x : ℂ) * (z₀ - z)
  have hg : Continuous g :=
    (Complex.continuous_ofReal.comp (bump n).continuous_normed).mul continuous_const
  have hexp : Continuous (fun x : ℝ => Real.exp (sigma * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hwg : Continuous (weighted sigma g) := hexp.smul hg
  have hn (x : ℝ) : ‖g x‖ = (bump n).normed volume x * ‖z₀ - z‖ := by
    change ‖((bump n).normed volume x : ℂ) * (z₀ - z)‖ = _
    rw [norm_mul, Complex.norm_of_nonneg ((bump n).nonneg_normed x)]
  obtain ⟨hki, hkm⟩ := bump_weighted_mass n ha hsigma
  have hi : Integrable (weighted sigma g) := by
    apply (integrable_norm_iff hwg.aestronglyMeasurable).mp
    simpa only [norm_weighted, hn, ← mul_assoc] using hki.mul_const ‖z₀ - z‖
  have hm : (∫ x : ℝ, Real.exp (sigma * x) * ‖g x‖) ≤ Real.exp a * ‖z₀ - z‖ := by
    simp only [hn, ← mul_assoc, integral_mul_const]
    exact mul_le_mul_of_nonneg_right hkm (norm_nonneg _)
  have heps : epsilon n ≤ 1 := by
    unfold epsilon
    exact div_le_self zero_le_one (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hdelay : sigma * (2 * epsilon n) ≤ 2 * a := calc
    _ ≤ a * (2 * epsilon n) := mul_le_mul_of_nonneg_right
      ((le_abs_self sigma).trans hsigma) (mul_nonneg (by norm_num) (epsilon_pos n).le)
    _ ≤ a * 2 := mul_le_mul_of_nonneg_left (by linarith) ha
    _ = _ := mul_comm _ _
  refine ⟨?_, ?_⟩
  · simpa only [norm_weighted, smoothDelayedEndpoint, g] using
      (weighted_shift_integrable sigma (2 * epsilon n) g hi).norm
  · change (∫ x : ℝ, Real.exp (sigma * x) * ‖g (x - 2 * epsilon n)‖) ≤ _
    rw [weighted_shift_mass]
    calc
      _ ≤ Real.exp (sigma * (2 * epsilon n)) * (Real.exp a * ‖z₀ - z‖) :=
        mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
      _ = Real.exp (sigma * (2 * epsilon n) + a) * ‖z₀ - z‖ := by
        rw [← mul_assoc, ← Real.exp_add]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (norm_nonneg _)

theorem smoothDelayed_weighted_iteratedDeriv_bound (n : ℕ) (z z₀ : ℂ) {sigma beta a L : ℝ}
    (hz : beta ≤ z.re) (hz₀ : beta ≤ z₀.re) (hgap : a < beta)
    (ha : 0 ≤ a) (hsigma : |sigma| ≤ a) (hLz : ‖z‖ ≤ L) (hLz₀ : ‖z₀‖ ≤ L)
    (j : ℕ) (hj : j ≤ 2) :
    Integrable (fun x : ℝ => Real.exp (sigma * x) * ‖iteratedDeriv j (smoothDelayed n z z₀) x‖) ∧
      (∫ x : ℝ, Real.exp (sigma * x) * ‖iteratedDeriv j (smoothDelayed n z z₀) x‖) ≤
        Real.exp (3 * a) * (2 * L^j / (beta - a) + if j = 2 then 2 * L else 0) := by
  interval_cases j
  · rw [iteratedDeriv_zero, ← smoothedBulk_zero n z z₀, if_neg (by decide : (0 : ℕ) ≠ 2), add_zero]
    exact ⟨smoothedBulk_weighted_integrable n 0 z z₀ hz hz₀ hgap ha hsigma,
      smoothedBulk_mass_bound n 0 z z₀ hz hz₀ hgap ha hsigma hLz hLz₀⟩
  · have hfirst : deriv (smoothDelayed n z z₀) = smoothedBulk n 1 z z₀ :=
      funext fun x => (smoothDelayed_derivatives n z z₀ x).1
    rw [iteratedDeriv_one, hfirst, if_neg (by decide : (1 : ℕ) ≠ 2), add_zero]
    exact ⟨smoothedBulk_weighted_integrable n 1 z z₀ hz hz₀ hgap ha hsigma,
      smoothedBulk_mass_bound n 1 z z₀ hz hz₀ hgap ha hsigma hLz hLz₀⟩
  · rw [if_pos rfl]
    let weight (x : ℝ) := Real.exp (sigma * x)
    let actual (x : ℝ) := weight x * ‖iteratedDeriv 2 (smoothDelayed n z z₀) x‖
    let endpoint (x : ℝ) := weight x * ‖smoothDelayedEndpoint n z z₀ x‖
    let bulkNorm (x : ℝ) := weight x * ‖smoothedBulk n 2 z z₀ x‖
    have hsecond (x : ℝ) : iteratedDeriv 2 (smoothDelayed n z z₀) x =
        smoothDelayedEndpoint n z z₀ x + smoothedBulk n 2 z z₀ x := by
      simpa only [iteratedDeriv_succ (n := 1), iteratedDeriv_one] using
        (smoothDelayed_derivatives n z z₀ x).2
    have hpointwise (x : ℝ) : actual x ≤ endpoint x + bulkNorm x := by
      dsimp only [actual, endpoint, bulkNorm]
      rw [hsecond, ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
    obtain ⟨hei, hem⟩ := smoothDelayedEndpoint_weighted_bound n z z₀ ha hsigma
    have hbi := smoothedBulk_weighted_integrable n 2 z z₀ hz hz₀ hgap ha hsigma
    have hbm := smoothedBulk_mass_bound n 2 z z₀ hz hz₀ hgap ha hsigma hLz hLz₀
    have hw : Continuous weight := Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hcd : Continuous (iteratedDeriv 2 (smoothDelayed n z z₀)) :=
      (smoothDelayed_smooth n z z₀).continuous_iteratedDeriv 2 (by simp)
    have hint : Integrable actual := by
      apply (hei.add hbi).mono_nonneg (hw.mul hcd.norm).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
      · exact Filter.Eventually.of_forall hpointwise
    have hdelta : ‖z₀ - z‖ ≤ 2 * L := by
      calc
        _ ≤ ‖z₀‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ L + L := add_le_add hLz₀ hLz
        _ = _ := by ring
    refine ⟨hint, ?_⟩
    calc
      _ ≤ ∫ x : ℝ, endpoint x + bulkNorm x := integral_mono hint (hei.add hbi) hpointwise
      _ = (∫ x : ℝ, endpoint x) + (∫ x : ℝ, bulkNorm x) := integral_add hei hbi
      _ ≤ Real.exp (3 * a) * (2 * L) + Real.exp (3 * a) * (2 * L^2 / (beta - a)) :=
        add_le_add (hem.trans (mul_le_mul_of_nonneg_left hdelta (Real.exp_pos _).le)) hbm
      _ = _ := by ring

#print axioms smoothDelayed_derivatives
#print axioms smoothDelayedEndpoint_weighted_bound
#print axioms smoothDelayed_weighted_iteratedDeriv_bound

end RHConnections.Mollifier
