import Verified
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution

noncomputable section
namespace RHConnections.Mollifier
open RelativeResolvent

private theorem logTest_eq_clamped (z z₀ : ℂ) (u : ℝ) :
    logTest z z₀ u = Complex.exp (-z * ((max 0 u : ℝ) : ℂ)) -
      Complex.exp (-z₀ * ((max 0 u : ℝ) : ℂ)) := by
  by_cases hu : 0 < u
  · simp [logTest, hu, max_eq_right hu.le]
  · simp [logTest, hu, max_eq_left (le_of_not_gt hu)]

theorem smoothDelayed_parameter_hasDerivAt (n : ℕ) (z z₀ : ℂ) (x : ℝ) :
    HasDerivAt (fun w : ℂ => smoothDelayed n w z₀ x)
      (∫ y : ℝ, (bump n).normed volume y •
        (-((max 0 (x - 2 * epsilon n - y) : ℝ) : ℂ) *
          Complex.exp (-z * ((max 0 (x - 2 * epsilon n - y) : ℝ) : ℂ)))) z := by
  let k : ℝ → ℝ := (bump n).normed volume
  let t (y : ℝ) : ℝ := max 0 (x - 2 * epsilon n - y)
  let F (w : ℂ) (y : ℝ) : ℂ :=
    k y • (Complex.exp (-w * (t y : ℂ)) - Complex.exp (-z₀ * (t y : ℂ)))
  let G (w : ℂ) (y : ℝ) : ℂ := k y • (-(t y : ℂ) * Complex.exp (-w * (t y : ℂ)))
  have hkc : Continuous k := (bump n).continuous_normed
  have hks : HasCompactSupport k := (bump n).hasCompactSupport_normed
  have htc : Continuous (fun y : ℝ => (t y : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.sub continuous_id))
  have hEc (w : ℂ) : Continuous (fun y : ℝ => Complex.exp (-w * (t y : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul htc)
  have hFc (w : ℂ) : Continuous (F w) := hkc.smul ((hEc w).sub (hEc z₀))
  have hGc (w : ℂ) : Continuous (G w) := hkc.smul (htc.neg.mul (hEc w))
  have hdiff (y : ℝ) (w : ℂ) : HasDerivAt (fun r : ℂ => F r y) (G w y) w := by
    have harg : HasDerivAt (fun r : ℂ => -r * (t y : ℂ)) (-(t y : ℂ)) w := by
      have hmul : HasDerivAt (fun r : ℂ => r * (t y : ℂ)) (t y : ℂ) w := by
        simpa only [id_eq, one_mul] using (hasDerivAt_id w).mul_const (t y : ℂ)
      simp only [neg_mul]
      exact hmul.neg
    have hvalue : HasDerivAt
        (fun r : ℂ => Complex.exp (-r * (t y : ℂ)) - Complex.exp (-z₀ * (t y : ℂ)))
        (-(t y : ℂ) * Complex.exp (-w * (t y : ℂ))) w := by
      simpa only [mul_comm] using harg.cexp.sub_const (Complex.exp (-z₀ * (t y : ℂ)))
    simpa only [F, G, Complex.real_smul] using hvalue.const_mul (k y : ℂ)
  let C : ℝ := |x - 2 * epsilon n| + epsilon n
  let D : ℝ := ‖z‖ + 1
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (epsilon_pos n).le
  have hD : 0 ≤ D := add_nonneg (norm_nonneg _) zero_le_one
  have hmajorant (y : ℝ) (w : ℂ) (hw : w ∈ Metric.ball z 1) :
      ‖G w y‖ ≤ (C * Real.exp (D * C)) * k y := by
    by_cases hy : |y| ≤ epsilon n
    · have ht0 : 0 ≤ t y := le_max_left _ _
      have htC : t y ≤ C := by
        apply max_le hC
        dsimp only [C]
        linarith [le_abs_self (x - 2 * epsilon n), neg_le_abs y]
      have hwD : ‖w‖ ≤ D := by
        have hdist : ‖w - z‖ < 1 := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hw
        calc
          ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ D := by dsimp only [D]; linarith
      have he : ‖Complex.exp (-w * (t y : ℂ))‖ ≤ Real.exp (D * C) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ ‖-w * (t y : ℂ)‖ := Complex.re_le_norm _
          _ = ‖w‖ * t y := by rw [norm_mul, norm_neg, Complex.norm_of_nonneg ht0]
          _ ≤ D * C := mul_le_mul hwD htC ht0 hD
      have hk0 : 0 ≤ k y := (bump n).nonneg_normed y
      dsimp only [G]
      rw [norm_smul, Real.norm_of_nonneg hk0, norm_mul, norm_neg, Complex.norm_of_nonneg ht0,
        mul_comm (C * Real.exp (D * C)) (k y)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul htC he (norm_nonneg _) hC) hk0
    · have hb : bump n y = 0 := (bump n).zero_of_le_dist (by
        simpa only [bump, Real.dist_eq, sub_zero] using (lt_of_not_ge hy).le)
      have hk0 : k y = 0 := by simp [k, ContDiffBump.normed_def, hb]
      simp [G, hk0]
  have hmajorant_int : Integrable (fun y : ℝ => (C * Real.exp (D * C)) * k y) :=
    ((bump n).integrable_normed (μ := volume)).const_mul _
  have hFint : Integrable (F z) := (hFc z).integrable_of_hasCompactSupport hks.smul_right
  have hi : HasDerivAt (fun w : ℂ => ∫ y : ℝ, F w y) (∫ y : ℝ, G z y) z :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := G)
      (Metric.ball_mem_nhds z zero_lt_one)
      (Eventually.of_forall fun w => (hFc w).aestronglyMeasurable) hFint (hGc z).aestronglyMeasurable
      (Eventually.of_forall hmajorant) hmajorant_int
      (Eventually.of_forall fun y w _ => hdiff y w)).2
  have hEq : (fun w : ℂ => smoothDelayed n w z₀ x) = (fun w : ℂ => ∫ y : ℝ, F w y) := by
    funext w
    unfold smoothDelayed
    rw [convolution_def]
    apply integral_congr_ae
    filter_upwards with y
    simp only [lsmul_apply, logTest_eq_clamped, F, k, t]
  rw [hEq]
  exact hi

theorem fullCandidate_parameter_differentiable (n : ℕ) (z₀ : ℂ) (x : ℝ) :
    Differentiable ℂ (fun z => fullCandidate n z z₀ x) := by
  intro z
  simpa only [fullCandidate, Complex.real_smul] using
    ((smoothDelayed_parameter_hasDerivAt n z z₀ x).const_mul (cutoff n x : ℂ)).differentiableAt

theorem fullCandidate_parameter_entire (n : ℕ) (z₀ : ℂ) (x : ℝ) :
    AnalyticOnNhd ℂ (fun z => fullCandidate n z z₀ x) Set.univ :=
  fun z _ => (fullCandidate_parameter_differentiable n z₀ x).analyticAt z

#print axioms smoothDelayed_parameter_hasDerivAt
#print axioms fullCandidate_parameter_differentiable
#print axioms fullCandidate_parameter_entire

end RHConnections.Mollifier
