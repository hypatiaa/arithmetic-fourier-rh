import Verified

open MeasureTheory Filter Set ContinuousLinearMap
open scoped Topology Convolution
noncomputable section
namespace RHConnections.FourierDecay
open Mollifier RelativeResolvent WeightedConvolution

theorem fullCandidate_exponential_envelope (n : ℕ) (z z₀ : ℂ) (b x : ℝ)
    (hz : b ≤ z.re) (hz₀ : b ≤ z₀.re) :
    ‖fullCandidate n z z₀ x‖ ≤ 2 * Real.exp (3 * |b| - b*x) := by
  let M := 2 * Real.exp (3 * |b| - b*x)
  let k := (bump n).normed volume
  have he : epsilon n ≤ 1 := by
    unfold epsilon
    exact div_le_self zero_le_one (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpoint (y : ℝ) :
      ‖k y • logTest z z₀ (x-2*epsilon n-y)‖ ≤ M * k y := by
    have hk := (bump n).nonneg_normed (μ := volume) y
    by_cases hy : |y| < epsilon n
    · have hshift : |2*epsilon n+y| ≤ 3 := by
        rw [abs_le]
        constructor <;> linarith [le_abs_self y, neg_le_abs y, epsilon_pos n]
      have hprod : b*(2*epsilon n+y) ≤ |b| *3 := calc
        _ ≤ |b*(2*epsilon n+y)| := le_abs_self _
        _ = |b| *|2*epsilon n+y| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hshift (abs_nonneg _)
      rw [norm_smul, Real.norm_of_nonneg hk, mul_comm M]
      apply mul_le_mul_of_nonneg_left _ hk
      by_cases ht : 0 < x-2*epsilon n-y
      · have h := WeightedBulk.positiveFormula_bound 0 z z₀ hz hz₀ ht.le
        simp only [WeightedBulk.positiveFormula, pow_zero, one_mul, one_add_one_eq_two] at h
        rw [logTest, if_pos ht]
        exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hprod] :
          -b*(x-2*epsilon n-y) ≤ 3*|b|-b*x)) (by norm_num))
      · simpa [logTest, ht] using hM
    · have hb : bump n y = 0 := (bump n).zero_of_le_dist (by
        simpa only [bump, Real.dist_eq, sub_zero] using (le_of_not_gt hy))
      have hk0 : k y = 0 := by simp [k, ContDiffBump.normed_def, hb]
      simp [hk0]
  have hconv : ‖smoothDelayed n z z₀ x‖ ≤ M := by
    unfold smoothDelayed
    rw [convolution_def]
    calc
      _ ≤ ∫ y : ℝ, M*k y :=
        norm_integral_le_of_norm_le (((bump n).integrable_normed (μ := volume)).const_mul M)
          (Eventually.of_forall fun y => by simpa only [lsmul_apply] using hpoint y)
      _ = M := by rw [integral_const_mul, show (∫ y, k y) = 1 from kernel_mass n, mul_one]
  rw [fullCandidate, norm_smul, Real.norm_of_nonneg ((cutoff n).nonneg)]
  exact (mul_le_mul_of_nonneg_right ((cutoff n).le_one) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hconv)

theorem weighted_angular_integral (f : ℝ → ℂ) (xi : ℂ) :
    angularTransform (weighted xi.re f) xi.im =
      ∫ x : ℝ, Complex.exp (xi * (x : ℂ)) * f x := by
  rw [angular_integral]
  apply integral_congr_ae
  filter_upwards with x
  rw [weighted, Complex.real_smul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem fullCandidate_weighted_angular_limit (z z₀ xi : ℂ)
    (hz : xi.re < z.re) (hz₀ : xi.re < z₀.re) :
    Tendsto (fun n => angularTransform (weighted xi.re (fullCandidate n z z₀)) xi.im)
      atTop (𝓝 (relative z z₀ xi)) := by
  let b := min z.re z₀.re
  let B := 2 * Real.exp (3*|b|)
  let D : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator (fun x => B * Real.exp ((xi.re-b)*x))
  have hb : xi.re < b := lt_min hz hz₀
  have hD : Integrable D := (integrable_indicator_iff measurableSet_Ioi).mpr
    ((integrableOn_exp_mul_Ioi (by linarith : xi.re-b < 0) 0).const_mul B)
  have hlimit : (∫ x : ℝ, Complex.exp (xi*(x : ℂ)) * logTest z z₀ x) =
      relative z z₀ xi := by
    rw [← laplace_difference z z₀ xi hz hz₀, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Set.Ioi 0 from hx), logTest, if_pos hx, mul_sub,
        ← Complex.exp_add, ← Complex.exp_add]
      congr 2 <;> ring
    · simp [logTest, hx, Set.indicator_of_notMem (show x ∉ Set.Ioi 0 from hx)]
  simp_rw [weighted_angular_integral]
  rw [← hlimit]
  apply tendsto_integral_of_dominated_convergence D
  · intro n
    exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (fullCandidate_smooth n z z₀).continuous).aestronglyMeasurable
  · exact hD
  · intro n
    filter_upwards with x
    by_cases hx : 0 < x
    · rw [norm_mul, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      calc
        _ ≤ Real.exp (xi.re*x) * (2 * Real.exp (3*|b|-b*x)) :=
          mul_le_mul_of_nonneg_left
            (fullCandidate_exponential_envelope n z z₀ b x (min_le_left ..) (min_le_right ..))
            (Real.exp_pos _).le
        _ = D x := by
          rw [show D x = B * Real.exp ((xi.re-b)*x) from indicator_of_mem hx _]
          dsimp only [B]
          rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
          congr 2 <;> ring
    · have hf := fullCandidate_vanishes_left n z z₀ ((le_of_not_gt hx).trans (epsilon_pos n).le)
      simp [hf, D, Set.indicator_of_notMem (show x ∉ Set.Ioi 0 from hx)]
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (fullCandidate_limit z z₀ x)

#print axioms fullCandidate_weighted_angular_limit
end RHConnections.FourierDecay
