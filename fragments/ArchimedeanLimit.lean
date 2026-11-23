import Verified

open MeasureTheory Filter Set ContinuousLinearMap
open scoped Topology Convolution
noncomputable section
namespace RHConnections.ArchimedeanLimit
open Mollifier RelativeResolvent EndpointIBP

theorem logTest_linear {z z₀ : ℂ} (hz : 0 ≤ z.re) (hz₀ : 0 ≤ z₀.re)
    {x : ℝ} (hx : 0 ≤ x) : ‖logTest z z₀ x‖ ≤ (‖z‖ + ‖z₀‖) * x := by
  have hd (y : ℝ) (hy : y ∈ Set.Icc 0 x) :
      ‖firstBranch z z₀ y‖ ≤ ‖z‖ + ‖z₀‖ := by
    simpa [firstBranch, WeightedBulk.positiveFormula] using
      WeightedBulk.positiveFormula_bound 1 z z₀ hz hz₀ hy.1
  have h := (convex_Icc (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y (_ : y ∈ Set.Icc 0 x) => (positiveBranch_derivative z z₀ y).hasDerivWithinAt)
    hd (show (0 : ℝ) ∈ Set.Icc 0 x from ⟨le_rfl, hx⟩)
    (show x ∈ Set.Icc 0 x from ⟨hx, le_rfl⟩)
  rcases hx.eq_or_lt with hzero | hpos
  · subst x
    simp [logTest]
  · simpa [logTest, hpos, positiveBranch, Real.norm_eq_abs, abs_of_nonneg hx] using h

theorem fullCandidate_linear (n : ℕ) {z z₀ : ℂ} (hz : 0 ≤ z.re) (hz₀ : 0 ≤ z₀.re)
    {x : ℝ} (hx : 0 ≤ x) : ‖fullCandidate n z z₀ x‖ ≤ (‖z‖ + ‖z₀‖) * x := by
  let M := (‖z‖ + ‖z₀‖) * x
  let k := (bump n).normed volume
  have hM : 0 ≤ M := mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hx
  have hpoint (y : ℝ) :
      ‖k y • logTest z z₀ (x-2*epsilon n-y)‖ ≤ M * k y := by
    have hk := (bump n).nonneg_normed (μ := volume) y
    by_cases hy : |y| < epsilon n
    · rw [norm_smul, Real.norm_of_nonneg hk, mul_comm M]
      apply mul_le_mul_of_nonneg_left _ hk
      by_cases ht : 0 ≤ x-2*epsilon n-y
      · apply (logTest_linear hz hz₀ ht).trans
        exact mul_le_mul_of_nonneg_left (by linarith [neg_le_abs y, epsilon_pos n])
          (add_nonneg (norm_nonneg _) (norm_nonneg _))
      · rw [vanishes_left z z₀ (le_of_lt (lt_of_not_ge ht)), norm_zero]
        exact hM
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

theorem local_kernel_limit {z z₀ : ℂ} (hz : 0 ≤ z.re) (hz₀ : 0 ≤ z₀.re)
    (K : ℝ → ℂ) (R C : ℝ)
    (hm : AEStronglyMeasurable K (volume.restrict (Set.Ioc 0 R)))
    (hK : ∀ x ∈ Set.Ioc 0 R, ‖K x‖ * x ≤ C) :
    Tendsto (fun n => ∫ x in Set.Ioc 0 R, K x * fullCandidate n z z₀ x) atTop
      (𝓝 (∫ x in Set.Ioc 0 R, K x * logTest z z₀ x)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => C * (‖z‖ + ‖z₀‖))
  · intro n
    exact hm.mul (fullCandidate_smooth n z z₀).continuous.aestronglyMeasurable
  · exact integrableOn_const (by simp [Real.volume_Ioc])
  · intro n
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    rw [norm_mul]
    calc
      _ ≤ ‖K x‖ * ((‖z‖ + ‖z₀‖) * x) := mul_le_mul_of_nonneg_left
        (fullCandidate_linear n hz hz₀ hx.1.le) (norm_nonneg _)
      _ = (‖K x‖ * x) * (‖z‖ + ‖z₀‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hK x hx) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (fullCandidate_limit z z₀ x)

#print axioms logTest_linear
#print axioms fullCandidate_linear
#print axioms local_kernel_limit
end RHConnections.ArchimedeanLimit
