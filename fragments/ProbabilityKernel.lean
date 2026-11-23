import Verified
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory

noncomputable section
namespace RHConnections.Mollifier

theorem probability_kernel_weighted_mass (rho : ℝ → ℝ) {radius a sigma : ℝ}
    (hrho : Integrable rho) (hnonneg : ∀ x, 0 ≤ rho x)
    (hmass : (∫ x : ℝ, rho x) = 1) (hsupport : ∀ x, radius < |x| → rho x = 0)
    (_hradius : 0 ≤ radius) (ha : 0 ≤ a) (hsigma : |sigma| ≤ a) :
    Integrable (fun x : ℝ => Real.exp (sigma * x) * rho x) ∧
      (∫ x : ℝ, Real.exp (sigma * x) * rho x) ≤ Real.exp (a * radius) := by
  have hpointwise (x : ℝ) :
      Real.exp (sigma * x) * rho x ≤ Real.exp (a * radius) * rho x := by
    by_cases hx : |x| ≤ radius
    · have harg : sigma * x ≤ a * radius := calc
        sigma * x ≤ |sigma * x| := le_abs_self _
        _ = |sigma| * |x| := abs_mul _ _
        _ ≤ a * radius := mul_le_mul hsigma hx (abs_nonneg _) ha
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr harg) (hnonneg x)
    · simp [hsupport x (lt_of_not_ge hx)]
  have hweight : Continuous (fun x : ℝ => Real.exp (sigma * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hmajorant : Integrable (fun x : ℝ => Real.exp (a * radius) * rho x) :=
    hrho.const_mul _
  have hweighted : Integrable (fun x : ℝ => Real.exp (sigma * x) * rho x) := by
    refine hmajorant.mono_nonneg (hweight.aestronglyMeasurable.mul hrho.aestronglyMeasurable) ?_ ?_
    · exact Filter.Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (hnonneg x)
    · exact Filter.Eventually.of_forall hpointwise
  refine ⟨hweighted, ?_⟩
  calc
    _ ≤ ∫ x : ℝ, Real.exp (a * radius) * rho x :=
      integral_mono hweighted hmajorant hpointwise
    _ = Real.exp (a * radius) := by rw [integral_const_mul, hmass, mul_one]

theorem bump_weighted_mass (n : ℕ) {a sigma : ℝ} (ha : 0 ≤ a) (hsigma : |sigma| ≤ a) :
    Integrable (fun x : ℝ => Real.exp (sigma * x) * (bump n).normed volume x) ∧
      (∫ x : ℝ, Real.exp (sigma * x) * (bump n).normed volume x) ≤ Real.exp a := by
  have hint : Integrable ((bump n).normed volume) :=
    (bump n).continuous_normed.integrable_of_hasCompactSupport (bump n).hasCompactSupport_normed
  have hsupport (x : ℝ) (hx : epsilon n < |x|) : (bump n).normed volume x = 0 := by
    have hb : bump n x = 0 := (bump n).zero_of_le_dist (by
      simpa only [bump, Real.dist_eq, sub_zero] using hx.le)
    simp [ContDiffBump.normed_def, hb]
  have hε : epsilon n ≤ 1 := by
    unfold epsilon
    exact div_le_self zero_le_one (le_add_of_nonneg_left (Nat.cast_nonneg n))
  obtain ⟨hweighted, hmass⟩ := probability_kernel_weighted_mass ((bump n).normed volume)
    hint (bump n).nonneg_normed (kernel_mass n) hsupport (epsilon_pos n).le ha hsigma
  refine ⟨hweighted, hmass.trans (Real.exp_le_exp.mpr ?_)⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hε ha

#print axioms probability_kernel_weighted_mass
#print axioms bump_weighted_mass

end RHConnections.Mollifier
