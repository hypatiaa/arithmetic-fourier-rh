import WeightedBulk
import WeightedConvolution

open MeasureTheory Set
noncomputable section
namespace RHConnections.WeightedBulk
open WeightedConvolution

theorem weighted_bulk_complex_integrable (j : ℕ) (z z₀ : ℂ) {sigma beta : ℝ}
    (hz : beta ≤ z.re) (hz₀ : beta ≤ z₀.re) (hs : sigma < beta) :
    Integrable (weighted sigma (bulk j z z₀)) := by
  have hi : (weighted sigma (bulk j z z₀)) =
      (Set.Ioi (0:ℝ)).indicator (fun y : ℝ => Real.exp (sigma*y) • positiveFormula j z z₀ y) := by
    funext y
    by_cases hy : 0 < y <;> simp [weighted, bulk, Set.indicator, hy]
  have hc : Continuous (fun y : ℝ => Real.exp (sigma*y) • positiveFormula j z z₀ y) := by
    unfold positiveFormula
    fun_prop
  have hm : AEStronglyMeasurable (weighted sigma (bulk j z z₀)) := by
    rw [hi]
    exact hc.aestronglyMeasurable.indicator measurableSet_Ioi
  apply (integrable_norm_iff hm).mp
  simpa only [norm_weighted] using weighted_bulk_integrable j z z₀ hz hz₀ hs

theorem weighted_shift_mass (sigma c : ℝ) (g : ℝ → ℂ) :
    (∫ x : ℝ, Real.exp (sigma*x)*‖g (x-c)‖) =
      Real.exp (sigma*c)*(∫ x : ℝ, Real.exp (sigma*x)*‖g x‖) := by
  calc
    _ = ∫ x : ℝ, Real.exp (sigma*c)*(Real.exp (sigma*(x-c))*‖g (x-c)‖) := by
      apply integral_congr_ae
      filter_upwards with x
      have he : Real.exp (sigma*x) = Real.exp (sigma*c)*Real.exp (sigma*(x-c)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact integral_sub_right_eq_self (fun x : ℝ => Real.exp (sigma*x)*‖g x‖) c

theorem weighted_shift_integrable (sigma c : ℝ) (g : ℝ → ℂ)
    (hg : Integrable (weighted sigma g)) :
    Integrable (weighted sigma (fun x => g (x-c))) := by
  have he : weighted sigma (fun x => g (x-c)) =
      fun x => Real.exp (sigma*c) • weighted sigma g (x-c) := by
    funext x
    unfold weighted
    rw [smul_smul]
    have harg : Real.exp (sigma*x) = Real.exp (sigma*c)*Real.exp (sigma*(x-c)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [harg]
  rw [he]
  exact (hg.comp_sub_right c).smul (Real.exp (sigma*c))

#print axioms weighted_bulk_complex_integrable
#print axioms weighted_shift_mass
#print axioms weighted_shift_integrable
end RHConnections.WeightedBulk
