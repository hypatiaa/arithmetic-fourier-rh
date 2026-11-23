import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

open MeasureTheory ContinuousLinearMap
open scoped Convolution
noncomputable section
namespace RHConnections.WeightedConvolution

def weighted (sigma : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ := Real.exp (sigma*x) • g x
def weightedKernel (sigma : ℝ) (rho : ℝ → ℝ) (x : ℝ) : ℝ := Real.exp (sigma*x)*rho x

theorem norm_weighted (sigma : ℝ) (g : ℝ → ℂ) (x : ℝ) :
    ‖weighted sigma g x‖ = Real.exp (sigma*x)*‖g x‖ := by
  rw [weighted, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem convolution_norm_le (rho : ℝ → ℝ) (g : ℝ → ℂ)
    (hn : ∀ x, 0 ≤ rho x) (x : ℝ) :
    ‖(rho ⋆[lsmul ℝ ℝ, volume] g) x‖ ≤
      (rho ⋆[lsmul ℝ ℝ, volume] (fun y => ‖g y‖)) x := by
  rw [convolution_def, convolution_def]
  calc
    _ ≤ ∫ y : ℝ, ‖(lsmul ℝ ℝ) (rho y) (g (x-y))‖ := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      simp [lsmul_apply, norm_smul, Real.norm_of_nonneg (hn y)]

theorem convolution_mass_bound (rho : ℝ → ℝ) (g : ℝ → ℂ)
    (hn : ∀ x, 0 ≤ rho x) (hr : Integrable rho) (hg : Integrable g) :
    (∫ x : ℝ, ‖(rho ⋆[lsmul ℝ ℝ, volume] g) x‖) ≤
      (∫ x : ℝ, rho x)*(∫ x : ℝ, ‖g x‖) := by
  have hi : Integrable (rho ⋆[lsmul ℝ ℝ, volume] g) :=
    Integrable.integrable_convolution (L := lsmul ℝ ℝ) hr hg
  have him : Integrable (rho ⋆[lsmul ℝ ℝ, volume] (fun y => ‖g y‖)) :=
    Integrable.integrable_convolution (L := lsmul ℝ ℝ) hr hg.norm
  calc
    _ ≤ ∫ x : ℝ, (rho ⋆[lsmul ℝ ℝ, volume] (fun y => ‖g y‖)) x :=
      integral_mono hi.norm him (convolution_norm_le rho g hn)
    _ = _ := by
      simpa only [lsmul_apply, smul_eq_mul] using integral_convolution
        (L := lsmul ℝ ℝ) hr hg.norm

theorem weighted_convolution (sigma : ℝ) (rho : ℝ → ℝ) (g : ℝ → ℂ) :
    weighted sigma (rho ⋆[lsmul ℝ ℝ, volume] g) =
      (weightedKernel sigma rho ⋆[lsmul ℝ ℝ, volume] weighted sigma g) := by
  funext x
  unfold weighted
  rw [convolution_def, convolution_def, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [weightedKernel, lsmul_apply, smul_smul]
  have he : Real.exp (sigma*x) = Real.exp (sigma*y)*Real.exp (sigma*(x-y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  congr 1
  ring

theorem weighted_convolution_mass_bound (sigma : ℝ) (rho : ℝ → ℝ) (g : ℝ → ℂ)
    (hn : ∀ x, 0 ≤ rho x) (hr : Integrable (weightedKernel sigma rho))
    (hg : Integrable (weighted sigma g)) :
    (∫ x : ℝ, Real.exp (sigma*x)*‖(rho ⋆[lsmul ℝ ℝ, volume] g) x‖) ≤
      (∫ x : ℝ, weightedKernel sigma rho x)*(∫ x : ℝ, Real.exp (sigma*x)*‖g x‖) := by
  simp_rw [← norm_weighted]
  rw [weighted_convolution]
  exact convolution_mass_bound _ _ (fun x => mul_nonneg (Real.exp_pos _).le (hn x)) hr hg

theorem weighted_convolution_integrable (sigma : ℝ) (rho : ℝ → ℝ) (g : ℝ → ℂ)
    (hr : Integrable (weightedKernel sigma rho)) (hg : Integrable (weighted sigma g)) :
    Integrable (weighted sigma (rho ⋆[lsmul ℝ ℝ, volume] g)) := by
  rw [weighted_convolution]
  exact Integrable.integrable_convolution (L := lsmul ℝ ℝ) hr hg

#print axioms norm_weighted
#print axioms convolution_norm_le
#print axioms convolution_mass_bound
#print axioms weighted_convolution
#print axioms weighted_convolution_mass_bound
#print axioms weighted_convolution_integrable
end RHConnections.WeightedConvolution
