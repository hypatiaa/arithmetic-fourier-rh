import Verified

open MeasureTheory Filter
noncomputable section
namespace RHConnections.PoleCompensation
open ArchimedeanLimit Mollifier RelativeResolvent

def parityRealPlaceKernel (odd : Bool) (x : ℝ) : ℝ :=
  Real.exp (-(if odd then (1:ℝ) else 0)*x) * realPlaceKernel x

theorem parityRealPlaceKernel_even (x : ℝ) :
    parityRealPlaceKernel false x = realPlaceKernel x := by simp [parityRealPlaceKernel]

theorem parityRealPlaceKernel_odd (x : ℝ) :
    parityRealPlaceKernel true x = Real.exp (-x)*realPlaceKernel x := by simp [parityRealPlaceKernel]

theorem damped_realPlace_limit {z z₀ : ℂ} (hz : 0 ≤ z.re) (hz₀ : 0 ≤ z₀.re)
    (p : ℝ → ℂ) (hp : Measurable p) (hunit : ∀ x : ℝ, 0 < x → ‖p x‖ ≤ 1) :
    Tendsto (fun n => ∫ x in Set.Ioi (0 : ℝ),
      p x * (realPlaceKernel x : ℂ) * fullCandidate n z z₀ x) atTop
      (nhds (∫ x in Set.Ioi (0 : ℝ), p x * (realPlaceKernel x : ℂ) * logTest z z₀ x)) := by
  let D := fun x : ℝ => (4*(‖z‖+‖z₀‖)) * Real.exp (-(1/4 : ℝ)*x)
  have hD : IntegrableOn D (Set.Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(1/4 : ℝ) < 0) 0).const_mul _
  have hK : Measurable (fun x : ℝ => (realPlaceKernel x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (by unfold realPlaceKernel; fun_prop)
  apply tendsto_integral_of_dominated_convergence D
  · intro n
    exact (hp.mul hK).aestronglyMeasurable.mul
      (fullCandidate_smooth n z z₀).continuous.aestronglyMeasurable
  · exact hD
  · intro n
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx' : 0 < x := hx
    have hK0 := realPlaceKernel_nonneg hx'
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg hK0]
    calc
      _ ≤ (1*realPlaceKernel x)*((‖z‖+‖z₀‖)*x) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hunit x hx') hK0)
          (fullCandidate_linear n hz hz₀ hx'.le) (norm_nonneg _) (by positivity)
      _ = (realPlaceKernel x*x)*(‖z‖+‖z₀‖) := by ring
      _ ≤ D x := (mul_le_mul_of_nonneg_right (realPlaceKernel_mul_x_bound hx')
        (by positivity : 0 ≤ ‖z‖+‖z₀‖)).trans_eq (by
          unfold D

          ring)
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (fullCandidate_limit z z₀ x)

theorem parity_realPlace_limit (odd : Bool) {z z₀ : ℂ} (hz : 0 ≤ z.re) (hz₀ : 0 ≤ z₀.re) :
    Tendsto (fun n => ∫ x in Set.Ioi (0 : ℝ),
      (parityRealPlaceKernel odd x : ℂ) * fullCandidate n z z₀ x) atTop
      (nhds (∫ x in Set.Ioi (0 : ℝ), (parityRealPlaceKernel odd x : ℂ) * logTest z z₀ x)) := by
  cases odd
  · simpa only [parityRealPlaceKernel_even] using realPlaceKernel_limit hz hz₀
  · let p := fun x : ℝ => (Real.exp (-x) : ℂ)
    have hp : Measurable p := by dsimp [p]; fun_prop
    have hu (x : ℝ) (hx : 0 < x) : ‖p x‖ ≤ 1 := by
      rw [show p x = (Real.exp (-x) : ℂ) by rfl, Complex.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (by linarith)
    simpa only [parityRealPlaceKernel_odd, Complex.ofReal_mul, p] using
      damped_realPlace_limit hz hz₀ p hp hu

end RHConnections.PoleCompensation
