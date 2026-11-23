import Verified

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace RHConnections.PoleCompensation
open ArchimedeanLimit RelativeResolvent

theorem realPlaceKernel_mul_x_bound {x : ℝ} (hx : 0 < x) :
    realPlaceKernel x * x ≤ 4 * Real.exp (-(1/4 : ℝ)*x) := by
  have hb := realPlaceKernel_denominator_bound hx
  have hd : 0 < 1 - Real.exp (-2*x) :=
    (div_pos (by positivity) (by positivity) : 0 < (2*x)/(1+2*x)).trans_le hb
  have hratio : x / (1-Real.exp (-2*x)) ≤ x+1/2 := by
    apply (div_le_iff₀ hd).2
    have h := (div_le_iff₀ (by positivity : 0 < 1+2*x)).1 hb
    nlinarith
  have hpoly : x + 1/2 ≤ 4 * Real.exp (x/4) := by linarith [Real.add_one_le_exp (x/4)]
  calc
    _ = Real.exp (-x/2) * (x / (1-Real.exp (-2*x))) := by unfold realPlaceKernel; ring
    _ ≤ Real.exp (-x/2) * (4 * Real.exp (x/4)) :=
      mul_le_mul_of_nonneg_left (hratio.trans hpoly) (Real.exp_pos _).le
    _ = 4 * Real.exp (-(1/4 : ℝ)*x) := by
      rw [show Real.exp (-x/2) * (4 * Real.exp (x/4)) =
        4 * (Real.exp (-x/2) * Real.exp (x/4)) by ring, ← Real.exp_add]
      congr 2 <;> ring

theorem realPlaceRelative_hasDerivAt {z z₀ : ℂ} (hz : 0 < z.re) (hz₀ : 0 ≤ z₀.re) :
    HasDerivAt (fun w => realPlaceRelative w z₀)
      (∫ x in Ioi (0 : ℝ), (realPlaceKernel x : ℂ) *
        (-(x : ℂ) * Complex.exp (-z*(x : ℂ)))) z := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F (w : ℂ) (x : ℝ) := (realPlaceKernel x : ℂ) * logTest w z₀ x
  let G (w : ℂ) (x : ℝ) := (realPlaceKernel x : ℂ) * (-(x : ℂ) * Complex.exp (-w*(x : ℂ)))
  let D (x : ℝ) := 4 * Real.exp (-(1/4 : ℝ)*x)
  have hD : Integrable D μ :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(1/4 : ℝ) < 0) 0).const_mul 4
  have hm : Measurable (fun x : ℝ => (realPlaceKernel x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (by unfold realPlaceKernel; fun_prop)
  have hFm (w : ℂ) : AEStronglyMeasurable (F w) μ :=
    hm.aestronglyMeasurable.mul (logTest_continuous w z₀).aestronglyMeasurable
  have hGm : AEStronglyMeasurable (G z) μ := by
    apply hm.aestronglyMeasurable.mul
    exact (show Continuous (fun x : ℝ => -(x : ℂ) * Complex.exp (-z*(x : ℂ))) by
      fun_prop).aestronglyMeasurable
  have hpos : ∀ᵐ x ∂μ, 0 < x := ae_restrict_mem (μ := volume) measurableSet_Ioi
  have hFi : Integrable (F z) μ := by
    apply (hD.mul_const (‖z‖ + ‖z₀‖)).mono' (hFm z)
    filter_upwards [hpos] with x hx
    simp only [F, norm_mul, Complex.norm_of_nonneg (realPlaceKernel_nonneg hx)]
    calc
      _ ≤ realPlaceKernel x * ((‖z‖ + ‖z₀‖) * x) :=
        mul_le_mul_of_nonneg_left (logTest_linear hz.le hz₀ hx.le) (realPlaceKernel_nonneg hx)
      _ = (realPlaceKernel x * x) * (‖z‖ + ‖z₀‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (realPlaceKernel_mul_x_bound hx) (by positivity)
  have hnb : {w : ℂ | 0 < w.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hd (x : ℝ) (hx : 0 < x) (w : ℂ) :
      HasDerivAt (fun r : ℂ => F r x) (G w x) w := by
    have ha : HasDerivAt (fun r : ℂ => -r * (x : ℂ)) (-(x : ℂ)) w := by
      have hmul : HasDerivAt (fun r : ℂ => r * (x : ℂ)) (x : ℂ) w := by
        simpa only [id_eq, one_mul] using (hasDerivAt_id w).mul_const (x : ℂ)
      simp only [neg_mul]
      exact hmul.neg
    have hv := (ha.cexp.sub_const (Complex.exp (-z₀*(x : ℂ)))).const_mul (realPlaceKernel x : ℂ)
    simpa only [F, G, logTest, if_pos hx, mul_comm (Complex.exp _) (-(x : ℂ))] using hv
  have hbound (x : ℝ) (hx : 0 < x) (w : ℂ) (hw : 0 < w.re) : ‖G w x‖ ≤ D x := by
    have he : ‖Complex.exp (-w*(x : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hw.le) hx.le
    simp only [G, norm_mul, norm_neg, Complex.norm_of_nonneg (realPlaceKernel_nonneg hx),
      Complex.norm_of_nonneg hx.le]
    calc
      _ ≤ realPlaceKernel x * (x * 1) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he hx.le) (realPlaceKernel_nonneg hx)
      _ ≤ D x := by simpa only [mul_one] using realPlaceKernel_mul_x_bound hx
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := G)
    hnb (Eventually.of_forall hFm) hFi hGm (hpos.mono fun x hx w hw => hbound x hx w hw)
    hD (hpos.mono fun x hx w _ => hd x hx w)).2

theorem realPlaceRelative_differentiableOn {z₀ : ℂ} (hz₀ : 0 ≤ z₀.re) :
    DifferentiableOn ℂ (fun z => realPlaceRelative z z₀) {z : ℂ | 0 < z.re} :=
  fun _ hz => (realPlaceRelative_hasDerivAt hz hz₀).differentiableAt.differentiableWithinAt

#print axioms realPlaceRelative_hasDerivAt
#print axioms realPlaceRelative_differentiableOn
end RHConnections.PoleCompensation
