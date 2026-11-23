import Verified
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
namespace RHConnections.PoleCompensation
open MeasureTheory RelativeResolvent ArchimedeanLimit

def realPlaceFrequency (v : ℝ) : ℂ := 1 - ((2*Real.pi*v : ℝ):ℂ)*Complex.I

private theorem frequency_bound (v : ℝ) :
    ‖realPlaceFrequency v‖+1 ≤ (2+2*Real.pi)*(1+|v|)^3 := by
  have h := norm_sub_le (1:ℂ) (((2*Real.pi*v : ℝ):ℂ)*Complex.I)
  simp only [norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  have hlin : ‖realPlaceFrequency v‖+1 ≤ (2+2*Real.pi)*(1+|v|) := by
    dsimp [realPlaceFrequency]
    nlinarith [Real.pi_pos, abs_nonneg v]
  apply hlin.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [abs_nonneg v, sq_nonneg |v|, pow_nonneg (abs_nonneg v) 3]

theorem realPlace_fourier_pairing (F f : ℝ → ℂ) (hFm : AEMeasurable F)
    (hF : Integrable (fun v => ‖F v‖*(1+|v|)^3))
    (hinv : ∀ x : ℝ, 0 < x →
      (∫ v : ℝ, F v * (Complex.exp ((((2*Real.pi*v : ℝ):ℂ)*Complex.I)*(x:ℂ))-1)) =
        Complex.exp (x:ℂ)*f x) :
    Integrable (fun v : ℝ => F v * realPlaceRelative (realPlaceFrequency v) 1) ∧
    (∫ v : ℝ, F v * realPlaceRelative (realPlaceFrequency v) 1) =
      ∫ x in Set.Ioi (0:ℝ), (realPlaceKernel x:ℂ)*f x := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let K := fun x : ℝ => (realPlaceKernel x:ℂ)
  let L := fun v x : ℝ => logTest (realPlaceFrequency v) 1 x
  let J := fun v x : ℝ => F v*(K x*L v x)
  let D := fun x : ℝ => 4*Real.exp (-(1/4:ℝ)*x)
  have hD : Integrable D μ :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(1/4 : ℝ) < 0) 0).const_mul 4
  have hK : Measurable K := Complex.continuous_ofReal.measurable.comp (by unfold realPlaceKernel; fun_prop)
  have hL : Measurable (fun p : ℝ×ℝ => L p.1 p.2) := by
    dsimp [L,logTest,realPlaceFrequency]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) (by fun_prop) measurable_const
  have hJ : Integrable (Function.uncurry J) (volume.prod μ) := by
    apply ((hF.mul_const (2+2*Real.pi)).mul_prod hD).mono'
    · exact hFm.aestronglyMeasurable.comp_fst.mul
        (hK.aestronglyMeasurable.comp_snd.mul hL.aestronglyMeasurable)
    · apply Filter.Eventually.of_forall
      rintro ⟨v,x⟩
      change ‖F v*(K x*L v x)‖ ≤ (‖F v‖*(1+|v|)^3*(2+2*Real.pi))*D x
      by_cases hx : 0 < x
      · have hr : 0 ≤ (realPlaceFrequency v).re := by simp [realPlaceFrequency,Complex.mul_re]
        have ht := logTest_linear (z := realPlaceFrequency v) (z₀ := (1:ℂ)) hr
          (by norm_num) hx.le
        have hK0 := realPlaceKernel_nonneg hx
        have hh : ‖K x*L v x‖ ≤ D x*((2+2*Real.pi)*(1+|v|)^3) := by
          rw [norm_mul, show ‖K x‖ = realPlaceKernel x from Complex.norm_of_nonneg hK0]
          calc
            _ ≤ realPlaceKernel x * ((‖realPlaceFrequency v‖+1)*x) := by
              exact mul_le_mul_of_nonneg_left (by simpa [L] using ht) hK0
            _ = (realPlaceKernel x*x)*(‖realPlaceFrequency v‖+1) := by ring
            _ ≤ _ := mul_le_mul (realPlaceKernel_mul_x_bound hx) (frequency_bound v)
              (by positivity) (by positivity)
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by ring)
      · simp only [L,logTest,if_neg hx,mul_zero,norm_zero]
        dsimp [D]; positivity
  have hv (v : ℝ) : (∫ x, J v x ∂μ) = F v * realPlaceRelative (realPlaceFrequency v) 1 :=
    integral_const_mul (F v) (fun x => K x*L v x)
  constructor
  · apply hJ.integral_prod_left.congr
    exact Filter.Eventually.of_forall hv
  calc
    _ = ∫ v : ℝ, ∫ x, J v x ∂μ := by
      apply integral_congr_ae
      filter_upwards with v
      exact (integral_const_mul (F v) (fun x => K x*L v x)).symm
    _ = ∫ x, (∫ v : ℝ, J v x) ∂μ := integral_integral_swap hJ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      change 0 < x at hx
      have hphase (v : ℝ) : L v x = Complex.exp (-(x:ℂ)) *
          (Complex.exp ((((2*Real.pi*v : ℝ):ℂ)*Complex.I)*(x:ℂ))-1) := by
        dsimp [L, logTest, realPlaceFrequency]
        rw [if_pos hx, mul_sub, mul_one, ← Complex.exp_add]
        congr 2 <;> ring
      have he (v : ℝ) : J v x = (K x*Complex.exp (-(x:ℂ))) *
          (F v*(Complex.exp ((((2*Real.pi*v : ℝ):ℂ)*Complex.I)*(x:ℂ))-1)) := by
        dsimp [J]; rw [hphase]; ring
      simp_rw [he]
      rw [integral_const_mul, hinv x hx, Complex.exp_neg]
      field_simp [Complex.exp_ne_zero] <;> ring

end RHConnections.PoleCompensation
