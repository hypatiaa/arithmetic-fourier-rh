import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

noncomputable section
open MeasureTheory
namespace RHConnections.PerronRampBounds

def kernel (h : ℝ) (s : ℂ) : ℂ :=
  (Complex.exp ((h:ℂ)*s) - Complex.exp (-((h:ℂ)*s))) / (2*(h:ℂ)*s^2)

def vertical (b t : ℝ) : ℂ := (b:ℂ) + (t:ℂ)*Complex.I

private theorem denominator_norm {h : ℝ} (hh : 0 < h) (s : ℂ) :
    ‖2*(h:ℂ)*s^2‖ = 2*h*‖s‖^2 := by simp [norm_mul, norm_pow, abs_of_pos hh]

private theorem numerator_le {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    {s : ℂ} (hs : 0 ≤ s.re) (hs₃ : s.re ≤ 3) :
    ‖Complex.exp ((h:ℂ)*s) - Complex.exp (-((h:ℂ)*s))‖ ≤ 2*Real.exp 3 := by
  refine (norm_sub_le _ _).trans ?_
  have hre : ((h:ℂ)*s).re = h*s.re := by simp [Complex.mul_re]
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re, hre]
  have h₁ : h*s.re ≤ 3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hh₁) hs]
  have h₂ : -(h*s.re) ≤ 3 := by nlinarith [mul_nonneg hh.le hs]
  linarith [Real.exp_le_exp.mpr h₁, Real.exp_le_exp.mpr h₂]

theorem kernel_norm_quadratic {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    {s : ℂ} (hs : 0 < s.re) (hs₃ : s.re ≤ 3) :
    ‖kernel h s‖ ≤ Real.exp 3 / (h*‖s‖^2) := by
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr (fun he => by simpa [he] using hs)
  rw [kernel, norm_div, denominator_norm hh]
  refine (div_le_div_of_nonneg_right (numerator_le hh hh₁ hs.le hs₃) (by positivity)).trans_eq ?_
  field_simp

theorem kernel_norm_linear {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    {s : ℂ} (hs : 0 < s.re) (hs₃ : s.re ≤ 3) :
    ‖kernel h s‖ ≤ (2+Real.exp 3) / ‖s‖ := by
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr (fun he => by simpa [he] using hs)
  by_cases hsmall : h*‖s‖ ≤ 1
  · let w := (h:ℂ)*s
    have hnw : ‖w‖ = h*‖s‖ := by simp [w,norm_mul,abs_of_pos hh]
    have hw : ‖w‖ ≤ 1 := by rwa [hnw]
    have hneg : ‖-w‖ ≤ 1 := by simpa using hw
    have hl := Complex.norm_exp_sub_one_le hw
    have hr := Complex.norm_exp_sub_one_le hneg
    have ht := norm_sub_le (Complex.exp w-1) (Complex.exp (-w)-1)
    rw [sub_sub_sub_cancel_right] at ht
    rw [norm_neg] at hr
    change ‖(Complex.exp w-Complex.exp (-w))/(2*(h:ℂ)*s^2)‖ ≤ _
    rw [norm_div, denominator_norm hh, div_le_div_iff₀ (by positivity) hn]
    have hnum : ‖Complex.exp w - Complex.exp (-w)‖ ≤ 4*(h*‖s‖) := by
      rw [← hnw]; linarith
    have hnum' := mul_le_mul_of_nonneg_right hnum hn.le
    nlinarith [mul_nonneg (Real.exp_pos 3).le (mul_nonneg hh.le (sq_nonneg ‖s‖))]
  · refine (kernel_norm_quadratic hh hh₁ hs hs₃).trans ?_
    rw [div_le_div_iff₀ (by positivity) hn]
    have hden : ‖s‖ ≤ h*‖s‖^2 := by nlinarith [mul_le_mul_of_nonneg_right (le_of_not_ge hsmall) hn.le]
    nlinarith [mul_le_mul_of_nonneg_left hden (Real.exp_pos 3).le, mul_nonneg hh.le (sq_nonneg ‖s‖)]

theorem kernel_norm_min {h b : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hb : 0 < b) (hb₃ : b ≤ 3) (t : ℝ) :
    ‖kernel h (vertical b t)‖ ≤ min ((2+Real.exp 3)/‖vertical b t‖)
      (Real.exp 3/(h*‖vertical b t‖^2)) := by
  have hre : (vertical b t).re = b := by simp [vertical]
  exact le_min (kernel_norm_linear (s := vertical b t) hh hh₁ (by rwa [hre]) (by rwa [hre]))
    (kernel_norm_quadratic (s := vertical b t) hh hh₁ (by rwa [hre]) (by rwa [hre]))

theorem weighted_kernel_integrable {h b η : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hb : 0 < b) (hb₃ : b ≤ 3) (hη : η < 1) :
    Integrable (fun t : ℝ => (1+|t|)^η * ‖kernel h (vertical b t)‖) := by
  let C := 1 + b⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase : Integrable (fun t : ℝ => (1+‖t‖)^(-(2-η))) := integrable_one_add_norm (r := 2-η)
    (by simpa using (show (1:ℝ) < 2-η by linarith))
  apply (hbase.const_mul (Real.exp 3 * C^2/h)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold kernel vertical
    fun_prop
  · apply Filter.Eventually.of_forall
    intro t
    let s := vertical b t
    have hre : s.re = b := by simp [s,vertical]
    have him : s.im = t := by simp [s,vertical]
    have hbr : b ≤ ‖s‖ := by simpa only [hre] using Complex.re_le_norm s
    have htr : |t| ≤ ‖s‖ := by simpa only [him] using Complex.abs_im_le_norm s
    have hn : 0 < ‖s‖ := hb.trans_le hbr
    have hd : 1+|t| ≤ C*‖s‖ := by
      have hi : 1 ≤ b⁻¹ * ‖s‖ := by
        calc
          _ = b⁻¹*b := (inv_mul_cancel₀ hb.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hbr (by positivity)
      dsimp [C]; nlinarith
    have hp : 0 < 1+|t| := by positivity
    have hrec : Real.exp 3/(h*‖s‖^2) ≤ (Real.exp 3*C^2/h)/(1+|t|)^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      field_simp [hh.ne']
      nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le hd 2) (Real.exp_pos 3).le]
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (1+|t|)^η * ((Real.exp 3*C^2/h)/(1+|t|)^2) := mul_le_mul_of_nonneg_left
        ((kernel_norm_quadratic (s := vertical b t) hh hh₁ (by rwa [hre]) (by rwa [hre])).trans hrec) (by positivity)
      _ = _ := by
        change _ = (Real.exp 3*C^2/h)*(1+‖t‖)^(-(2-η))
        rw [Real.norm_eq_abs, show -(2-η)=η-2 by ring, Real.rpow_sub hp]
        norm_num
        <;> ring

end RHConnections.PerronRampBounds
