import Verified

open Metric
noncomputable section
namespace RHConnections.ZetaDiskLog
open ZetaAbelGrowth ZetaEulerNearOne

def verticalCenter (t : ℝ) : ℂ := (4:ℂ)+(t:ℂ)*Complex.I

theorem verticalCenter_re (t : ℝ) : (verticalCenter t).re = 4 := by
  norm_num [verticalCenter,Complex.add_re,Complex.mul_re]

theorem verticalCenter_im (t : ℝ) : (verticalCenter t).im = t := by
  norm_num [verticalCenter,Complex.add_im,Complex.mul_im]

theorem ball_verticalCenter_re_bounds {t R : ℝ} {s : ℂ} (hs : s ∈ ball (verticalCenter t) R) :
    4-R < s.re ∧ s.re < 4+R := by
  have h := (Complex.abs_re_le_norm (s-verticalCenter t)).trans_lt
    (by simpa only [mem_ball,dist_eq_norm] using hs)
  rw [Complex.sub_re, verticalCenter_re] at h
  have h' := abs_lt.mp h
  constructor <;> linarith [h'.1,h'.2]

theorem ball_verticalCenter_norm_bounds {t R : ℝ} (hR : R ≤ 4) {s : ℂ}
    (hs : s ∈ ball (verticalCenter t) R) :
    ‖s‖ ≤ |t|+8 ∧ |t|-4 ≤ ‖s-1‖ := by
  have hd : ‖s-verticalCenter t‖ < R := by simpa only [mem_ball,dist_eq_norm] using hs
  have hc : ‖verticalCenter t‖ ≤ 4+|t| := by
    simpa [verticalCenter, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      norm_add_le (4:ℂ) ((t:ℂ)*Complex.I)
  have hIm := (Complex.abs_im_le_norm (s-verticalCenter t)).trans hd.le
  rw [Complex.sub_im, verticalCenter_im] at hIm
  have hsim : |s.im| ≤ ‖s-1‖ := by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (s-1)
  constructor
  · have h := norm_add_le (s-verticalCenter t) (verticalCenter t)
    rw [sub_add_cancel] at h
    linarith
  · have h := abs_sub_abs_le_abs_sub t s.im
    rw [abs_sub_comm t s.im] at h
    linarith

theorem zeta_norm_on_vertical_ball {t R : ℝ} (ht : 5 ≤ |t|)
    (hR : R ≤ 7/2) {s : ℂ} (hs : s ∈ ball (verticalCenter t) R) :
    ‖riemannZeta s‖ ≤ 3*(|t|+10) := by
  have hRe : (1/2:ℝ) ≤ s.re := by
    have h := (ball_verticalCenter_re_bounds hs).1
    linarith
  have hRePos : 0 < s.re := by linarith
  obtain ⟨hn,hp⟩ := ball_verticalCenter_norm_bounds (by linarith : R ≤ 4) hs
  have hd : 1 ≤ ‖s-1‖ := by linarith
  have hnz : s ≠ 1 := by
    intro he
    rw [he,sub_self,norm_zero] at hd
    linarith
  have ha := zeta_vertical_bound hRePos hnz
  rw [norm_div] at ha
  have h1 : ‖s‖/‖s-1‖ ≤ ‖s‖ := div_le_self (norm_nonneg _) hd
  have h2 : ‖s‖/s.re ≤ 2*‖s‖ := by
    apply (div_le_iff₀ hRePos).2
    nlinarith [mul_nonneg (norm_nonneg s) (show 0 ≤ 2*s.re-1 by linarith)]
  linarith

theorem principal_log_norm_of_zeta_right {s : ℂ} (hs : 3 ≤ s.re) :
    ‖Complex.log (riemannZeta s)‖ ≤ 1+Real.pi := by
  obtain ⟨hl,hu,_⟩ := zeta_right_bounds hs
  have hll := Real.log_le_log (by norm_num : (0:ℝ)<1/2) hl
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),Real.log_one,zero_sub] at hll
  have hup := Real.log_le_sub_one_of_pos (by linarith : 0 < ‖riemannZeta s‖)
  have hlog : |Real.log ‖riemannZeta s‖| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ ≤ |(Complex.log (riemannZeta s)).re| + |(Complex.log (riemannZeta s)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by
      rw [Complex.log_re, Complex.log_im]
      exact add_le_add hlog (Complex.abs_arg_le_pi _)

end RHConnections.ZetaDiskLog
