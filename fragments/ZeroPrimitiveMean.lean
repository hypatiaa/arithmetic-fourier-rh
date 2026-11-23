import Verified
import AstraLocalModeContrast
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set MeasureTheory
namespace RHConnections.LocalModeContrast

def zeroPrimitive (rho : ℂ) (y : ℝ) : ℂ :=
  Complex.exp (rho*(Real.log y:ℂ))/rho

theorem zero_primitive_derivative {rho : ℂ} (hr : rho≠0) {y : ℝ} (hy : 0<y) :
    HasDerivAt (zeroPrimitive rho) (logMode rho y) y := by
  have h := ((((Real.hasDerivAt_log hy.ne').ofReal_comp).const_mul rho).cexp).div_const rho
  have he : logMode rho y =
      Complex.exp (rho*(Real.log y:ℂ))*(rho*((y⁻¹:ℝ):ℂ))/rho := by
    unfold logMode
    rw [sub_mul,one_mul,Complex.exp_sub,←Complex.ofReal_exp,Real.exp_log hy,Complex.ofReal_inv]
    field_simp [hr,Complex.ofReal_ne_zero.mpr hy.ne']
    <;> ring
  rw [he]
  exact h

theorem zero_primitive_scales (rho : ℂ) {L y : ℝ} (hL : 0<L) (hy : 0<y) :
    zeroPrimitive rho (L*y) = Complex.exp (rho*(Real.log L:ℂ))*zeroPrimitive rho y := by
  unfold zeroPrimitive
  rw [Real.log_mul hL.ne' hy.ne',Complex.ofReal_add,mul_add,Complex.exp_add]
  ring

theorem zero_primitive_difference_eq_mean {rho : ℂ} (hr : rho≠0) {a b : ℝ}
    (ha : 0<a) (hb : 0<b) :
    zeroPrimitive rho b-zeroPrimitive rho a = ((b-a:ℝ):ℂ)*normalizedMean (logMode rho) a b := by
  let G (s : ℝ) := zeroPrimitive rho (segment a b s)
  let g (s : ℝ) := logMode rho (segment a b s)*((b-a:ℝ):ℂ)
  have hpos (s) (hs : s ∈ Icc (0:ℝ) 1) : 0<segment a b s :=
    (convex_Ioi (0:ℝ)) ha hb (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel _ _)
  have hseg (s : ℝ) : HasDerivAt (segment a b) (b-a) s := by
    have hx := (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).mul_const a).add
      ((hasDerivAt_id s).mul_const b)
    convert hx using 1
    · rfl
    · ring
  have hder (s) (hs : s∈Icc (0:ℝ) 1) : HasDerivAt G (g s) s :=
    by simpa [G,g,Function.comp_def,Algebra.smul_def,mul_comm] using
      (zero_primitive_derivative hr (hpos s hs)).scomp s (hseg s)
  have hg : ContinuousOn g (uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    intro s hs
    have hh : ContinuousAt (logMode rho) (segment a b s) := by
      change ContinuousAt (fun y : ℝ => Complex.exp ((rho-1)*(Real.log y:ℂ))) (segment a b s)
      fun_prop (disch := exact (hpos s hs).ne')
    exact ((hh.comp (by unfold segment; fun_prop)).mul continuousAt_const).continuousWithinAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hder s (by simpa only [Set.uIcc_of_le zero_le_one] using hs))
    hg.intervalIntegrable
  have h01 : segment a b 0=a := by simp [segment]
  have h11 : segment a b 1=b := by simp [segment]
  simp only [G,h01,h11,g,intervalIntegral.integral_mul_const] at he
  unfold normalizedMean
  rw [mul_comm]
  exact he.symm

theorem scaled_zero_primitive_difference {rho : ℂ} (hr : rho≠0) {L a b : ℝ}
    (hL : 0<L) (ha : 0<a) (hb : 0<b) :
    zeroPrimitive rho (L*b)-zeroPrimitive rho (L*a) =
        (Complex.exp (rho*(Real.log L:ℂ))*((b-a:ℝ):ℂ))*normalizedMean (logMode rho) a b := by
  rw [zero_primitive_scales rho hL ha,zero_primitive_scales rho hL hb,←mul_sub,
    zero_primitive_difference_eq_mean hr ha hb]
  ring

end RHConnections.LocalModeContrast
