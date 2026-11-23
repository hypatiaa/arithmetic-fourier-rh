import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform Topology
namespace RHConnections.PerronRamp

def ramp (h x : ℝ) : ℝ := (max (x+h) 0 - max (x-h) 0)/(2*h)

theorem ramp_continuous (h : ℝ) : Continuous (ramp h) := by unfold ramp; fun_prop

theorem ramp_zero {h x : ℝ} (hh : 0 < h) (hx : x ≤ -h) : ramp h x = 0 := by
  simp [ramp,max_eq_right (by linarith : x+h ≤ 0),max_eq_right (by linarith : x-h ≤ 0)]

theorem ramp_one {h x : ℝ} (hh : 0 < h) (hx : h ≤ x) : ramp h x = 1 := by
  rw [ramp,max_eq_left (by linarith : 0 ≤ x+h),max_eq_left (by linarith : 0 ≤ x-h)]
  field_simp
  ring

theorem ramp_mem_Icc {h : ℝ} (hh : 0 < h) (x : ℝ) : ramp h x ∈ Set.Icc 0 1 := by
  by_cases hl : x ≤ -h
  · simp [ramp_zero hh hl]
  by_cases hr : h ≤ x
  · simp [ramp_one hh hr]
  have he : ramp h x = (x+h)/(2*h) := by
    simp [ramp,max_eq_left (by linarith : 0 ≤ x+h),max_eq_right (by linarith : x-h ≤ 0)]
  rw [he]
  exact ⟨div_nonneg (by linarith) (by positivity), (div_le_one (by positivity)).2 (by linarith)⟩

def probe (c v : ℝ) : ℂ := (c:ℂ) + ((2*Real.pi*v : ℝ):ℂ)*Complex.I
def kernel (h : ℝ) (s : ℂ) : ℂ := (Complex.exp ((h:ℂ)*s)-Complex.exp (-(h:ℂ)*s))/(2*(h:ℂ)*s^2)
def dampedRamp (h c x : ℝ) : ℂ := (Real.exp (-c*x) * ramp h x : ℝ)

private def E (s : ℂ) (x : ℝ) := Complex.exp (-s*(x:ℂ))
private def X (s : ℂ) (x : ℝ) := (x:ℂ)*E s x
private def P (s : ℂ) (x : ℝ) := (max x 0 : ℝ) * E s x

private theorem norm_E (s : ℂ) (x : ℝ) : ‖E s x‖ = Real.exp (-s.re*x) := by
  simp [E, Complex.norm_exp, Complex.mul_re]

private theorem X_int {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (X s) (Set.Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => x * Real.exp (-s.re*x)) (Set.Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (by norm_num) (by norm_num) hs
  have hc : Continuous (X s) := by unfold X E; fun_prop
  apply h.mono' hc.aestronglyMeasurable
  have he : ∀ᵐ x ∂volume.restrict (Set.Ioi (0:ℝ)), 0 < x :=
    ae_restrict_mem measurableSet_Ioi
  refine he.mono ?_
  intro x hx
  change ‖(x:ℂ)*E s x‖ ≤ x * Real.exp (-s.re*x)
  rw [norm_mul, Complex.norm_of_nonneg (show 0 ≤ x from le_of_lt hx), norm_E]

private theorem laplace_X {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Set.Ioi (0:ℝ), X s x) = 1/s^2 := by
  have hsn : s ≠ 0 := by intro he; simpa [he] using hs
  have ha : (-s).re < 0 := by simpa using hs
  have hi : IntegrableOn (E s) (Set.Ioi 0) := integrableOn_exp_mul_complex_Ioi ha 0
  have hder (x : ℝ) : HasDerivAt (X s) (E s x + (-s)*X s x) x := by
    have he := (((hasDerivAt_id (x:ℂ)).const_mul (-s)).cexp)
    have hd := ((hasDerivAt_id (x:ℂ)).mul he).comp_ofReal
    convert hd using 1 <;> first | rfl | (dsimp [X,E,id]; ring)
  have ht : Tendsto (X s) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) s.re hs).congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simp only [Real.rpow_one, X, norm_mul, Complex.norm_of_nonneg hx, norm_E]
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0:ℝ))
    (fun x _ => hder x) (hi.add ((X_int hs).const_mul (-s))) ht
  change (∫ x in Set.Ioi (0:ℝ), E s x + (-s)*X s x) = 0 - X s 0 at he
  rw [integral_add hi ((X_int hs).const_mul (-s)), integral_const_mul] at he
  have he0 : (∫ x in Set.Ioi (0:ℝ), E s x) = 1/s := by
    simpa [E] using integral_exp_mul_complex_Ioi ha 0
  rw [he0, show X s 0 = 0 by simp [X], sub_zero] at he
  field_simp [hsn] at he ⊢
  linear_combination -he

private theorem P_indicator (s : ℂ) : P s = (Set.Ioi (0:ℝ)).indicator (X s) := by
  funext x
  by_cases hx : 0 < x
  · simp [P,X,Set.mem_Ioi.mpr hx,max_eq_left hx.le]
  · simp [P, hx, max_eq_right (le_of_not_gt hx)]

private theorem shift_P (s : ℂ) (a x : ℝ) :
    E s x * (max (x+a) 0 : ℝ) = Complex.exp ((a:ℂ)*s) * P s (x+a) := by
  simp only [P,E]
  rw [mul_left_comm (Complex.exp _) _ (Complex.exp _), ← Complex.exp_add]
  simp only [Complex.ofReal_add]
  rw [show (a:ℂ)*s + -s*((x:ℂ)+(a:ℂ)) = -s*(x:ℂ) by ring]
  ring

private theorem weighted_eq (s : ℂ) (h x : ℝ) :
    E s x * (ramp h x : ℂ) =
      (Complex.exp ((h:ℂ)*s)*P s (x+h) - Complex.exp (-(h:ℂ)*s)*P s (x+(-h)))/(2*(h:ℂ)) := by
  rw [← shift_P s h x, ← Complex.ofReal_neg, ← shift_P s (-h) x]
  unfold ramp
  push_cast
  simp only [← sub_eq_add_neg]
  ring

private theorem weighted_int {s : ℂ} (hs : 0 < s.re) (h : ℝ) :
    Integrable (fun x : ℝ => E s x * (ramp h x : ℂ)) := by
  have hi : Integrable (P s) := by rw [P_indicator]; exact (X_int hs).integrable_indicator measurableSet_Ioi
  simp_rw [weighted_eq]
  exact (((hi.comp_add_right h).const_mul _).sub ((hi.comp_add_right (-h)).const_mul _)).div_const _

theorem dampedRamp_integrable (h : ℝ) {c : ℝ} (hc : 0 < c) : Integrable (dampedRamp h c) := by
  refine (weighted_int (s := (c:ℂ)) hc h).congr (ae_of_all _ fun x => ?_)
  simp only [dampedRamp, E, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]

theorem ramp_laplace {s : ℂ} (hs : 0 < s.re) (h : ℝ) :
    (∫ x : ℝ, E s x * (ramp h x : ℂ)) = kernel h s := by
  have hi : Integrable (P s) := by rw [P_indicator]; exact (X_int hs).integrable_indicator measurableSet_Ioi
  have hp : (∫ x : ℝ, P s x) = 1/s^2 := by
    rw [P_indicator, integral_indicator measurableSet_Ioi, laplace_X hs]
  simp_rw [weighted_eq]
  rw [integral_div, integral_sub ((hi.comp_add_right h).const_mul _) ((hi.comp_add_right (-h)).const_mul _),
    integral_const_mul, integral_const_mul, integral_add_right_eq_self, integral_add_right_eq_self, hp]
  unfold kernel
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem ramp_fourier (h : ℝ) {c : ℝ} (hc : 0 < c) (v : ℝ) :
    𝓕 (dampedRamp h c) v = kernel h (probe c v) := by
  have hs : 0 < (probe c v).re := by simpa [probe,Complex.mul_re] using hc
  rw [Real.fourier_real_eq_integral_exp_smul, ← ramp_laplace hs]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp only [smul_eq_mul, dampedRamp, E, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [probe, Complex.ofReal_mul]
    push_cast
    ring

theorem kernel_integrable {h c : ℝ} (hh : 0 < h) (hc : 0 < c) :
    Integrable (fun v : ℝ => kernel h (probe c v)) := by
  let B := Real.exp (h*c) + Real.exp (-h*c)
  let b := 2*Real.pi/c
  have hb : b ≠ 0 := by dsimp [b]; positivity
  apply ((integrable_inv_one_add_mul_sq hb).const_mul (B/(2*h*c^2))).mono'
  · apply Measurable.aestronglyMeasurable
    unfold kernel probe
    fun_prop
  · exact ae_of_all _ fun v => by
      have hnorm : ‖probe c v‖^2 = c^2*(1+(b*v)^2) := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [probe, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        dsimp only [b]
        field_simp [hc.ne']
        <;> ring
      have hnum : ‖Complex.exp ((h:ℂ)*probe c v) - Complex.exp (-(h:ℂ)*probe c v)‖ ≤ B := by
        apply (norm_sub_le _ _).trans
        simp [B,Complex.norm_exp,probe,Complex.mul_re]
      change ‖kernel h (probe c v)‖ ≤ (B/(2*h*c^2))*(1+(b*v)^2)⁻¹
      rw [kernel,norm_div,norm_mul,norm_mul,norm_pow,Complex.norm_two,
        Complex.norm_of_nonneg hh.le,hnorm]
      calc
        _ ≤ B / (2*h*(c^2*(1+(b*v)^2))) := div_le_div_of_nonneg_right hnum (by positivity)
        _ = _ := by simp only [div_eq_mul_inv, _root_.mul_inv_rev]; ring

theorem ramp_fourier_inversion {h c : ℝ} (hh : 0 < h) (hc : 0 < c) (x : ℝ) :
    (∫ v : ℝ, Complex.exp (((2*Real.pi*v*x:ℝ):ℂ)*Complex.I) * kernel h (probe c v)) =
      dampedRamp h c x := by
  have hF : 𝓕 (dampedRamp h c) = fun v => kernel h (probe c v) := funext (ramp_fourier h hc)
  have hcont : Continuous (dampedRamp h c) := by unfold dampedRamp ramp; fun_prop
  have hiF : Integrable (𝓕 (dampedRamp h c)) := hF ▸ kernel_integrable hh hc
  have hinv := congrFun (hcont.fourierInv_fourier_eq (dampedRamp_integrable h hc) hiF) x
  rw [hF, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hinv
  simpa only [show ∀ v : ℝ, -2*Real.pi*v*(-x) = 2*Real.pi*v*x from fun v => by ring,
    smul_eq_mul] using hinv

#print axioms ramp_fourier
#print axioms ramp_fourier_inversion
end RHConnections.PerronRamp
