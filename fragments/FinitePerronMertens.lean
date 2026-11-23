import Verified
import FinitePerronTails

noncomputable section
open MeasureTheory Set Complex
open scoped Interval

namespace RHConnections.FinitePerron
open PerronRamp ZetaDiskLog PoleCompensation MertensCriterion

private theorem finite_probe_re (b t : ℝ) : (PerronRampBounds.vertical b t).re=b := by
  simp [PerronRampBounds.vertical,Complex.mul_re]

private theorem finite_probe_im (b t : ℝ) : (PerronRampBounds.vertical b t).im=t := by
  simp [PerronRampBounds.vertical,Complex.mul_im]

theorem perron_analytic_at_of_reg_nonzero {h X : ℝ} (hh : 0<h) (hX : 0<X)
    {s : ℂ} (hs : 0<s.re) (hreg : regularizedZeta s≠0) :
    AnalyticAt ℂ (perronIntegrand h X) s := by
  have hS : s≠0 := fun he => by norm_num [he] at hs
  have hH : (h:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hG : AnalyticAt ℂ zetaReciprocal s :=
    (analyticAt_id.sub analyticAt_const).div (regularizedZeta_analytic s) hreg
  have hx : AnalyticAt ℂ (fun s : ℂ => (X:ℂ)^s) s := by
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne')]
    fun_prop
  have hk : AnalyticAt ℂ (kernel h) s := by
    unfold kernel
    have hD : (2:ℂ)*(h:ℂ)*s^2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hH) (pow_ne_zero _ hS)
    exact (show AnalyticAt ℂ (fun z : ℂ =>
      Complex.exp ((h:ℂ)*z)-Complex.exp (-(h:ℂ)*z)) s by fun_prop).div (by fun_prop) hD
  exact (hG.mul hx).mul hk

theorem finite_perron_mertens_bound {X h b c T U V W : ℝ}
    (hX : 1≤X) (hh : 0<h) (hh1 : h≤1) (hb : 1/2≤b) (hbc : b≤c)
    (hc : 1<c) (hc3 : c≤3) (hT : 0<T)
    (hU : 0≤U) (hV : 0≤V) (hW : 0≤W)
    (hreg : ∀ s : ℂ, s.re ∈ Icc b c → s.im ∈ Icc (-T) T → regularizedZeta s≠0)
    (hleft : ∀ t ∈ Icc (-T) T, ‖zetaReciprocal (PerronRampBounds.vertical b t)‖ ≤ U)
    (hedge : ∀ x ∈ Icc b c, ∀ t, |t|=T →
      ‖zetaReciprocal (PerronRampBounds.vertical x t)‖ ≤ V)
    (hright : ∀ t, ‖zetaReciprocal (PerronRampBounds.vertical c t)‖ ≤ W) :
    ‖mertens X‖ ≤ 3*(X*h+1) + (|2*Real.pi|)⁻¹*
      (4*T*U*X^b*(2+Real.exp 3)+2*(c-b)*V*X^c*Real.exp 3/(h*T^2)+
        2*W*X^c*Real.exp 3/(h*T)) := by
  have hXp := zero_lt_one.trans_le hX
  let F := perronIntegrand h X
  let v := PerronRampBounds.vertical
  let A := 2*U*X^b*(2+Real.exp 3)
  let B := V*X^c*Real.exp 3/(h*T^2)
  let D := W*X^c*Real.exp 3/h
  have he (x t : ℝ) : ‖F (v x t)‖ =
      ‖zetaReciprocal (v x t)‖*X^x*‖PerronRampBounds.kernel h (v x t)‖ := by
    unfold F perronIntegrand
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hXp,finite_probe_re]
    simp only [kernel,PerronRampBounds.kernel,neg_mul]
  have hA (t : ℝ) (ht : t ∈ Icc (-T) T) : ‖F (v b t)‖ ≤ A := by
    have hd : 1/2 ≤ ‖v b t‖ := hb.trans (by simpa only [v,finite_probe_re] using Complex.re_le_norm (v b t))
    have hk := PerronRampBounds.kernel_norm_linear hh hh1 (s := v b t)
      (by rw [finite_probe_re]; linarith) (by rw [finite_probe_re]; linarith)
    have hk' : ‖PerronRampBounds.kernel h (v b t)‖ ≤ 2*(2+Real.exp 3) :=
      hk.trans ((div_le_div_of_nonneg_left (by positivity) (by norm_num) hd).trans_eq (by ring))
    rw [he]
    dsimp only [A]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right (hleft t ht) (by positivity)) hk'
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hK (x t : ℝ) (hx : x ∈ Icc b c) (ht : 0 < |t|) :
      ‖PerronRampBounds.kernel h (v x t)‖ ≤ Real.exp 3/(h*|t|^2) := by
    have hx0 : 0 < (v x t).re := by rw [finite_probe_re]; linarith [hx.1]
    have hx3 : (v x t).re ≤ 3 := by rw [finite_probe_re]; exact hx.2.trans hc3
    have hn : |t|≤‖v x t‖ := by simpa only [v,finite_probe_im] using Complex.abs_im_le_norm (v x t)
    exact (PerronRampBounds.kernel_norm_quadratic hh hh1 hx0 hx3).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hn _) hh.le))
  have hEdge (x : ℝ) (hx : x ∈ Icc b c) (t : ℝ) (ht : |t|=T) : ‖F (v x t)‖ ≤ B := by
    have hk := hK x t hx (ht ▸ hT : 0 < |t|)
    rw [ht] at hk
    rw [he]
    dsimp only [B]
    have hxPow := Real.rpow_le_rpow_of_exponent_le hX hx.2
    exact (mul_le_mul (mul_le_mul (hedge x hx t ht) hxPow (by positivity) hV) hk
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hAnalytic : AnalyticOnNhd ℂ F {z | z.re ∈ Icc b c ∧ z.im ∈ Icc (-T) T} := by
    intro s hs
    exact perron_analytic_at_of_reg_nonzero hh hXp (by linarith [hs.1.1]) (hreg s hs.1 hs.2)
  have hcentral := central_vertical_bound (F := F) hbc hT.le hAnalytic hA
    (fun x hx => ⟨hEdge x hx (-T) (by rw [abs_neg,abs_of_pos hT]),
      hEdge x hx T (abs_of_pos hT)⟩)
  have hContinuous : Continuous (fun t : ℝ => F (v c t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hcr : 1 < (v c t).re := by simpa only [v,finite_probe_re] using hc
    have hreg' : regularizedZeta (v c t) ≠ 0 := by
      have hn : v c t ≠ 1 := by intro he; norm_num [he] at hcr
      rw [(regularizedZeta_germ hn).eq_of_nhds]
      exact mul_ne_zero (sub_ne_zero.mpr hn) (riemannZeta_ne_zero_of_one_le_re hcr.le)
    exact (perron_analytic_at_of_reg_nonzero hh hXp (by linarith) hreg').continuousAt.comp
      (by unfold v PerronRampBounds.vertical; fun_prop)
  have hiK : Integrable (fun t : ℝ => ‖PerronRampBounds.kernel h (v c t)‖) := by
    simpa only [Real.rpow_zero,one_mul] using PerronRampBounds.weighted_kernel_integrable (η := 0)
      hh hh1 (by linarith : 0<c) hc3 (by norm_num)
  have hfi : Integrable (fun t : ℝ => F (v c t)) := by
    apply (hiK.const_mul (W*X^c)).mono' hContinuous.aestronglyMeasurable
    apply ae_of_all
    intro t
    rw [he]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hright t) (by positivity)) (norm_nonneg _)
  have hTail (t : ℝ) (ht : T≤|t|) : ‖F (v c t)‖ ≤ D*|t|^(-2:ℝ) := by
    have hpos := hT.trans_le ht
    rw [he,Real.rpow_neg hpos.le,Real.rpow_two]
    have hk := hK c t ⟨hbc,le_rfl⟩ hpos
    exact (mul_le_mul (mul_le_mul_of_nonneg_right (hright t) (by positivity)) hk
      (norm_nonneg _) (by positivity)).trans_eq (by dsimp [D]; ring)
  have htbound := integral_tails_bound hfi hT (by dsimp [D]; positivity) hTail
  have hWhole : ‖∫ t : ℝ, F (v c t)‖ ≤ (2*T*A+2*(c-b)*B)+2*D/T := by
    have htriangle := norm_add_le (∫ t in -T..T,F (v c t))
      ((∫ t : ℝ,F (v c t)) - ∫ t in -T..T,F (v c t))
    rw [add_sub_cancel] at htriangle
    exact htriangle.trans (add_le_add hcentral htbound)
  have hsmooth := smoothedMertens_eq_euler_integral hh hc hXp
  have hscale : (∫ t : ℝ, F (probe c t)) =
      (|2*Real.pi|)⁻¹ • ∫ t : ℝ, F (v c t) := by
    simpa only [abs_inv,probe,v,PerronRampBounds.vertical] using Measure.integral_comp_mul_left
      (fun t => F (v c t)) (2*Real.pi)
  rw [hscale] at hsmooth
  have htr := norm_sub_le (smoothedMertens h X) (smoothedMertens h X-mertens X)
  rw [sub_sub_cancel] at htr
  apply htr.trans
  have hs : ‖smoothedMertens h X‖ ≤ (|2*Real.pi|)⁻¹*((2*T*A+2*(c-b)*B)+2*D/T) := by
    rw [hsmooth,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hWhole (by positivity)
  exact (add_le_add hs (smoothedMertens_error hX hh hh1)).trans_eq (by dsimp [A,B,D]; ring)

end RHConnections.FinitePerron
