import Verified
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace RHConnections.PerronRamp
open ZetaDiskLog VerticalIntegralShift

private theorem kernel_eq_bounds (h : ℝ) (s : ℂ) :
    kernel h s = PerronRampBounds.kernel h s := by
  simp only [kernel,PerronRampBounds.kernel,neg_mul]

private theorem vertical_re (b t : ℝ) : (PerronRampBounds.vertical b t).re = b := by
  simp [PerronRampBounds.vertical,Complex.add_re,Complex.mul_re]

private theorem vertical_im (b t : ℝ) : (PerronRampBounds.vertical b t).im = t := by
  simp [PerronRampBounds.vertical,Complex.add_im,Complex.mul_im]

private theorem perron_integrand_analytic (hRH : RiemannHypothesis)
    {s : ℂ} (hs : 1/2 < s.re) {h X : ℝ} (hh : 0 < h) (hX : 0 < X) :
    AnalyticAt ℂ (perronIntegrand h X) s := by
  have hS : s ≠ 0 := fun he => by norm_num [he] at hs
  have hH : (h:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hG := zetaReciprocal_analytic_of_RH hRH s hs
  have hx : AnalyticAt ℂ (fun s => (X:ℂ)^s) s := by
    change AnalyticAt ℂ (fun s : ℂ => (X:ℂ)^s) s
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne')]
    fun_prop
  have hk : AnalyticAt ℂ (kernel h) s := by
    unfold kernel
    have hD : (2:ℂ)*(h:ℂ)*s^2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hH) (pow_ne_zero _ hS)
    exact (show AnalyticAt ℂ (fun z : ℂ =>
      Complex.exp ((h:ℂ)*z)-Complex.exp (-(h:ℂ)*z)) s by fun_prop).div
      (by fun_prop) hD
  exact (hG.mul hx).mul hk

private theorem perron_frequency_rescale (h X b : ℝ) :
    (∫ v : ℝ, perronIntegrand h X (probe b v)) =
      (|2*Real.pi|)⁻¹ • ∫ t : ℝ, perronIntegrand h X (PerronRampBounds.vertical b t) := by
  simpa only [abs_inv,probe,PerronRampBounds.vertical] using Measure.integral_comp_mul_left
    (fun t => perronIntegrand h X (PerronRampBounds.vertical b t)) (2*Real.pi)

theorem smoothedMertens_bound_of_RH (hRH : RiemannHypothesis)
    {b η : ℝ} (hb : 1/2 < b) (hb₁ : b < 1) (hη : 0 < η) (hη₁ : η < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X h : ℝ), 1 ≤ X → 0 < h → h ≤ 1 →
      ‖smoothedMertens h X‖ ≤ C * X^b * h^(-η) := by
  obtain ⟨C,hC,hRecip⟩ := zetaReciprocal_subpower_of_RH hRH hb hb₁ hη
  let D := C*(10:ℝ)^η
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨A,hA,hK⟩ := PerronRampBounds.weighted_kernel_integral_bound
    (by linarith : 0 < b) (by linarith : b ≤ 3) hη hη₁
  refine ⟨(|2*Real.pi|)⁻¹*(D*A),by positivity,?_⟩
  intro X h hX hh hh₁
  have hXp : 0 < X := zero_lt_one.trans_le hX
  let F := perronIntegrand h X
  have hmain (x t : ℝ) (hx : x ∈ Icc b 2) :
      ‖F (PerronRampBounds.vertical x t)‖ ≤
      (D*X^x)*((1+|t|)^η*‖PerronRampBounds.kernel h (PerronRampBounds.vertical x t)‖) := by
    let s := PerronRampBounds.vertical x t
    have hrecip := hRecip s (by simpa only [s,vertical_re] using hx.1)
      (by have := hx.2; simp only [s,vertical_re]; linarith)
    have he : (|t|+10)^η ≤ (10:ℝ)^η*(1+|t|)^η := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      apply Real.rpow_le_rpow (by positivity) _ hη.le
      linarith [abs_nonneg t]
    have hrecip' : ‖zetaReciprocal s‖ ≤ C*(|t|+10)^η := by
      simpa only [s,vertical_im] using hrecip
    have hR : ‖zetaReciprocal s‖ ≤ D*(1+|t|)^η :=
      hrecip'.trans
        (by dsimp [D]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left he hC)
    dsimp only [F,perronIntegrand]
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hXp,vertical_re,kernel_eq_bounds]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hR (by positivity)) (norm_nonneg _)).trans_eq (by ring)
  have hVert (x : ℝ) (hx : x ∈ Icc b 2) :
      Integrable (fun t : ℝ => F (PerronRampBounds.vertical x t)) := by
    have hi := PerronRampBounds.weighted_kernel_integrable hh hh₁
      (by linarith [hx.1] : 0 < x) (by linarith [hx.2] : x ≤ 3) hη₁
    apply (hi.const_mul (D*X^x)).mono'
    · have h : Continuous (fun t => F (PerronRampBounds.vertical x t)) := by
        apply continuous_iff_continuousAt.mpr
        intro t
        exact (perron_integrand_analytic hRH (by rw [vertical_re]; linarith [hx.1]) hh hXp).continuousAt.comp
          (by unfold PerronRampBounds.vertical; fun_prop)
      exact h.aestronglyMeasurable
    · exact ae_of_all _ (hmain x · hx)
  have hb2 : b ≤ (2:ℝ) := by linarith
  have hbVert := hVert b ⟨le_rfl,hb2⟩
  have h2Vert := hVert 2 ⟨hb2,le_rfl⟩
  let W : ℝ := D*X^2*(2:ℝ)^η*Real.exp 3/h
  have hdec : Tendsto (fun t : ℝ => W*t^(η-2)) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop (show 0 < 2-η by linarith)).const_mul W
    simpa only [neg_sub, mul_zero] using ht
  have hedge (T : ℝ) (hT : 1 ≤ T) (x : ℝ) (hx : x ∈ Icc b 2) (t : ℝ)
      (heq : |t| = T) : ‖F (PerronRampBounds.vertical x t)‖ ≤ W*T^(η-2) := by
    let s := PerronRampBounds.vertical x t
    have hn : T ≤ ‖s‖ := by simpa only [s,vertical_im,heq] using Complex.abs_im_le_norm s
    have hmain' := hmain x t hx
    have hT0 : 0 < T := by linarith
    have hsq : T^2 ≤ ‖s‖^2 := pow_le_pow_left₀ hT0.le hn 2
    have hKn : ‖PerronRampBounds.kernel h s‖ ≤ Real.exp 3/(h*T^2) :=
      ((PerronRampBounds.kernel_norm_min hh hh₁
        (by linarith [hx.1] : 0 < x) (by linarith [hx.2] : x ≤ 3) t).trans (min_le_right _ _)).trans
        (div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
          (mul_le_mul_of_nonneg_left hsq hh.le))
    have hpow : (1+|t|)^η ≤ (2:ℝ)^η*T^η := by
      rw [heq, ← Real.mul_rpow (by norm_num) hT0.le]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hη.le
    have hXpow : X^x ≤ X^2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hX hx.2
    calc
      _ ≤ (D*X^x)*((1+|t|)^η*‖PerronRampBounds.kernel h s‖) := hmain'
      _ ≤ (D*X^2)*(((2:ℝ)^η*T^η)*(Real.exp 3/(h*T^2))) := by gcongr
      _ = W*T^(η-2) := by
        dsimp [W]
        rw [Real.rpow_sub hT0]
        simp only [Real.rpow_two, div_eq_mul_inv, _root_.mul_inv_rev]
        ring
  have hshift := vertical_integral_eq (F := F) hb2
    (fun s hs => perron_integrand_analytic hRH (hb.trans_le hs.1) hh hXp)
    hbVert h2Vert (fun T => W*T^(η-2)) hdec (by
      filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT x hx
      exact ⟨hedge T hT x hx (-T) (by rw [abs_neg,abs_of_nonneg (by linarith)]),
        hedge T hT x hx T (abs_of_nonneg (by linarith))⟩)
  have hshift' : (∫ t : ℝ, perronIntegrand h X (PerronRampBounds.vertical b t)) =
      ∫ t : ℝ, perronIntegrand h X (PerronRampBounds.vertical 2 t) := hshift
  rw [smoothedMertens_eq_euler_integral hh (show (1:ℝ)<2 by norm_num) hXp, perron_frequency_rescale,
    ← hshift', norm_smul, Real.norm_of_nonneg (by positivity)]
  have hI := PerronRampBounds.weighted_kernel_integrable hh hh₁
    (by linarith : 0 < b) (by linarith : b ≤ 3) hη₁
  have hBoundInt :
      ‖∫ t : ℝ, F (PerronRampBounds.vertical b t)‖ ≤ (D*X^b)*(A*h^(-η)) := by
    calc
      _ ≤ ∫ t : ℝ, ‖F (PerronRampBounds.vertical b t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (D*X^b)*((1+|t|)^η*‖PerronRampBounds.kernel h (PerronRampBounds.vertical b t)‖) :=
        integral_mono hbVert.norm (hI.const_mul _) (fun t => hmain b t ⟨le_rfl,hb2⟩)
      _ ≤ _ := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hK h hh hh₁) (by positivity)
  exact (mul_le_mul_of_nonneg_left hBoundInt (by positivity)).trans_eq (by ring)

end RHConnections.PerronRamp
