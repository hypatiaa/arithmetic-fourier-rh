import Verified

open MeasureTheory Set Filter
noncomputable section
namespace RHConnections.SmoothedPrimeLimit
open PoleCompensation SpectralTail ArchimedeanLimit EulerGeometricLimit ChebyshevCriterion

theorem scaled_real_place_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hf0 : ∀ x ≤ 0, f x = 0) {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ x in Ioi (0:ℝ), (realPlaceKernel x:ℂ)*scaleTest T f x‖ ≤
      (2*∫ x : ℝ, ‖f x‖)*Real.exp (-T) := by
  let F : ℝ → ℂ := fun x => (realPlaceKernel x:ℂ)*scaleTest T f x
  let H : ℝ → ℝ := fun x => (2*Real.exp (-T))*‖f (x-T)‖
  have hfn : Integrable (fun x : ℝ => ‖f x‖) := (hf.continuous.integrable_of_hasCompactSupport hc).norm
  have hH : Integrable H := (hfn.comp_sub_right T).const_mul _
  have hbound (x : ℝ) (hx : 0 < x) : ‖F x‖ ≤ H x := by
    by_cases hxt : x ≤ T
    · simp only [F,scaleTest,hf0 _ (by linarith : x-T ≤ 0),mul_zero,norm_zero,H,le_refl]
    have hx1 : 1 ≤ x := hT.trans (lt_of_not_ge hxt).le
    have hd : 1/2 ≤ 1-Real.exp (-2*x) := by
      have h := realPlaceKernel_denominator_bound hx
      have hv : 1/2 ≤ (2*x)/(1+2*x) := (le_div_iff₀ (by positivity)).mpr (by linarith)
      exact hv.trans h
    have hd' : 0 < 1-Real.exp (-2*x) := (by norm_num : (0:ℝ)<1/2).trans_le hd
    change ‖(realPlaceKernel x:ℂ)*scaleTest T f x‖ ≤ H x
    rw [norm_mul, Complex.norm_of_nonneg (realPlaceKernel_nonneg hx),scaleTest,norm_mul,Complex.norm_exp]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    have he : ((1/2:ℂ).re) = 1/2 := by norm_num [Complex.div_re]
    rw [he,realPlaceKernel]
    calc
      _ = (Real.exp (-T)/(1-Real.exp (-2*x)))*‖f (x-T)‖ := by
        have he' : Real.exp (-x/2)*Real.exp (1/2*x-T) = Real.exp (-T) := by
          rw [← Real.exp_add,show -x/2+(1/2*x-T) = -T by ring]
        calc
          _ = (Real.exp (-x/2)*Real.exp (1/2*x-T))/(1-Real.exp (-2*x))*‖f (x-T)‖ := by ring
          _ = _ := by rw [he']
      _ ≤ H x := mul_le_mul_of_nonneg_right ((div_le_iff₀ hd').mpr
        (by nlinarith [mul_le_mul_of_nonneg_left hd (Real.exp_pos (-T)).le])) (norm_nonneg _)
  have hFi : IntegrableOn F (Ioi (0:ℝ)) := by
    apply hH.integrableOn.mono'
    · have hk : Measurable (fun x => (realPlaceKernel x:ℂ)) := by
        apply Complex.continuous_ofReal.measurable.comp
        unfold realPlaceKernel
        fun_prop
      exact hk.aestronglyMeasurable.mul (scaleTest_smooth hf T).continuous.aestronglyMeasurable
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => hbound x hx))
  have hK : IntegrableOn (fun x => ‖F x‖) (Ioi (0:ℝ)) := Integrable.norm hFi
  change ‖∫ x in Ioi (0:ℝ), F x‖ ≤ _
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ x in Ioi (0:ℝ), H x := setIntegral_mono_on hK
      hH.integrableOn measurableSet_Ioi hbound
    _ ≤ ∫ x : ℝ, H x := setIntegral_le_integral hH (ae_of_all _ (fun x => by dsimp [H]; positivity))
    _ = _ := by
      change (∫ x : ℝ, (2*Real.exp (-T))*‖f (x-T)‖) = _
      rw [integral_const_mul,integral_sub_right_eq_self (fun x : ℝ => ‖f x‖) T]
      ring

theorem smoothed_prime_explicit_identity {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hf0 : ∀ x ≤ 0, f x = 0) {T : ℝ} (hT : 0 ≤ T) :
    Complex.exp (-(T:ℂ)) * (∑' n : ℕ, mangoldtCoeff n*f (Real.log n-T)) =
      (∫ x in Ioi (0:ℝ), Complex.exp (x:ℂ)*f x) +
      Complex.exp (-(T:ℂ))*(∫ x in Ioi (0:ℝ), f x) -
      (∫ x in Ioi (0:ℝ), (realPlaceKernel x:ℂ)*scaleTest T f x) -
      (∑' rho : NontrivialZetaZero, compactZeroTerm (scaleTest T f) rho) := by
  have h := zeta_explicit_formula_compact (scaleTest T f) (scaleTest_smooth hf T)
    (scaleTest_compact hc T) (scaleTest_vanishes_left hf0 hT le_rfl)
  rw [prime_scaled_test_eq,scaleTest_pairing hf0 hT,scaleTest_pairing hf0 hT] at h
  norm_num [show (1/2:ℂ)-(1/2:ℂ)=0 by ring,show (1/2:ℂ)+(1/2:ℂ)=1 by ring] at h
  unfold compactZeroTerm
  linear_combination h

private theorem real_decay : Tendsto (fun T : ℝ => Real.exp (-T)) atTop (nhds 0) :=
  Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

theorem smoothed_prime_limit {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hf0 : ∀ x ≤ 0, f x = 0) :
    Tendsto (fun T : ℝ => Complex.exp (-(T:ℂ)) * ∑' n : ℕ, mangoldtCoeff n*f (Real.log n-T))
      atTop (nhds (∫ x in Ioi (0:ℝ), Complex.exp (x:ℂ)*f x)) := by
  have hA : Tendsto (fun T : ℝ => ∫ x in Ioi (0:ℝ), (realPlaceKernel x:ℂ)*scaleTest T f x)
      atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa only [mul_zero] using real_decay.const_mul (2*∫ x : ℝ, ‖f x‖))
    exact (eventually_ge_atTop (1:ℝ)).mono (fun T hT => scaled_real_place_bound hf hc hf0 hT)
  have hL : Tendsto (fun T : ℝ => Complex.exp (-(T:ℂ))*(∫ x in Ioi (0:ℝ), f x))
      atTop (nhds 0) := by
    have h := tendsto_zero_iff_norm_tendsto_zero.mpr
      (show Tendsto (fun T : ℝ => ‖Complex.exp (-(T:ℂ))‖) atTop (nhds 0) from by
        simpa only [Complex.norm_exp,Complex.neg_re,Complex.ofReal_re] using real_decay)
    simpa only [zero_mul] using h.mul_const (∫ x in Ioi (0:ℝ), f x)
  have hS := scaled_zero_sum_tendsto_zero hf hc hf0
  have hP : Tendsto (fun _ : ℝ => ∫ x in Ioi (0:ℝ), Complex.exp (x:ℂ)*f x) atTop
      (nhds (∫ x in Ioi (0:ℝ), Complex.exp (x:ℂ)*f x)) := tendsto_const_nhds
  have h := ((hP.add hL).sub hA).sub hS
  simp only [add_zero,sub_zero] at h
  exact h.congr' ((eventually_ge_atTop (0:ℝ)).mono
    (fun T hT => (smoothed_prime_explicit_identity hf hc hf0 hT).symm))

end RHConnections.SmoothedPrimeLimit
