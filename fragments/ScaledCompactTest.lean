import Verified

open MeasureTheory Set Filter
noncomputable section
namespace RHConnections.SmoothedPrimeLimit
open PoleCompensation SpectralTail EulerGeometricLimit ArchimedeanLimit ChebyshevCriterion

def scaleTest (T : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((1/2:ℂ)*(x:ℂ)-(T:ℂ))*f (x-T)

theorem scaleTest_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (T : ℝ) :
    ContDiff ℝ ∞ (scaleTest T f) := by
  have he (x : ℝ) : Complex.exp ((1/2:ℂ)*(x:ℂ)-(T:ℂ)) =
      (Real.exp (x/2-T):ℂ) := by simp [Complex.ofReal_exp,Complex.ofReal_div,div_eq_mul_inv,mul_comm]
  have hExp : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (x/2-T)) := by fun_prop
  have hShift : ContDiff ℝ ∞ (fun x => f (x-T)) := hf.comp (by fun_prop)
  change ContDiff ℝ ∞ (fun x : ℝ => Complex.exp ((1/2:ℂ)*(x:ℂ)-(T:ℂ))*f (x-T))
  simp_rw [he]
  exact (Complex.ofRealCLM.contDiff.comp hExp).mul hShift

theorem scaleTest_compact {f : ℝ → ℂ} (hf : HasCompactSupport f) (T : ℝ) :
    HasCompactSupport (scaleTest T f) := by
  let S := (fun x : ℝ => x+T) '' tsupport f
  have hcont : Continuous (fun x : ℝ => x+T) := by fun_prop
  have hS : IsCompact S := hf.isCompact.image hcont
  refine HasCompactSupport.intro hS ?_
  intro x hx
  have hz : f (x-T) = 0 := by
    by_contra h
    exact hx ⟨x-T,subset_tsupport f h,by ring⟩
  simp [scaleTest,hz]

theorem scaleTest_vanishes_left {f : ℝ → ℂ} (hf : ∀ x ≤ 0, f x = 0)
    {T x : ℝ} (hT : 0 ≤ T) (hx : x ≤ 0) : scaleTest T f x = 0 := by
  simp only [scaleTest,hf _ (by linarith : x-T ≤ 0),mul_zero]

private theorem integral_Ioi_zero_eq_integral {g : ℝ → ℂ} (h : ∀ x ≤ 0, g x = 0) :
    (∫ x in Ioi (0:ℝ), g x) = ∫ x : ℝ, g x := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ Ioi (0:ℝ)
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,h x (le_of_not_gt hx)]

theorem scaleTest_pairing {f : ℝ → ℂ} (hf : ∀ x ≤ 0, f x = 0)
    {T : ℝ} (hT : 0 ≤ T) (w : ℂ) :
    (∫ x in Ioi (0:ℝ), Complex.exp (w*(x:ℂ))*scaleTest T f x) =
      Complex.exp ((w-1/2)*(T:ℂ)) *
        ∫ x in Ioi (0:ℝ), Complex.exp ((w+1/2)*(x:ℂ))*f x := by
  rw [integral_Ioi_zero_eq_integral (fun x hx => by rw [scaleTest_vanishes_left hf hT hx,mul_zero]),
    integral_Ioi_zero_eq_integral (fun x hx => by rw [hf x hx,mul_zero])]
  have he (x : ℝ) : Complex.exp (w*(x:ℂ))*scaleTest T f x =
      Complex.exp ((w-1/2)*(T:ℂ)) * (Complex.exp ((w+1/2)*((x-T:ℝ):ℂ))*f (x-T)) := by
    simp only [scaleTest,← mul_assoc,← Complex.exp_add,Complex.ofReal_sub]
    congr 2
    ring
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self (fun x : ℝ => Complex.exp ((w+1/2)*(x:ℂ))*f x) T

theorem prime_scaled_test_eq (T : ℝ) (f : ℝ → ℂ) :
    (∑' n : ℕ, halfWeight n*scaleTest T f (Real.log n)) =
      Complex.exp (-(T:ℂ)) * ∑' n : ℕ, mangoldtCoeff n*f (Real.log n-T) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [halfWeight,mangoldtCoeff]
  have hnC : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [halfWeight,LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hnC,scaleTest]
  simp only [mangoldtCoeff,← Complex.natCast_log,div_eq_mul_inv,← Complex.exp_neg]

  have he : -(Complex.log (n:ℂ)*(1/2:ℂ)) + ((1/2:ℂ)*Complex.log (n:ℂ)-(T:ℂ)) = -(T:ℂ) := by ring
  calc
    _ = (mangoldtCoeff n) *
        (Complex.exp (-(Complex.log (n:ℂ)*(1/2:ℂ))) *
          Complex.exp ((1/2:ℂ)*Complex.log (n:ℂ)-(T:ℂ))) * f (Real.log n-T) := by
      unfold mangoldtCoeff
      simp only [Complex.natCast_log]
      ring
    _ = _ := by rw [← Complex.exp_add,he]; unfold mangoldtCoeff; ring

theorem scaled_zero_term_eq {f : ℝ → ℂ} (hf : ∀ x ≤ 0, f x = 0)
    {T : ℝ} (hT : 0 ≤ T) (r : NontrivialZetaZero) :
    compactZeroTerm (scaleTest T f) r =
      Complex.exp ((r.val-1)*(T:ℂ)) * compactZeroTerm (scaleTest 0 f) r := by
  unfold compactZeroTerm
  rw [scaleTest_pairing hf hT,scaleTest_pairing hf (le_refl 0)]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul]
  rw [show r.val-(1/2:ℂ)-1/2 = r.val-1 by ring]
  ring

theorem scaled_zero_sum_tendsto_zero {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hf0 : ∀ x ≤ 0, f x = 0) :
    Tendsto (fun T : ℝ => ∑' r : NontrivialZetaZero, compactZeroTerm (scaleTest T f) r) atTop (nhds 0) := by
  have hB := compact_zero_terms_abs_summable (scaleTest_smooth hf 0) (scaleTest_compact hc 0)
    (scaleTest_vanishes_left hf0 (le_refl 0) (le_refl 0))
  have hpoint (r : NontrivialZetaZero) : Tendsto
      (fun T : ℝ => Complex.exp ((r.val-1)*(T:ℂ))*compactZeroTerm (scaleTest 0 f) r)
      atTop (nhds 0) := by
    have hβ : r.val.re-1 < 0 := sub_neg.mpr r.property.1.2
    have ht : Tendsto (fun T : ℝ => (r.val.re-1)*T) atTop atBot :=
      tendsto_const_nhds.neg_mul_atTop hβ tendsto_id
    have hnorm : Tendsto (fun T : ℝ => ‖Complex.exp ((r.val-1)*(T:ℂ))‖) atTop (nhds 0) := by
      simpa only [Complex.norm_exp,Complex.mul_re,Complex.sub_re,Complex.one_re,
        Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Function.comp_apply]
        using (show Tendsto (fun T : ℝ => Real.exp ((r.val.re-1)*T)) atTop (nhds 0) from Real.tendsto_exp_atBot.comp ht)
    have h0 := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    simpa only [zero_mul] using h0.mul_const (compactZeroTerm (scaleTest 0 f) r)
  have hmaj : ∀ᶠ T : ℝ in atTop, ∀ r : NontrivialZetaZero,
      ‖Complex.exp ((r.val-1)*(T:ℂ))*compactZeroTerm (scaleTest 0 f) r‖ ≤
        ‖compactZeroTerm (scaleTest 0 f) r‖ := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT r
    rw [norm_mul,Complex.norm_exp]
    apply (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)).trans_eq (one_mul _)
    rw [Real.exp_le_one_iff]
    simp only [Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr r.property.1.2.le) hT
  have hlim := tendsto_tsum_of_dominated_convergence hB hpoint hmaj
  rw [tsum_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  simp only [scaled_zero_term_eq hf0 hT]

end RHConnections.SmoothedPrimeLimit
