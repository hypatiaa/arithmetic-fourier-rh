import Verified

open MeasureTheory Filter ArithmeticFunction
open scoped Topology
noncomputable section
namespace RHConnections.PrimeErrorLaplace
open PoleCompensation ChebyshevCriterion ZetaAbelGrowth

def realPrimeError (x : ℝ) : ℝ := Chebyshev.psi x-x

theorem real_prime_error_at_nat (n : ℕ) :
    realPrimeError (n:ℝ) = ArithmeticFourierShortBlocks.primeRemainder n := rfl

theorem real_prime_error_fold (x : ℝ) :
    realPrimeError x = realPrimeError (⌊x⌋₊:ℝ) - (x-(⌊x⌋₊:ℝ)) := by
  unfold realPrimeError
  simp only [Chebyshev.psi_eq_sum_Icc,Nat.floor_natCast]
  ring

theorem real_prime_error_measurable : Measurable realPrimeError := by
  have hpsi : Monotone Chebyshev.psi := Chebyshev.psi_mono
  exact hpsi.measurable.sub measurable_id

private theorem psi_eq_real_psi (x : ℝ) :
    ChebyshevCriterion.psi x = (Chebyshev.psi x:ℂ) := by
  rw [Chebyshev.psi_eq_sum_Icc,Complex.ofReal_sum]
  unfold ChebyshevCriterion.psi mangoldtCoeff
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Icc.mp hn).2⟩
  · intro n hn hx
    have hN := (Finset.mem_Icc.mp hn).2
    have hz : n=0 := by
      by_contra hd
      apply hx
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd,hN⟩
    simp [hz]

theorem real_prime_error_linear {x : ℝ} (hx : 0≤x) :
    |realPrimeError x| ≤ (Real.log 4+5)*x := by
  have hpsi : 0 ≤ Chebyshev.psi x := by
    rw [Chebyshev.psi_eq_sum_Icc]
    exact Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
  unfold realPrimeError
  calc
    _ ≤ |Chebyshev.psi x|+|x| := abs_sub _ _
    _ ≤ (Real.log 4+4)*x+x := by
      rw [abs_of_nonneg hpsi,abs_of_nonneg hx]
      exact add_le_add (Chebyshev.psi_le_const_mul_self hx) (le_refl _)
    _ = _ := by ring

private theorem real_abel_remainder_nonneg {s : ℝ} (_ : 0<s) :
    0 ≤ (ZetaAbelGrowth.remainder (s:ℂ)).re := by
  rw [remainder_integral]
  have he : ∀ᵐ x ∂volume.restrict (Set.Ioi (1:ℝ)),
      frac x*(x:ℂ)^(-(s:ℂ)-1) = ((x-(⌊x⌋₊:ℝ))*x^(-s-1):ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxp : 0≤x := (show 1<x from hx).le.trans' (by norm_num)
    rw [frac,Complex.ofReal_mul,Complex.ofReal_cpow hxp]
    push_cast
    rfl
  rw [integral_congr_ae he,integral_complex_ofReal,Complex.ofReal_re]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxp : 0≤x := (show 1<x from hx).le.trans' (by norm_num)
  exact mul_nonneg (sub_nonneg.mpr (Nat.floor_le hxp)) (Real.rpow_nonneg hxp _)

theorem regularized_zeta_ne_zero_positive_real {s : ℝ} (hs : 0<s) :
    regularizedZeta (s:ℂ) ≠ 0 := by
  by_cases hs1 : s=1
  · subst s
    simpa only [Complex.ofReal_one,regularizedZeta_one] using (one_ne_zero : (1:ℂ)≠0)
  have hs1c : (s:ℂ)≠1 := by
    intro h
    exact hs1 (by simpa only [Complex.ofReal_re,Complex.one_re] using congrArg Complex.re h)
  rw [(regularizedZeta_germ hs1c).eq_of_nhds]
  apply mul_ne_zero (sub_ne_zero.mpr hs1c)
  by_cases h : 1≤s
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa only [Complex.ofReal_re] using h)
  · intro hz
    have hab := zeta_abel_formula (show 0<(s:ℂ).re by simpa only [Complex.ofReal_re] using hs) hs1c
    rw [← remainder_integral] at hab
    have hneg : s/(s-1)<0 := div_neg_of_pos_of_neg hs (by linarith)
    have hreal := congrArg Complex.re hab
    have hrealdiv : (s:ℂ)/((s:ℂ)-1) = (s/(s-1):ℝ) := by push_cast; rfl
    rw [hz,hrealdiv,Complex.zero_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hreal
    linarith only [hneg,hreal,mul_nonneg hs.le (real_abel_remainder_nonneg hs)]

theorem prime_error_weighted_integrable {s : ℂ} (hs : 1<s.re) : IntegrableOn (fun x => (realPrimeError x:ℂ)*(x:ℂ)^(-(s+1))) (Set.Ioi 1) := by
  refine (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re < -1) (by norm_num : (0:ℝ)<1)).const_mul
    (Real.log 4+5) |>.mono' ?_ ?_
  · exact (Complex.continuous_ofReal.measurable.comp real_prime_error_measurable).aestronglyMeasurable.mul
      (integrableOn_Ioi_cpow_of_lt
        (show (-(s+1)).re < -1 by simp [Complex.add_re]; linarith) (by norm_num : (0:ℝ)<1)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0<x := lt_trans (by norm_num) hx
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Complex.neg_re,Complex.add_re,Complex.one_re]
    have h := mul_le_mul_of_nonneg_right (real_prime_error_linear hx0.le)
      (Real.rpow_nonneg hx0.le (-(s.re+1)))
    have he : x*x^(-(s.re+1)) = x^(-s.re) := by
      calc
        _ = x^(1:ℝ)*x^(-(s.re+1)) := congrArg (fun y => y*x^(-(s.re+1))) (Real.rpow_one x).symm
        _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
    rwa [mul_assoc,he] at h

theorem prime_error_euler_integral {s : ℂ} (hs : 1<s.re) :
    (∫ x in Set.Ioi (1:ℝ), (realPrimeError x:ℂ)*(x:ℂ)^(-(s+1))) =
      (compensatedLogDerivative s-1)/s := by
  have hcount : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,mangoldtCoeff k) =O[atTop]
      (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
    refine Asymptotics.isBigO_iff.mpr ⟨Real.log 4+4,Eventually.of_forall (fun n => ?_)⟩
    have he : (∑ k ∈ Finset.Icc 1 n,mangoldtCoeff k) = (Chebyshev.psi (n:ℝ):ℂ) := by
      simpa only [ChebyshevCriterion.psi,Nat.floor_natCast] using psi_eq_real_psi (n:ℝ)
    have hn : 0≤Chebyshev.psi (n:ℝ) := by
      rw [Chebyshev.psi_eq_sum_Icc]
      exact Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
    rw [he,Complex.norm_real,Real.norm_of_nonneg hn,Real.rpow_one,
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)
  have euler := LSeries_eq_mul_integral mangoldtCoeff (by norm_num : (0:ℝ)≤1) hs
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs) hcount
  change LSeries mangoldtCoeff s = s * ∫ x in Set.Ioi (1:ℝ),
    ChebyshevCriterion.psi x*(x:ℂ)^(-(s+1)) at euler
  have hneg : (-s).re < -1 := by simp; linarith
  have hpowI := integrableOn_Ioi_cpow_of_lt hneg (by norm_num : (0:ℝ)<1)
  have herrorI := prime_error_weighted_integrable hs
  have hsplit (x : ℝ) (hx : x∈Set.Ioi (1:ℝ)) :
      ChebyshevCriterion.psi x*(x:ℂ)^(-(s+1)) =
        (realPrimeError x:ℂ)*(x:ℂ)^(-(s+1))+(x:ℂ)^(-s) := by
    have hx0 : 0<x := lt_trans (by norm_num) hx
    have he : (x:ℂ)*(x:ℂ)^(-(s+1)) = (x:ℂ)^(-s) := by
      calc
        _ = (x:ℂ)^(1:ℂ)*(x:ℂ)^(-(s+1)) := by rw [Complex.cpow_one]
        _ = _ := by
          rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx0.ne')]
          congr 1
          ring
    rw [psi_eq_real_psi,realPrimeError,Complex.ofReal_sub,sub_mul,he,sub_add_cancel]
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,integral_add herrorI hpowI,
    integral_Ioi_cpow_of_lt hneg (by norm_num),Complex.ofReal_one,Complex.one_cpow] at euler
  unfold mangoldtCoeff at euler
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at euler
  have hs0 : s≠0 := by intro h; norm_num [h] at hs
  have hs1 : s≠1 := by intro h; simp [h] at hs
  have hd : (-1:ℂ)/(-s+1)=1/(s-1) := by rw [show -s+1=-(s-1) by ring,div_neg,neg_div,neg_neg]
  rw [hd,mul_add] at euler
  apply (eq_div_iff hs0).mpr
  rw [compensatedLogDerivative]
  have hfrac : s*(1/(s-1))=1+1/(s-1) := by
    field_simp [sub_ne_zero.mpr hs1]
    ring
  linear_combination -euler-hfrac

end RHConnections.PrimeErrorLaplace
