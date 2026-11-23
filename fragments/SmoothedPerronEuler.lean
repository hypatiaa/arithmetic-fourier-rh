import Verified

open MeasureTheory
noncomputable section
namespace RHConnections.PerronRamp
open MertensCriterion ZetaDiskLog

def perronIntegrand (h X : ℝ) (s : ℂ) : ℂ :=
  zetaReciprocal s * (X:ℂ)^s * kernel h s

theorem probe_re (c v : ℝ) : (probe c v).re = c := by
  simp [probe,Complex.add_re,Complex.mul_re]

theorem zetaReciprocal_eq_moebius_series {s : ℂ} (hs : 1 < s.re) :
    zetaReciprocal s = LSeries moebiusCoeff s := by
  have hZ := riemannZeta_ne_zero_of_one_le_re hs.le
  have hs1 : s ≠ 1 := fun h => by simpa [h] using hs
  rw [zetaReciprocal_eq_inv_of_ne_one hs1, ← one_div]
  symm
  apply (eq_div_iff hZ).mpr
  rw [mul_comm, ← LSeries_one_eq_riemannZeta hs]
  exact LSeries_one_mul_Lseries_moebius hs

private theorem perron_term_identity (h c X : ℝ) (hX : 0 < X) (n : ℕ) (hn : n ≠ 0)
    (v : ℝ) :
    LSeries.term moebiusCoeff (probe c v) n * (X:ℂ)^(probe c v) * kernel h (probe c v) =
      (moebiusCoeff n * Complex.exp ((c:ℂ)*(Real.log X-Real.log n:ℝ))) *
        (Complex.exp (((2*Real.pi*v*(Real.log X-Real.log n):ℝ):ℂ)*Complex.I) *
          kernel h (probe c v)) := by
  have hnC : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hXC : (X:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hnC,
    Complex.cpow_def_of_ne_zero hXC]
  simp only [← Complex.natCast_log, ← Complex.ofReal_log hX.le, div_eq_mul_inv,
    ← Complex.exp_neg]
  have he :
      Complex.exp (-(↑(Real.log ↑n) * probe c v)) *
        Complex.exp (↑(Real.log X) * probe c v) =
      Complex.exp ((c:ℂ)*(Real.log X-Real.log n:ℝ)) *
        Complex.exp (((2*Real.pi*v*(Real.log X-Real.log n):ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold probe
    push_cast
    ring
  rw [mul_assoc (moebiusCoeff n), he]
  ring

theorem smoothedMertens_eq_euler_integral {h c X : ℝ}
    (hh : 0 < h) (hc : 1 < c) (hX : 0 < X) :
    smoothedMertens h X =
      ∫ v : ℝ, perronIntegrand h X (probe c v) := by
  let F (n : ℕ) (v : ℝ) :=
    LSeries.term moebiusCoeff (probe c v) n * (X:ℂ)^(probe c v) * kernel h (probe c v)
  let b := fun n : ℕ => ‖LSeries.term moebiusCoeff (c:ℂ) n‖
  let D := fun v : ℝ => X^c * ‖kernel h (probe c v)‖
  have hc' : 0 < c := by linarith
  have hD : Integrable D := (kernel_integrable hh hc').norm.const_mul _
  have hb : Summable b :=
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by simpa using hc)).norm
  have hnorm (n : ℕ) (v : ℝ) : ‖F n v‖ = b n * D v := by
    dsimp [F,b,D]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, probe_re,
      LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp [mul_assoc,probe_re]
  have hprobe (v : ℝ) : probe c v ≠ 0 := fun he => by
    have hp := probe_re c v
    rw [he,Complex.zero_re] at hp
    linarith
  have hFi (n : ℕ) : Integrable (F n) := by
    apply (hD.const_mul (b n)).mono'
    · apply Continuous.aestronglyMeasurable
      by_cases hn : n = 0
      · simp [F,hn]
        exact continuous_const
      · have hP : Continuous (probe c) := by unfold probe; fun_prop
        have hk : ∀ v, (2:ℂ)*(h:ℂ)*probe c v^2 ≠ 0 :=
          fun v => mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hh.ne'))
            (pow_ne_zero _ (hprobe v))
        simp only [F,LSeries.term_of_ne_zero hn, kernel,
          Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'),
          Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn : (n:ℂ) ≠ 0)]
        fun_prop (disch := first | exact hk | exact hk _ | positivity | simp)
    · exact ae_of_all _ (fun v => (hnorm n v).le)
  have hsum : Summable (fun n => ∫ v : ℝ, ‖F n v‖) := by
    simpa only [hnorm, integral_const_mul] using hb.mul_right (∫ v : ℝ, D v)
  have hseries (v : ℝ) : perronIntegrand h X (probe c v) = ∑' n, F n v := by
    unfold perronIntegrand
    rw [zetaReciprocal_eq_moebius_series (by rwa [probe_re]),LSeries,tsum_mul_right,tsum_mul_right]
  symm
  simp_rw [hseries]
  rw [← integral_tsum_of_summable_integral_norm hFi hsum]
  unfold smoothedMertens
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [F,moebiusCoeff]
  let x := Real.log X-Real.log n
  have hEq (v : ℝ) : F n v =
      (moebiusCoeff n * Complex.exp ((c:ℂ)*(x:ℂ))) *
        (Complex.exp (((2*Real.pi*v*x:ℝ):ℂ)*Complex.I) * kernel h (probe c v)) :=
    perron_term_identity h c X hX n hn v
  simp_rw [hEq,integral_const_mul,ramp_fourier_inversion hh hc']
  simp only [dampedRamp, Complex.ofReal_mul, Complex.ofReal_exp]
  simp only [Complex.ofReal_neg,neg_mul]
  have he : Complex.exp ((c:ℂ)*(x:ℂ))*Complex.exp (-((c:ℂ)*(x:ℂ))) = 1 := by
    rw [← Complex.exp_add,add_neg_cancel,Complex.exp_zero]
  calc
    _ = (moebiusCoeff n * (Complex.exp ((c:ℂ)*(x:ℂ))*
        Complex.exp (-((c:ℂ)*(x:ℂ))))) * (ramp h x:ℂ) := by ring
    _ = _ := by simp only [he,mul_one,x]

end RHConnections.PerronRamp
