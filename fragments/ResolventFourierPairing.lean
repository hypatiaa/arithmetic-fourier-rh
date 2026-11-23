import Verified
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory
namespace RHConnections.FourierTestInversion
open RelativeResolvent

theorem verticalProbe_re (v : ℝ) : (verticalProbe v).re = 1 := by
  simp [verticalProbe, Complex.sub_re, Complex.mul_re]

theorem relative_eq_phase_integral (v : ℝ) {xi : ℂ} (hxi : xi.re < 1) :
    relative (verticalProbe v) 1 xi =
      ∫ x in Set.Ioi (0:ℝ), Complex.exp ((xi-1)*(x:ℂ)) * (phase v x-1) := by
  rw [← laplace_difference _ _ _ (by rwa [verticalProbe_re]) (by simpa using hxi)]
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_sub, mul_one, phase, ← Complex.exp_add]
  congr 2
  simp only [verticalProbe, Complex.ofReal_mul]
  ring

theorem pair_relative_resolvent {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hzero : f 0 = 0) {xi : ℂ} (hxi : xi.re < 1) :
    Integrable (fun v => testFourier f v * relative (verticalProbe v) 1 xi) ∧
    (∫ v : ℝ, testFourier f v * relative (verticalProbe v) 1 xi) =
      ∫ x in Set.Ioi (0:ℝ), Complex.exp (xi*(x:ℂ))*f x := by
  let μ := (volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))
  let E := fun x : ℝ => Complex.exp ((xi-1)*(x:ℂ))
  let A := testFourier f
  let K := fun (v x : ℝ) => A v * (E x * (phase v x-1))
  have hA := testFourier_integrable hf hc
  have hE : Integrable E μ := integrableOn_exp_mul_complex_Ioi
    (by simpa [Complex.sub_re] using sub_neg.mpr hxi) 0
  have hK : Integrable (Function.uncurry K) (volume.prod μ) := by
    apply ((hA.norm.const_mul 2).mul_prod hE.norm).mono'
    · have hAsm : AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1) (volume.prod μ) :=
        hA.aestronglyMeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_fst)
      exact hAsm.mul (show AEStronglyMeasurable (fun p : ℝ × ℝ =>
        E p.2 * (phase p.1 p.2-1)) (volume.prod μ) by
        apply Continuous.aestronglyMeasurable
        dsimp [E,phase]
        fun_prop)
    · exact ae_of_all _ fun p => by
        change ‖A p.1 * (E p.2 * (phase p.1 p.2-1))‖ ≤
          2 * ‖A p.1‖ * ‖E p.2‖
        have hb : ‖phase p.1 p.2 - 1‖ ≤ 2 := by
          have h := norm_sub_le (phase p.1 p.2) (1:ℂ)
          norm_num [phase_norm] at h ⊢
          exact h
        rw [norm_mul, norm_mul]
        calc
          _ ≤ ‖A p.1‖ * (‖E p.2‖ * 2) := by gcongr
          _ = _ := by ring
  have hEq (v : ℝ) : testFourier f v * relative (verticalProbe v) 1 xi = ∫ x, K v x ∂μ := by
    rw [relative_eq_phase_integral v hxi]
    exact (integral_const_mul _ _).symm
  refine ⟨hK.integral_prod_left.congr (ae_of_all _ (fun v => (hEq v).symm)), ?_⟩
  calc
    _ = ∫ v : ℝ, ∫ x, K v x ∂μ :=
      integral_congr_ae (ae_of_all _ hEq)
    _ = ∫ x, ∫ v : ℝ, K v x ∂volume ∂μ := integral_integral_swap hK
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      change (∫ v : ℝ, A v * (E x * (phase v x-1))) = _
      simp_rw [show ∀ v : ℝ, A v * (E x * (phase v x-1)) =
        E x * (A v * (phase v x-1)) from fun v => by ring]
      rw [integral_const_mul, testFourier_compensated_inversion hf hc hzero]
      simp only [E, twistedTest, Complex.real_smul, Complex.ofReal_exp, ← mul_assoc,
        ← Complex.exp_add]
      congr 2
      ring

end RHConnections.FourierTestInversion
