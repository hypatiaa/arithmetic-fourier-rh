import Verified
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
noncomputable section
namespace RHConnections.PerronRamp

def smoothedPole (h X : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0:ℝ), Real.exp u * ramp h (Real.log X-u)

theorem smoothedPole_euler_pairing {h X : ℝ} (hh : 0 < h) (hX : 0 < X) :
    Integrable (fun v : ℝ => (probe 2 v-1)⁻¹ * (X:ℂ)^(probe 2 v) * kernel h (probe 2 v)) ∧
      (smoothedPole h X : ℂ) = ∫ v : ℝ,
        (probe 2 v-1)⁻¹ * (X:ℂ)^(probe 2 v) * kernel h (probe 2 v) := by
  let μp := (volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))
  let s := probe 2
  let A := fun v => (X:ℂ)^(s v) * kernel h (s v)
  let J := fun (v u : ℝ) => Complex.exp ((1-s v)*(u:ℂ))*A v
  have hre (v : ℝ) : (s v).re = 2 := probe_re 2 v
  have hK : Integrable (fun v => kernel h (s v)) := kernel_integrable hh (by norm_num)
  have hE : Integrable (fun u : ℝ => Real.exp (-u)) μp := by
    change IntegrableOn _ (Set.Ioi (0:ℝ))
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ) < 0) (0:ℝ)
  have hpow (v : ℝ) : ‖(X:ℂ)^(s v)‖ = X^2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hre]
    norm_num
  have hnorm (u v : ℝ) : ‖J v u‖ = (X^2 * ‖kernel h (s v)‖)*Real.exp (-u) := by
    simp only [J,A,norm_mul,hpow,Complex.norm_exp,Complex.mul_re,Complex.sub_re,Complex.one_re,
      hre,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    norm_num <;> ring
  have hJ : Integrable (Function.uncurry J) (volume.prod μp) := by
    apply ((hK.norm.const_mul (X^2)).mul_prod hE).mono'
    · apply Measurable.aestronglyMeasurable
      unfold Function.uncurry J A s kernel probe
      fun_prop
    · exact ae_of_all _ fun p => (hnorm p.2 p.1).le
  have hv (v : ℝ) : (∫ u, J v u ∂μp) = (s v-1)⁻¹ * (X:ℂ)^(s v)*kernel h (s v) := by
    have hn : (1-s v).re < 0 := by simp [Complex.sub_re,hre]
    change (∫ u in Set.Ioi (0:ℝ), Complex.exp ((1-s v)*(u:ℂ))*A v) = _
    rw [integral_mul_const, integral_exp_mul_complex_Ioi hn 0]
    simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,show 1-s v = -(s v-1) by ring,
      neg_div_neg_eq,one_div,A]
    ring
  have hu (u : ℝ) : (∫ v : ℝ, J v u) = ((Real.exp u*ramp h (Real.log X-u):ℝ):ℂ) := by
    let x := Real.log X-u
    let B : ℂ := Complex.exp ((u:ℂ)+2*(x:ℂ))
    have he (v : ℝ) : J v u = B * (Complex.exp (((2*Real.pi*v*x:ℝ):ℂ)*Complex.I)*kernel h (s v)) := by
      dsimp only [J,A,B]
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'), ← Complex.ofReal_log hX.le]
      rw [← mul_assoc, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]
      congr 2
      dsimp [s,probe,x]
      push_cast
      ring
    simp_rw [he, integral_const_mul]
    rw [show (∫ v : ℝ, Complex.exp (((2*Real.pi*v*x:ℝ):ℂ)*Complex.I)*kernel h (s v)) =
        dampedRamp h 2 x from ramp_fourier_inversion hh (by norm_num) x]
    simp only [B,dampedRamp,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_ofNat]
    rw [← mul_assoc, ← Complex.exp_add, show (u:ℂ)+2*(x:ℂ)+(-2)*(x:ℂ)=(u:ℂ) by ring]
  refine ⟨hJ.integral_prod_left.congr (ae_of_all _ hv), ?_⟩
  calc
    _ = ∫ u, (∫ v : ℝ, J v u) ∂μp := by
      simp_rw [hu]
      exact integral_complex_ofReal.symm
    _ = ∫ v : ℝ, ∫ u, J v u ∂μp := (integral_integral_swap hJ).symm
    _ = _ := integral_congr_ae (ae_of_all _ hv)

end RHConnections.PerronRamp
