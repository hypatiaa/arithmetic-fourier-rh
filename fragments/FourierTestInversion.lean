import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
namespace RHConnections.FourierTestInversion

def verticalProbe (v : ℝ) : ℂ := 1 - ((2*Real.pi*v : ℝ) : ℂ)*Complex.I

def twistedTest (f : ℝ → ℂ) (x : ℝ) : ℂ := Real.exp x • f x

def testFourier (f : ℝ → ℂ) : ℝ → ℂ := 𝓕 (twistedTest f)

def phase (v x : ℝ) := Complex.exp (((2*Real.pi*v*x : ℝ) : ℂ)*Complex.I)

theorem phase_norm (v x : ℝ) : ‖phase v x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem verticalProbe_exp (v x : ℝ) :
    Complex.exp (-verticalProbe v * (x : ℂ)) =
      Complex.exp (-(x : ℂ)) * phase v x := by
  rw [phase, ← Complex.exp_add]
  congr 1
  simp only [verticalProbe, Complex.ofReal_mul]
  ring

private def testSchwartz (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    SchwartzMap ℝ ℂ :=
  (show HasCompactSupport (twistedTest f) from hc.smul_left (f := Real.exp)).toSchwartzMap
    (show ContDiff ℝ ∞ (twistedTest f) from Real.contDiff_exp.smul hf)

theorem testFourier_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (testFourier f) :=
  (𝓕 (testSchwartz f hf hc)).integrable

theorem testFourier_integrable_cubic {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun v : ℝ => (1 + |v|)^3 * ‖testFourier f v‖) := by
  let S := 𝓕 (testSchwartz f hf hc)
  have h := (((S.integrable_pow_mul volume 0).add
    ((S.integrable_pow_mul volume 1).const_mul 3)).add
    ((S.integrable_pow_mul volume 2).const_mul 3)).add (S.integrable_pow_mul volume 3)
  refine h.congr (ae_of_all _ fun v => ?_)
  change ‖v‖^0 * ‖S v‖ + 3*(‖v‖^1 * ‖S v‖) + 3*(‖v‖^2 * ‖S v‖) +
    ‖v‖^3 * ‖S v‖ = (1+|v|)^3 * ‖S v‖
  rw [Real.norm_eq_abs]
  ring

theorem testFourier_phase_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (x : ℝ) :
    Integrable (fun v => testFourier f v * phase v x) := by
  have hF : Continuous (testFourier f) := (𝓕 (testSchwartz f hf hc)).continuous
  apply (testFourier_integrable hf hc).norm.mono'
  · apply Continuous.aestronglyMeasurable
    apply hF.mul
    unfold phase
    fun_prop
  · exact ae_of_all _ fun v => by simp [norm_mul, phase_norm]

theorem testFourier_inversion {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (x : ℝ) :
    (∫ v : ℝ, testFourier f v * phase v x) = twistedTest f x := by
  have hcψ : Continuous (twistedTest f) := (testSchwartz f hf hc).continuous
  have hiψ : Integrable (twistedTest f) := (testSchwartz f hf hc).integrable
  have h := congrFun (hcψ.fourierInv_fourier_eq hiψ (testFourier_integrable hf hc)) x
  change (𝓕⁻ (testFourier f)) x = twistedTest f x at h
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at h
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun v => ?_)) h
  change testFourier f v * phase v x =
    Complex.exp (((-2*Real.pi*v*(-x) : ℝ) : ℂ)*Complex.I) * testFourier f v
  rw [show -2*Real.pi*v*(-x) = 2*Real.pi*v*x by ring, mul_comm] <;> rfl

theorem testFourier_compensated_inversion {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hzero : f 0 = 0) (x : ℝ) :
    (∫ v : ℝ, testFourier f v * (phase v x - 1)) = twistedTest f x := by
  have h₀ := testFourier_inversion hf hc 0
  simp [phase, twistedTest, hzero] at h₀
  simp_rw [mul_sub, mul_one]
  rw [integral_sub (testFourier_phase_integrable hf hc x) (testFourier_integrable hf hc),
    h₀, sub_zero, testFourier_inversion hf hc]

end RHConnections.FourierTestInversion
