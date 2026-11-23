import Verified

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace RHConnections.PositiveLaplace

variable {α : Type*} [MeasurableSpace α] {measure : Measure α}

def complexLaplace (f Y : α → ℝ) (measure : Measure α) (s : ℂ) : ℂ :=
  ∫ x, (f x:ℂ)*Complex.exp (-s*(Y x:ℂ)) ∂measure

theorem complex_laplace_analytic {f Y : α → ℝ} (hf : Measurable f) (hY : Measurable Y)
    (hf0 : ∀ x, 0≤f x) (hY0 : ∀ x, 0≤Y x)
    (hI : ∀ b : ℝ, 0<b → Integrable (fun x => f x*Real.exp (-b*Y x)) measure) :
    AnalyticOnNhd ℂ (complexLaplace f Y measure) {s : ℂ | 0<s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  change 0<s.re at hs
  let r := s.re/4
  let b := s.re/2
  have hr : 0<r := by dsimp [r]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  let F := fun (z : ℂ) (x : α) => (f x:ℂ)*Complex.exp (-z*(Y x:ℂ))
  let D := fun (z : ℂ) (x : α) => F z x * (-(Y x:ℂ))
  have hF (z : ℂ) : Measurable (F z) := by unfold F; fun_prop
  have hD (z : ℂ) : Measurable (D z) := by unfold D; fun_prop
  have hnorm (z : ℂ) (x : α) : ‖F z x‖ = f x*Real.exp (-z.re*Y x) := by
    simp only [F,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hf0 x),
      Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have hFs : Integrable (F s) measure :=
    (hI s.re hs).mono' (hF s).aestronglyMeasurable (ae_of_all _ fun x => le_of_eq (hnorm s x))
  let bound := fun x => f x*Real.exp (-b*Y x)/r
  have hbound : Integrable bound measure := (hI b hb).div_const r
  have hDb : ∀ᵐ x ∂measure, ∀ z ∈ Metric.ball s r, ‖D z x‖ ≤ bound x := by
    refine ae_of_all _ fun x z hz => ?_
    have hd : |(z-s).re| ≤ ‖z-s‖ := Complex.abs_re_le_norm (z-s)
    have hh := (mem_ball_iff_norm.mp hz)
    have hzr : b+r ≤ z.re := by
      rw [Complex.sub_re] at hd
      have hh' := neg_abs_le (z.re-s.re)
      dsimp [b,r] at *
      linarith only [hd,hh,hh',hs]
    have hlog : r*Y x ≤ Real.exp (r*Y x) := by linarith only [Real.add_one_le_exp (r*Y x)]
    have hYexp : Y x * Real.exp (-(r*Y x)) ≤ 1/r := by
      apply (le_div_iff₀ hr).mpr
      calc
        _ = (r*Y x)*Real.exp (-(r*Y x)) := by ring
        _ ≤ Real.exp (r*Y x)*Real.exp (-(r*Y x)) :=
          mul_le_mul_of_nonneg_right hlog (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
    have he : Real.exp (-z.re*Y x) ≤ Real.exp (-b*Y x)*Real.exp (-(r*Y x)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hzr (hY0 x)
      linarith only [h,show (b+r)*Y x=b*Y x+r*Y x by ring]
    change ‖F z x * (-(Y x:ℂ))‖ ≤ _
    rw [norm_mul,hnorm,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hY0 x)]
    calc
      _ ≤ (f x*(Real.exp (-b*Y x)*Real.exp (-(r*Y x))))*Y x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (hf0 x)) (hY0 x)
      _ = (f x*Real.exp (-b*Y x))*(Y x*Real.exp (-(r*Y x))) := by ring
      _ ≤ (f x*Real.exp (-b*Y x))*(1/r) :=
        mul_le_mul_of_nonneg_left hYexp (mul_nonneg (hf0 x) (Real.exp_pos _).le)
      _ = _ := by unfold bound; ring
  have hDeriv : ∀ᵐ x ∂measure, ∀ z ∈ Metric.ball s r,
      HasDerivAt (fun w => F w x) (D z x) z := by
    refine ae_of_all _ fun x z _ => ?_
    have hd := ((((hasDerivAt_id z).neg).mul_const (Y x:ℂ)).cexp).const_mul (f x:ℂ)
    convert hd using 1
    · ext w; simp [F,Pi.neg_apply]
    · dsimp [D,F]; ring
  have hDInt := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s hr)
    (Eventually.of_forall fun z => (hF z).aestronglyMeasurable) hFs (hD s).aestronglyMeasurable hDb hbound hDeriv
  exact hDInt.2.differentiableAt.differentiableWithinAt

end RHConnections.PositiveLaplace
