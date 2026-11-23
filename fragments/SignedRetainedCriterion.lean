import Verified
import ParametricSignedSharp

noncomputable section
open Filter
namespace RHConnections.ParametricSignedSharp
open PrimeErrorPower PrimeErrorLaplace
open ParametricSharpRightEndpoint (paramRightSum_eq_zero_of_strip parametricShellRight
  parametric_dyadic_remainder_order)

def signedMode (a σ T : ℝ) : ℝ :=
  if σ=1 then (lowerMode a T).re else -(upperMode a T).re

theorem signed_mode_bounds_prime_error {a σ : ℝ}
    (ha : 1/2≤a) (ha1 : a<1) (hσ : σ=1 ∨ σ= -1) :
    ∃ C : ℝ, 0≤C ∧ ∀ X : ℝ, Real.exp 2≤X →
      -((X/Real.exp 1)*signedMode a σ (Real.log X-1)+C*X^a*(1+Real.log X)^2) ≤
        σ*realDyadicPrimeError X := by
  obtain ⟨C,hC,hR⟩ := parametric_signed_sharp_dyadic_log ha ha1
  refine ⟨C,hC,?_⟩
  intro X hX
  have hx := (Real.exp_pos 2).trans_le hX
  let T := Real.log X-1
  have hT : 1≤T := by
    have h := Real.log_le_log (Real.exp_pos 2) hX
    rw [Real.log_exp] at h
    dsimp [T]
    linarith
  have hXX : Real.exp (T+1)=X := by dsimp [T]; rw [sub_add_cancel,Real.exp_log hx]
  have hTexp : Real.exp T=X/Real.exp 1 := by simp only [T,Real.exp_sub,Real.exp_log hx]
  have hPow : Real.exp T*Real.exp (-(1-a)*T)≤X^a := by
    rw [←Real.exp_add,Real.rpow_def_of_pos hx]
    apply Real.exp_le_exp.mpr
    dsimp [T]
    nlinarith only [ha]
  have hLog : T+2=1+Real.log X := by dsimp [T]; ring
  have hErr : Real.exp T*(C*Real.exp (-(1-a)*T)*(T+2)^2) ≤ C*X^a*(1+Real.log X)^2 := by
    calc
      _ = C*(Real.exp T*Real.exp (-(1-a)*T))*(T+2)^2 := by ring
      _ ≤ _ := by rw [hLog]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPow hC) (sq_nonneg _)
  have h := hR T hT
  dsimp only at h
  rw [hXX] at h
  have he : Chebyshev.psi (2*X)-Chebyshev.psi X-X=realDyadicPrimeError X := by
    unfold realDyadicPrimeError realPrimeError
    ring
  rw [he] at h
  rcases hσ with rfl|rfl
  · simp only [signedMode,ite_true,one_mul,←hTexp]
    change -(Real.exp T*(lowerMode a T).re+C*X^a*(1+Real.log X)^2)≤realDyadicPrimeError X
    linarith only [h.1,hErr,show Real.exp T*((lowerMode a T).re+C*Real.exp (-(1-a)*T)*(T+2)^2)
      =Real.exp T*(lowerMode a T).re+Real.exp T*(C*Real.exp (-(1-a)*T)*(T+2)^2) by ring]
  · have hn : (-1:ℝ)≠1 := by norm_num
    simp only [signedMode,ite_eq_right hn,neg_one_mul,←hTexp]
    linarith only [h.2,hErr,show Real.exp T*(-(upperMode a T).re+C*Real.exp (-(1-a)*T)*(T+2)^2)
      =Real.exp T*(-(upperMode a T).re)+Real.exp T*(C*Real.exp (-(1-a)*T)*(T+2)^2) by ring]

theorem fixed_strip_iff_signed_retained_mode {a σ : ℝ}
    (ha : 1/2≤a) (ha1 : a<1) (hσ : σ=1 ∨ σ= -1) :
    (∀ s : ℂ, a<s.re → riemannZeta s≠0) ↔
      (∀ ε : ℝ, 0<ε → ∃ K : ℝ, 0≤K ∧ ∀ᶠ T : ℝ in atTop,
        signedMode a σ T≤K*Real.exp ((a+ε-1)*T)) := by
  constructor
  · intro h ε hε
    refine ⟨0,le_rfl,Eventually.of_forall fun T => ?_⟩
    have hl : lowerMode a T=0 := paramRightSum_eq_zero_of_strip h _ _
    have hu : upperMode a T=0 := paramRightSum_eq_zero_of_strip h _ _
    simp only [signedMode,hl,hu,Complex.zero_re,neg_zero,ite_self,zero_mul,le_refl]
  · intro h
    apply (fixed_strip_iff_one_sided_dyadic_prime_error ha ha1 hσ).mpr
    intro ε hε
    obtain ⟨K,hK,hK'⟩ := h ε hε
    obtain ⟨C,hC,hR⟩ := signed_mode_bounds_prime_error ha ha1 hσ
    obtain ⟨Y,hY⟩ := eventually_atTop.mp hK'
    refine ⟨K+4*C,by positivity,?_⟩
    filter_upwards [eventually_ge_atTop (max (Real.exp 2) (Real.exp (Y+1))),
      parametric_dyadic_remainder_order a hε] with X hX hErr
    have hX2 := (le_max_left (Real.exp 2) _).trans hX
    have hx := (Real.exp_pos 2).trans_le hX2
    let T := Real.log X-1
    have hT : Y≤T := by
      have hLog := Real.log_le_log (Real.exp_pos (Y+1)) ((le_max_right (Real.exp 2) _).trans hX)
      rw [Real.log_exp] at hLog
      dsimp [T]
      linarith
    have hPow : (X/Real.exp 1)*Real.exp ((a+ε-1)*T)≤X^(a+ε) := by
      have hTexp : X/Real.exp 1=Real.exp T := by simp only [T,Real.exp_sub,Real.exp_log hx]
      rw [hTexp,←Real.exp_add,Real.rpow_def_of_pos hx]
      apply Real.exp_le_exp.mpr
      dsimp [T]
      nlinarith only [ha,hε]
    have hMode : (X/Real.exp 1)*signedMode a σ T≤K*X^(a+ε) := by
      refine (mul_le_mul_of_nonneg_left (hY T hT) (by positivity)).trans ?_
      calc
        _ = K*((X/Real.exp 1)*Real.exp ((a+ε-1)*T)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hPow hK
    have hRem := mul_le_mul_of_nonneg_left hErr hC
    have h := hR X hX2
    nlinarith only [h,hMode,hRem]

theorem rh_iff_signed_critical_mode {σ : ℝ} (hσ : σ=1 ∨ σ= -1) :
    RiemannHypothesis ↔
      (∀ ε : ℝ, 0<ε → ∃ K : ℝ, 0≤K ∧ ∀ᶠ T : ℝ in atTop,
        signedMode (1/2) σ T≤K*Real.exp ((1/2+ε-1)*T)) :=
  ⟨fun h => (fixed_strip_iff_signed_retained_mode le_rfl (by norm_num) hσ).mp
    (ZetaDiskLog.right_zero_free_of_RH h),
    fun h => PoleCompensation.riemannHypothesis_of_right_zero_free
      ((fixed_strip_iff_signed_retained_mode le_rfl (by norm_num) hσ).mpr h)⟩

end RHConnections.ParametricSignedSharp
