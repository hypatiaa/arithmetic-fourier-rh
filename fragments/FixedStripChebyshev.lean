import Verified
import FixedStripLogDerivative
import ChebyshevFixedPowerConverse

noncomputable section
open Filter Asymptotics
namespace RHConnections.ChebyshevCriterion
open PerronRamp PerronGrowthTransfer ZetaDiskLog PoleCompensation

theorem chebyshev_power_bound_of_strip {a ε : ℝ}
    (hStrip : ∀ s : ℂ, a<s.re → riemannZeta s≠0)
    (ha : 1/2≤a) (ha1 : a<1) (hε : 0<ε) :
    psiError =O[atTop] (fun X : ℝ => X^(a+ε)) := by
  let d := min (ε/2) ((1-a)/2)
  let b := a+d
  have hd : 0<d := lt_min (by positivity) (by linarith)
  have hdε : d≤ε/2 := min_le_left _ _
  have hd1 : d≤(1-a)/2 := min_le_right _ _
  have hb : a<b := by dsimp [b]; linarith
  have hb1 : b<1 := by dsimp [b]; linarith
  have hExp : 0<a+ε := by linarith
  obtain ⟨D,hD,hGrow⟩ := regularizedLogDerivative_subpower_of_strip hStrip ha hb hb1 hd
  have hA : AnalyticOnNhd ℂ regularizedLogDerivative {s : ℂ | s.re∈Set.Icc b 2} :=
    fun s hs => regularizedLogDerivative_on_halfplane hStrip s (hb.trans_le hs.1)
  obtain ⟨C,hC,hB⟩ := euler_integral_bound_of_strip_growth (by linarith : 0<b)
    (by linarith : b≤2) hd (by linarith : d<1) hD hA (fun s hs => hGrow s hs.1 hs.2)
  apply IsBigO.of_bound (C+6*(1+(a+ε)⁻¹)+4)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
  have hX0 := zero_lt_one.trans_le hX
  let h := X⁻¹
  have hh : 0<h := inv_pos.mpr hX0
  have hh1 : h≤1 := inv_le_one_of_one_le₀ hX
  have hxhp : X*h=1 := mul_inv_cancel₀ hX0.ne'
  have hC' := hB X h hX hh hh1
  rw [←smoothed_chebyshev_compensated_euler hX0 hh] at hC'
  have hdexp : h^(-d)=X^d := by
    dsimp [h]
    rw [Real.inv_rpow hX0.le,Real.rpow_neg hX0.le,inv_inv]
  rw [hdexp,mul_assoc,←Real.rpow_add hX0] at hC'
  have hS := hC'.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX (show b+d≤a+ε by dsimp [b]; linarith)) hC)
  have hLog := Real.log_le_rpow_div hX0.le hExp
  have hPow : 1≤X^(a+ε) := Real.one_le_rpow hX hExp.le
  have hApprox := smoothedChebyshev_error hX hh hh1
  rw [hxhp] at hApprox
  have hApprox' : ‖smoothedChebyshev h X-psi X‖ ≤ 6*(1+(a+ε)⁻¹)*X^(a+ε) := by
    change ‖smoothedChebyshev h X-sharpChebyshev X‖ ≤ _
    refine hApprox.trans ?_
    rw [div_eq_mul_inv] at hLog
    nlinarith only [hPow,hLog]
  have hPole : ‖((smoothedPole h X:ℝ):ℂ)-((X:ℂ)-1)‖≤3 := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have hP := smoothedPole_error hX hh hh1
    rw [mul_assoc,hxhp,mul_one] at hP
    exact hP
  let P := ((smoothedPole h X:ℝ):ℂ)
  have he : psiError X=(psi X-smoothedChebyshev h X)+(smoothedChebyshev h X-P)
      +(P-((X:ℂ)-1))-1 := by unfold psiError; ring
  have hBound : ‖psiError X‖ ≤ (C+6*(1+(a+ε)⁻¹)+4)*X^(a+ε) := by
    rw [he]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)) le_rfl).trans ?_
    rw [norm_sub_rev (psi X),norm_one]
    nlinarith only [hS,hApprox',hPole,hPow]
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)] using hBound

end RHConnections.ChebyshevCriterion

namespace RHConnections.DyadicEndpoint
open RHConnections.ChebyshevCriterion

theorem fixed_strip_iff_dyadic_chebyshev_power {a : ℝ} (ha : 1/2≤a) (ha1 : a<1) :
    (∀ s : ℂ, a<s.re → riemannZeta s≠0) ↔
      (∀ ε : ℝ, 0<ε → dyadicChebyshevError =O[atTop] (fun X : ℝ => X^(a+ε))) := by
  constructor
  · intro h ε hε
    exact (dyadic_chebyshev_power_iff (by linarith : 0<a+ε)).mpr
      (chebyshev_power_bound_of_strip h ha ha1 hε)
  · intro h s hs
    let ε := min ((s.re-a)/2) ((1-a)/2)
    have hε : 0<ε := lt_min (by linarith) (by linarith)
    have hb1 : a+ε<1 := by linarith [min_le_right ((s.re-a)/2) ((1-a)/2)]
    have hbs : a+ε<s.re := by linarith [min_le_left ((s.re-a)/2) ((1-a)/2)]
    exact zero_free_of_chebyshev_fixed_power hb1
      ((dyadic_chebyshev_power_iff (by linarith : 0<a+ε)).mp (h ε hε)) s hbs

end RHConnections.DyadicEndpoint
