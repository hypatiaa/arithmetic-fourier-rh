import Verified

open MeasureTheory
noncomputable section
namespace RHConnections.SmoothedPrimeLimit
open PoleCompensation SpectralTail RelativeResolvent FourierTestInversion

def compactZeroTerm (f : ℝ → ℂ) (r : NontrivialZetaZero) : ℂ :=
  (analyticOrderNatAt riemannZeta r.val : ℂ) *
    ∫ x in Set.Ioi (0:ℝ), Complex.exp ((r.val-(1/2:ℂ))*(x:ℂ))*f x

theorem compact_zero_terms_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (h0 : f 0 = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : NontrivialZetaZero,
      ‖compactZeroTerm f r‖ ≤ (analyticOrderNatAt riemannZeta r.val : ℝ)/‖r.val‖^2 * K := by
  let m := fun r : NontrivialZetaZero => analyticOrderNatAt riemannZeta r.val
  let b := fun r : NontrivialZetaZero => (m r : ℝ)/‖r.val‖^2
  let C := 2*Real.pi
  let W := fun v : ℝ => 16*C*(1+2*C)*((1+|v|)^3*‖testFourier f v‖)
  have hW : Integrable W := (testFourier_integrable_cubic hf hc).const_mul _
  refine ⟨∫ v : ℝ, W v, integral_nonneg (fun v => by dsimp [W,C]; positivity),?_⟩
  intro r
  let g := fun v => testFourier f v * relative (verticalProbe v) 1 (r.val-(1/2:ℂ))
  have hr : (r.val-(1/2:ℂ)).re < 1 := by
    norm_num [Complex.sub_re,Complex.div_re]
    linarith [r.property.1.2]
  have h := pair_relative_resolvent hf hc h0 hr
  have hmul : compactZeroTerm f r = ∫ v : ℝ, (m r:ℂ)*g v := by
    rw [integral_const_mul]
    exact congrArg ((m r:ℂ)*·) h.2.symm
  have hbound (v : ℝ) : ‖(m r:ℂ)*g v‖ ≤ b r * W v := by
    have hrb := relative_vertical_norm_le (verticalProbe_re v) r
    have hp : ‖verticalProbe v-1‖ = C*|v| := by
      unfold verticalProbe
      rw [show 1 - ((2*Real.pi*v : ℝ):ℂ)*Complex.I - 1 =
        -(((2*Real.pi*v : ℝ):ℂ)*Complex.I) by ring]
      simp [C,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos]
    have hpoly : 16*‖verticalProbe v-1‖*(1+2*‖verticalProbe v-1‖) ≤
        16*C*(1+2*C)*(1+|v|)^3 := by
      rw [hp]
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hv : 1 ≤ 1+|v| := by linarith [abs_nonneg v]
      have hlin : 1+2*(C*|v|) ≤ (1+2*C)*(1+|v|) := by linarith [abs_nonneg v]
      calc
        _ ≤ (16*(C*(1+|v|)))*((1+2*C)*(1+|v|)) := by gcongr <;> linarith
        _ = 16*C*(1+2*C)*(1+|v|)^2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (by nlinarith [mul_nonneg (sq_nonneg (1+|v|)) (abs_nonneg v)]) (by positivity)
    dsimp only [g]
    rw [norm_mul,norm_mul,Complex.norm_natCast]
    calc
      _ ≤ (m r:ℝ) * (‖testFourier f v‖ *
          (16 * ‖verticalProbe v-1‖ * (1+2*‖verticalProbe v-1‖) / ‖r.val‖^2)) := by gcongr
      _ ≤ (m r:ℝ) * (‖testFourier f v‖ *
          (16*C*(1+2*C)*(1+|v|)^3 / ‖r.val‖^2)) := by
        gcongr
      _ = _ := by dsimp [b,W]; ring
  rw [hmul,← integral_const_mul]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono (h.1.const_mul _).norm (hW.const_mul _) hbound)

theorem compact_zero_terms_abs_summable {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (h0 : f 0 = 0) :
    Summable (fun r : NontrivialZetaZero => ‖compactZeroTerm f r‖) := by
  obtain ⟨K,_,hK⟩ := compact_zero_terms_bound hf hc h0
  exact (zeta_inverse_square_with_multiplicity.mul_right K).of_nonneg_of_le
    (fun _ => norm_nonneg _) hK

end RHConnections.SmoothedPrimeLimit
