import Verified
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory
namespace RHConnections.PoleCompensation
open SpectralTail RelativeResolvent FourierTestInversion

theorem pair_zetaSpectralRelative {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hzero : f 0 = 0) :
    (∫ v : ℝ, testFourier f v * zetaSpectralRelative (verticalProbe v) 1) =
      ∑' r : NontrivialZetaZero, (analyticOrderNatAt riemannZeta r.val : ℂ) *
        ∫ x in Set.Ioi (0:ℝ), Complex.exp ((r.val-(1/2:ℂ))*(x:ℂ))*f x := by
  classical
  let m := fun r : NontrivialZetaZero => analyticOrderNatAt riemannZeta r.val
  let b := fun r : NontrivialZetaZero => (m r : ℝ)/‖r.val‖^2
  let C := (2:ℝ)*Real.pi
  let W := fun v : ℝ => (16*C*(1+2*C))*((1+|v|)^3*‖testFourier f v‖)
  let k := fun (r : NontrivialZetaZero) (v : ℝ) => testFourier f v *
    ((m r : ℂ) * relative (verticalProbe v) 1 (r.val-(1/2:ℂ)))
  obtain ⟨δ,hδ,hd⟩ := zeta_zero_norm_lower
  have hb : Summable b := zeta_inverse_square_with_multiplicity
  have hbpos (r : NontrivialZetaZero) : 0 < b r := by
    have hnr : 0 < ‖r.val‖ := hδ.trans_le (hd r)
    obtain ⟨ha,hfin⟩ := zeta_nontrivial_zero_finite_order r
    have hn : m r ≠ 0 := by
      intro h0
      have horder := Nat.cast_analyticOrderNatAt hfin
      change (m r : ℕ∞) = _ at horder
      rw [h0, Nat.cast_zero] at horder
      rcases analyticOrderAt_eq_zero.mp horder.symm with hs | hs
      · exact hs ha
      · exact hs r.property.2
    exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (sq_pos_of_pos hnr)
  have hsup : Function.support b = Set.univ := by
    ext r
    simp [Function.mem_support, (hbpos r).ne']
  haveI : Countable NontrivialZetaZero := Set.countable_univ_iff.mp (hsup ▸ hb.countable_support)
  have hW : Integrable W := (testFourier_integrable_cubic hf hc).const_mul _
  have hprobe (v : ℝ) : ‖verticalProbe v - 1‖ = C*|v| := by
    unfold verticalProbe
    rw [show 1 - ((2*Real.pi*v : ℝ):ℂ)*Complex.I - 1 =
      -(((2*Real.pi*v : ℝ):ℂ)*Complex.I) by ring]
    simp [C, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
  have hpoly (v : ℝ) :
      16 * ‖verticalProbe v - 1‖ * (1 + 2*‖verticalProbe v - 1‖) ≤
        16*C*(1+2*C)*(1+|v|)^3 := by
    rw [hprobe]
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have h1 : 1 ≤ 1+|v| := by linarith [abs_nonneg v]
    have h2 : 1+2*(C*|v|) ≤ (1+2*C)*(1+|v|) := by linarith [abs_nonneg v]
    calc
      _ ≤ (16*(C*(1+|v|)))*((1+2*C)*(1+|v|)) := by
        gcongr <;> linarith [abs_nonneg v]
      _ = 16*C*(1+2*C)*(1+|v|)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by nlinarith [mul_nonneg (sq_nonneg (1+|v|)) (abs_nonneg v)]) (by positivity)
  have hbound (r : NontrivialZetaZero) (v : ℝ) : ‖k r v‖ ≤ b r * W v := by
    have hrel := relative_vertical_norm_le (verticalProbe_re v) r
    dsimp only [k]
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ ‖testFourier f v‖ * ((m r : ℝ) *
          (16 * ‖verticalProbe v-1‖ * (1+2*‖verticalProbe v-1‖) / ‖r.val‖^2)) := by gcongr
      _ ≤ ‖testFourier f v‖ * ((m r : ℝ) *
          (16*C*(1+2*C)*(1+|v|)^3 / ‖r.val‖^2)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (hpoly v) (sq_nonneg _)) (Nat.cast_nonneg _)) (norm_nonneg _)
      _ = _ := by dsimp [b,W]; ring
  have hi (r : NontrivialZetaZero) : Integrable (k r) := by
    apply (hW.const_mul (b r)).mono'
    · refine (testFourier_integrable hf hc).aestronglyMeasurable.mul ?_
      apply Measurable.aestronglyMeasurable
      dsimp [relative,verticalProbe]
      fun_prop
    · exact ae_of_all _ (hbound r)
  have hs : Summable (fun r => ∫ v : ℝ, ‖k r v‖) := by
    apply (hb.mul_right (∫ v : ℝ, W v)).of_nonneg_of_le
      (fun r => integral_nonneg fun v => norm_nonneg _)
    intro r
    rw [← integral_const_mul]
    exact integral_mono (hi r).norm (hW.const_mul (b r)) (hbound r)
  have hswap := (integral_tsum_of_summable_integral_norm hi hs).symm
  have hpoint (v : ℝ) :
      testFourier f v * zetaSpectralRelative (verticalProbe v) 1 = ∑' r, k r v := by
    simp [zetaSpectralRelative,k,m,tsum_mul_left]
  simp_rw [hpoint]
  rw [hswap]
  apply tsum_congr
  intro r
  have hxr : (r.val-(1/2:ℂ)).re < 1 := by
    norm_num [Complex.sub_re, Complex.div_re]
    linarith [r.property.1.2]
  have he (v : ℝ) : k r v = (m r : ℂ) *
      (testFourier f v * relative (verticalProbe v) 1 (r.val-(1/2:ℂ))) := by
    dsimp [k]
    ring
  simp_rw [he, integral_const_mul, (pair_relative_resolvent hf hc hzero hxr).2]
  rfl
end RHConnections.PoleCompensation
