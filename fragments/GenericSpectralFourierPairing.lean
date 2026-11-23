import Verified
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory
namespace RHConnections.SpectralTail
open RelativeResolvent

theorem relative_vertical_norm_le_of_re_lt_one {z : ℂ} (hz : z.re = 1) (rho : ℂ) (hre : rho.re < 1) (hne : rho ≠ 0) :
    ‖relative z 1 (rho-(1/2:ℂ))‖ ≤
      16 * ‖z-1‖ * (1+2*‖z-1‖) / ‖rho‖^2 := by
  let xi := rho-(1/2:ℂ)
  let A := ‖z-xi‖
  let B := ‖(1:ℂ)-xi‖
  let D := ‖z-1‖
  have hxi : xi.re < 1/2 := by
    dsimp [xi]
    norm_num [Complex.sub_re, Complex.div_re]
    linarith [hre]
  have hA : 1/2 ≤ A := by
    have h := Complex.re_le_norm (z-xi)
    rw [Complex.sub_re, hz] at h
    dsimp [A]
    linarith
  have hB : 1/2 ≤ B := by
    have h := Complex.re_le_norm ((1:ℂ)-xi)
    rw [Complex.sub_re, Complex.one_re] at h
    dsimp [B]
    linarith
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hD : 0 ≤ D := norm_nonneg _
  have hv : B ≤ (1+2*D)*A := by
    calc
      B = ‖(1-z)+(z-xi)‖ := by dsimp [B]; congr 1; ring
      _ ≤ D+A := by simpa [A,D,norm_sub_rev] using norm_add_le ((1:ℂ)-z) (z-xi)
      _ ≤ _ := by nlinarith [mul_nonneg hD (show 0 ≤ 2*A-1 by linarith)]
  have hrB : ‖rho‖ ≤ 4*B := by
    calc
      _ = ‖(3/2:ℂ)-((1:ℂ)-xi)‖ := by congr 1; dsimp [xi]; ring
      _ ≤ 3/2+B := by simpa [B, norm_div] using norm_sub_le (3/2:ℂ) (1-xi)
      _ ≤ _ := by linarith
  have hsquare : ‖rho‖^2 ≤ 16*(1+2*D)*(A*B) := by
    calc
      _ ≤ (4*B)^2 := pow_le_pow_left₀ (norm_nonneg _) hrB 2
      _ = 16*B*B := by ring
      _ ≤ 16*B*((1+2*D)*A) := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = _ := by ring
  have hr : 0 < ‖rho‖ := norm_pos_iff.mpr hne
  change ‖relative z 1 xi‖ ≤ 16*D*(1+2*D)/‖rho‖^2
  rw [reference_subtraction z 1 xi (norm_pos_iff.mp hAp) (norm_pos_iff.mp hBp),
    norm_div, norm_mul, norm_sub_rev (1:ℂ) z]
  change D / (A*B) ≤ _
  apply (div_le_div_iff₀ (mul_pos hAp hBp) (sq_pos_of_pos hr)).mpr
  calc
    _ ≤ D*(16*(1+2*D)*(A*B)) := mul_le_mul_of_nonneg_left hsquare hD
    _ = _ := by ring

end RHConnections.SpectralTail

namespace RHConnections.PoleCompensation
open SpectralTail RelativeResolvent FourierTestInversion

def carrierSpectralRelative {ι : Type*} (rho : ι → ℂ) (m : ι → ℕ) (z z₀ : ℂ) :=
  ∑' i, (m i : ℂ) * relative z z₀ (rho i-(1/2:ℂ))

theorem pair_carrierSpectralRelative {ι : Type*} [Countable ι]
    (rho : ι → ℂ) (m : ι → ℕ) (hre : ∀ r, (rho r).re < 1)
    (hne : ∀ r, rho r ≠ 0) (hsum : Summable (fun r => (m r : ℝ)/‖rho r‖^2))
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hzero : f 0 = 0) :
    (∫ v : ℝ, testFourier f v * carrierSpectralRelative rho m (verticalProbe v) 1) =
      ∑' r : ι, (m r : ℂ) *
        ∫ x in Set.Ioi (0:ℝ), Complex.exp (((rho r)-(1/2:ℂ))*(x:ℂ))*f x := by
  classical
  let b := fun r : ι => (m r : ℝ)/‖(rho r)‖^2
  let C := (2:ℝ)*Real.pi
  let W := fun v : ℝ => (16*C*(1+2*C))*((1+|v|)^3*‖testFourier f v‖)
  let k := fun (r : ι) (v : ℝ) => testFourier f v *
    ((m r : ℂ) * relative (verticalProbe v) 1 ((rho r)-(1/2:ℂ)))
  have hb : Summable b := hsum
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
  have hbound (r : ι) (v : ℝ) : ‖k r v‖ ≤ b r * W v := by
    have hrel := relative_vertical_norm_le_of_re_lt_one (verticalProbe_re v) (rho r) (hre r) (hne r)
    dsimp only [k]
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ ‖testFourier f v‖ * ((m r : ℝ) *
          (16 * ‖verticalProbe v-1‖ * (1+2*‖verticalProbe v-1‖) / ‖(rho r)‖^2)) := by gcongr
      _ ≤ ‖testFourier f v‖ * ((m r : ℝ) *
          (16*C*(1+2*C)*(1+|v|)^3 / ‖(rho r)‖^2)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (hpoly v) (sq_nonneg _)) (Nat.cast_nonneg _)) (norm_nonneg _)
      _ = _ := by dsimp [b,W]; ring
  have hi (r : ι) : Integrable (k r) := by
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
      testFourier f v * carrierSpectralRelative rho m (verticalProbe v) 1 = ∑' r, k r v := by
    simp [carrierSpectralRelative,k,tsum_mul_left]
  simp_rw [hpoint]
  rw [hswap]
  apply tsum_congr
  intro r
  have hxr : ((rho r)-(1/2:ℂ)).re < 1 := by
    norm_num [Complex.sub_re, Complex.div_re]
    linarith [hre r]
  have he (v : ℝ) : k r v = (m r : ℂ) *
      (testFourier f v * relative (verticalProbe v) 1 ((rho r)-(1/2:ℂ))) := by
    dsimp [k]
    ring
  simp_rw [he, integral_const_mul, (pair_relative_resolvent hf hc hzero hxr).2]
  all_goals rfl
end RHConnections.PoleCompensation
