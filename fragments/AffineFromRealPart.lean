import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic

noncomputable section
open Filter Metric Set Complex Real
open scoped Topology
namespace RHConnections.AffineFromRealPart

def meanAbsRe (G : ℂ → ℂ) (R : ℝ) : ℝ :=
  circleAverage (fun z => |(G z).re|) 0 R

private theorem halfDisc {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : ‖w‖ ≤ R/2) :
    (G w).re ≤ 3 * meanAbsRe G R := by
  have hin : w ∈ ball (0 : ℂ) R := by simpa using (show ‖w‖ < R by linarith)
  let K := fun z => (herglotzRieszKernel 0 w z).re
  have hout : w ∉ sphere (0 : ℂ) |R| := by
    simp [abs_of_pos hR, mem_sphere, ne_of_lt (show ‖w‖ < R by linarith)]
  have hc : ContinuousOn K (sphere 0 |R|) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hout)
  have hpi : K • G = (fun z => K z • G z) := funext (fun _ => rfl)
  have hci : CircleIntegrable (fun z => K z • G z) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    rw [← hpi]
    simpa only [abs_of_pos hR] using hc.smul (hG.continuous.continuousOn)
  have heq : circleAverage (fun z => K z * (G z).re) 0 R = (G w).re := by
    have h := congrArg Complex.re (hG.diffContOnCl.circleAverage_re_herglotzRieszKernel_smul hin)
    change (circleAverage (K • G) 0 R).re = (G w).re at h
    rw [hpi] at h
    rw [← h]
    simpa [Function.comp_def, K, Complex.smul_re, Pi.smul_def] using Complex.reCLM.circleAverage_comp_comm hci
  rw [← heq]
  change _ ≤ (3 : ℝ) • circleAverage (fun z => |(G z).re|) 0 R
  rw [← circleAverage_fun_smul]
  apply circleAverage_mono
  · apply ContinuousOn.circleIntegrable hR.le
    simpa [abs_of_pos hR, Pi.mul_def, Function.comp_def] using hc.mul ((Complex.continuous_re.comp hG.continuous).continuousOn)
  · apply ContinuousOn.circleIntegrable hR.le
    exact (show Continuous (fun z : ℂ => (3:ℝ) * |(G z).re|) from
      continuous_const.mul (Complex.continuous_re.comp hG.continuous).abs).continuousOn
  · intro z hz
    rw [abs_of_pos hR] at hz
    have hhi := re_herglotzRieszKernel_le hz hin
    have hlo := le_re_herglotzRieszKernel hz hin
    simp only [sub_zero] at hhi hlo
    have hk₀ : 0 ≤ K z := by
      simpa [K, herglotzRieszKernel_def] using
        (div_nonneg (show 0 ≤ R - ‖w‖ by linarith) (show 0 ≤ R + ‖w‖ by positivity)).trans hlo
    have hk : K z ≤ 3 := by
      simpa [K, herglotzRieszKernel_def] using hhi.trans
        ((div_le_iff₀ (show 0 < R-‖w‖ by linarith)).mpr (show R+‖w‖ ≤ 3*(R-‖w‖) by linarith))
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) hk₀).trans (mul_le_mul_of_nonneg_right hk (abs_nonneg _))

private theorem quarterDisc {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : ‖w‖ ≤ R/4) :
    ‖G w‖ ≤ 6 * meanAbsRe G R + (2 + 3 * ‖G 0‖) := by
  have hA : 0 ≤ meanAbsRe G R := by
    apply Real.circleAverage_nonneg_of_nonneg
    intros; positivity
  let M := 1 + 3 * meanAbsRe G R
  have hM : 0 < M := by dsimp [M]; linarith
  have hm : MapsTo G (ball 0 (R/2)) {z : ℂ | z.re ≤ M} := by
    intro z hz
    have hhalf : ‖z‖ ≤ R/2 := (by simpa using hz : ‖z‖ < R/2).le
    exact (halfDisc hG hR hhalf).trans (by dsimp [M]; linarith)
  have hin : w ∈ ball (0 : ℂ) (R/2) := by simpa using (show ‖w‖ < R/2 by linarith)
  have h := Complex.borelCaratheodory hM hG.differentiableOn hm (by positivity) hin
  have hd : 0 < R/2 - ‖w‖ := by linarith
  have h₁ : 2*M*‖w‖ / (R/2-‖w‖) ≤ 2*M := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg hM.le (show 0 ≤ R/4-‖w‖ by linarith)]
  have h₂ : ‖G 0‖*(R/2+‖w‖) / (R/2-‖w‖) ≤ 3*‖G 0‖ := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (norm_nonneg (G 0)) (show 0 ≤ R/4-‖w‖ by linarith)]
  exact h.trans ((add_le_add h₁ h₂).trans_eq (by dsimp [M]; ring))

theorem affine_of_subquadratic_meanAbsRe {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hgrowth : Tendsto (fun R : ℝ => meanAbsRe G R / R^2) atTop (𝓝 0)) :
    ∀ z, G z = G 0 + deriv G 0 * z := by
  have hsecond (c : ℂ) : deriv (deriv G) c = 0 := by
    let D := 2 + 3 * ‖G 0‖
    have hzero : Tendsto (fun R : ℝ =>
        768 * (meanAbsRe G R / R ^ 2) + (128 * D) * R⁻¹ ^ 2) atTop (𝓝 0) := by
      simpa using (hgrowth.const_mul 768).add
        ((tendsto_inv_atTop_zero.pow 2).const_mul (128*D))
    have hle : ∀ᶠ R : ℝ in atTop, ‖iteratedDeriv 2 G c‖ ≤
        768 * (meanAbsRe G R / R^2) + (128*D)*R⁻¹^2 := by
      filter_upwards [eventually_gt_atTop (8*‖c‖+1)] with R hR
      have hp : 0 < R := by nlinarith [norm_nonneg c]
      have hball (z : ℂ) (hz : z ∈ sphere c (R/8)) : ‖z‖ ≤ R/4 := by
        have hh : ‖z-c‖ = R/8 := by simpa [mem_sphere, dist_eq_norm] using hz
        have ht := norm_add_le (z-c) c
        rw [sub_add_cancel, hh] at ht
        linarith
      have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2
        (show 0 < R/8 by positivity) hG.diffContOnCl
        (fun z hz => quarterDisc hG hp (hball z hz))
      refine h.trans_eq ?_
      norm_num [D, Nat.factorial]
      field_simp [hp.ne']
      <;> ring

    have hn : ‖iteratedDeriv 2 G c‖ ≤ 0 := le_of_tendsto_of_tendsto
      tendsto_const_nhds hzero hle
    have hv := norm_le_zero_iff.mp hn
    simpa [iteratedDeriv_succ] using hv
  have hd : Differentiable ℂ (deriv G) := hG.deriv
  have hc (z : ℂ) := is_const_of_deriv_eq_zero hd hsecond z 0
  let H := fun z : ℂ => G z - deriv G 0 * z
  have hH (z : ℂ) : HasDerivAt H 0 z := by
    simpa [H, hc z, Pi.sub_def, id_eq] using ((hG z).hasDerivAt.sub ((hasDerivAt_id z).const_mul (deriv G 0)))
  intro z
  have h := is_const_of_deriv_eq_zero (fun x => (hH x).differentiableAt)
    (fun x => (hH x).deriv) z 0
  dsimp [H] at h
  linear_combination h

end RHConnections.AffineFromRealPart
