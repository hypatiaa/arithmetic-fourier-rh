import Verified

open Filter
namespace RHConnections.SpectralTail

theorem zeta_zero_norm_lower : ∃ δ : ℝ, 0 < δ ∧
    ∀ r : NontrivialZetaZero, δ ≤ ‖r.val‖ := by
  have hcont : ContinuousAt riemannZeta (0:ℂ) :=
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  have hnear : ∀ᶠ s in nhds (0:ℂ), riemannZeta s ≠ 0 :=
    hcont.eventually_ne (by norm_num [riemannZeta_zero])
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro r
  apply le_of_not_gt
  intro hr
  exact hh (show dist r.val (0:ℂ) < δ by simpa only [dist_zero_right] using hr) r.property.2

theorem zeta_inverse_square_with_multiplicity :
    Summable (fun r : NontrivialZetaZero =>
      (analyticOrderNatAt riemannZeta r.val : ℝ)/‖r.val‖^2) := by
  obtain ⟨C, hC, hcount⟩ := zeta_quantitative_zero_count
  obtain ⟨δ, hδ, hd⟩ := zeta_zero_norm_lower
  let m := fun r : NontrivialZetaZero => analyticOrderNatAt riemannZeta r.val
  let N (T : ℝ) := C * (max T 1+2) * Real.log (max T 1+2)
  have h := multiplicity_majorant_summable (fun r : NontrivialZetaZero => r.val.im)
    m (8*C*Real.log 2) (fun j s hs => ?_)
  · let B := 1 + (δ^2)⁻¹
    apply (h.mul_left B).of_nonneg_of_le (fun _ => by positivity)
    intro r
    have hρ : 0 < ‖r.val‖ := hδ.trans_le (hd r)
    have hd' : δ^2 ≤ ‖r.val‖^2 := by nlinarith [hd r]
    have him := Complex.abs_im_le_norm r.val
    have him' : r.val.im^2 ≤ ‖r.val‖^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) him 2
    have h₁ : 1 ≤ (δ^2)⁻¹ * ‖r.val‖^2 := by
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ (by positivity)).2 (by simpa using hd')
    have hc : 1+r.val.im^2 ≤ B*‖r.val‖^2 := by
      dsimp [B]
      rw [add_mul, one_mul]
      linarith
    have hcmp : 1/‖r.val‖^2 ≤ B/(1+r.val.im^2) := by
      exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa using hc)
    calc
      _ = (m r : ℝ)*(1/‖r.val‖^2) := by simp [m, div_eq_mul_inv]
      _ ≤ (m r : ℝ)*(B/(1+r.val.im^2)) :=
        mul_le_mul_of_nonneg_left hcmp (Nat.cast_nonneg _)
      _ = _ := by simp only [div_eq_mul_inv]; ring
  · apply le_trans _ (cumulative_count_dyadic N C hC (fun T hT => by simp [N, max_eq_left hT]) j)
    exact hcount (max ((2:ℝ)^(j+1)) 1) s (le_max_right _ _)
      (fun r hr => (hs r hr).le.trans (le_max_left _ _))

abbrev RepeatedZetaZero := Σ r : NontrivialZetaZero, Fin (analyticOrderNatAt riemannZeta r.val)

theorem zeta_inverse_square_repeated :
    Summable (fun i : RepeatedZetaZero => 1/‖i.1.val‖^2) := by
  apply (summable_sigma_of_nonneg (fun _ => by positivity)).2
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using
    zeta_inverse_square_with_multiplicity

end RHConnections.SpectralTail
