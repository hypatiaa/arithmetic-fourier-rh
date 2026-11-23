import Verified

noncomputable section
namespace RHConnections.EntireCanonicalProduct.Data
open Filter CanonicalFactor SpectralTail AffineFromRealPart NormalizedEntireQuotient
variable (D : RHConnections.EntireCanonicalProduct.Data)

theorem product_norm_le_exp_three_halves (hsum : Summable (fun r : D.RepeatedZero => 1/(‖r.1.val‖ * Real.sqrt ‖r.1.val‖))) (s : ℂ) :
    ‖D.product s‖ ≤ Real.exp
      (3 * (‖s‖ * Real.sqrt ‖s‖) *
        ∑' r : D.RepeatedZero, 1/(‖r.1.val‖ * Real.sqrt ‖r.1.val‖)) := by
  let u := fun r : D.RepeatedZero => 1/(‖r.1.val‖ * Real.sqrt ‖r.1.val‖)
  let a := 3 * (‖s‖ * Real.sqrt ‖s‖)
  have h := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    D.product_locally_uniform).tendsto_at (Set.mem_univ s)
  have hterm (r : D.RepeatedZero) : ‖D.factor r s‖ ≤ Real.exp (a * u r) := by
    have he := norm_genusOne_le_exp_three_halves (s/r.1.val)
    rw [norm_div, Real.sqrt_div (norm_nonneg s)] at he
    have hh : ‖s‖ / ‖r.1.val‖ * (Real.sqrt ‖s‖ / Real.sqrt ‖r.1.val‖) =
        ‖s‖ * Real.sqrt ‖s‖ * u r := by dsimp [u]; ring
    rw [hh] at he
    unfold factor
    simpa only [a, mul_assoc] using he
  have hprod (S : Finset D.RepeatedZero) :
      (∏ r ∈ S, ‖D.factor r s‖) ≤ ∏ r ∈ S, Real.exp (a * u r) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert r S hr ih =>
      rw [Finset.prod_insert hr, Finset.prod_insert hr]
      exact mul_le_mul (hterm r) ih (by positivity) (Real.exp_pos _).le
  apply le_of_tendsto (continuous_norm.continuousAt.tendsto.comp h)
  filter_upwards with S
  change ‖∏ r ∈ S, D.factor r s‖ ≤ Real.exp (a * ∑' r, u r)
  rw [norm_prod]
  calc
    _ ≤ ∏ r ∈ S, Real.exp (a * u r) := hprod S
    _ = Real.exp (a * ∑ r ∈ S, u r) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (hsum.sum_le_tsum S (fun _ _ => by positivity))
      (by dsimp [a]; positivity))

theorem product_posLog_growth (hsum : Summable (fun r : D.RepeatedZero => 1/(‖r.1.val‖ * Real.sqrt ‖r.1.val‖))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ s ∈ Metric.sphere (0:ℂ) R,
      max 0 (Real.log ‖D.product s‖) ≤ C * (R * Real.sqrt R) := by
  let C := 3 * ∑' r : D.RepeatedZero, 1/(‖r.1.val‖ * Real.sqrt ‖r.1.val‖)
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (tsum_nonneg fun r => by positivity)
  refine ⟨C,hC,?_⟩
  intro R hR s hs
  have hrad : ‖s‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hs
  have hnonneg : 0 ≤ C*(R * Real.sqrt R) := by positivity
  apply max_le hnonneg
  by_cases hp : D.product s = 0
  · simpa [hp] using hnonneg
  have h := Real.log_le_log (norm_pos_iff.mpr hp) (D.product_norm_le_exp_three_halves hsum s)
  rw [Real.log_exp, hrad] at h
  exact h.trans_eq (by dsimp [C]; ring)

theorem mellin_envelope_circle_log {f : ℂ → ℂ} (hg : MellinGrowthEnvelope f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 3 ≤ R → ∀ s ∈ Metric.sphere (0:ℂ) R,
      Real.log ‖f s‖ ≤ C*(R*Real.sqrt R) := by
  obtain ⟨K,B,hK,hB,h⟩ := hg
  refine ⟨K+1+2*B,by positivity,?_⟩
  intro R hR s hs
  have hr : 0 < R := by linarith
  have hs' : ‖s‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hs
  have hsr : 1 ≤ Real.sqrt R := by simpa using Real.sqrt_le_sqrt (show 1 ≤ R by linarith)
  have hW : 1 ≤ R*Real.sqrt R := by nlinarith [mul_le_mul_of_nonneg_left hsr hr.le]
  have hlog : Real.log R ≤ 2*Real.sqrt R := by
    have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hr)
    rw [Real.log_sqrt hr.le] at hl
    linarith
  by_cases hz : f s = 0
  · simp only [hz, norm_zero, Real.log_zero]; positivity
  have hh : ‖f s‖ ≤ (K+1)*Real.exp (B*R*Real.log R) :=
    (h R (by linarith) s hs'.le).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  have hl := Real.log_le_log (norm_pos_iff.mpr hz) hh
  rw [Real.log_mul (show K+1 ≠ 0 by linarith) (Real.exp_pos _).ne', Real.log_exp] at hl
  have hconst : Real.log (K+1) ≤ (K+1)*(R*Real.sqrt R) := by
    calc Real.log (K+1) ≤ K+1 := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0<K+1)]
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hW (show 0≤K+1 by linarith)
  have hb := mul_le_mul_of_nonneg_left hlog (mul_nonneg hB hr.le)
  nlinarith

theorem hadamard_factorization (hg : MellinGrowthEnvelope D.F)
    (hsum : Summable (fun r : D.RepeatedZero => 1/(‖r.1.val‖ * Real.sqrt ‖r.1.val‖))) :
    ∃ b : ℂ, ∀ s : ℂ, D.F s = Complex.exp (b*s)*D.product s := by
  have ha (s : ℂ) := D.entire s (Set.mem_univ _)
  have hp (s : ℂ) := D.product_entire s (Set.mem_univ _)
  have hord (s : ℂ) : ∃ n : ℕ, analyticOrderAt D.F s = n ∧ analyticOrderAt D.product s = n := by
    by_cases hz : D.F s = 0
    · have h := (Nat.cast_analyticOrderNatAt (D.zero_finite_order ⟨s,hz⟩).2).symm
      exact ⟨_,h,(D.product_order_everywhere s).trans h⟩
    · have h := analyticOrderAt_eq_zero.mpr (Or.inr hz)
      exact ⟨0,by simpa using h,by simpa using (D.product_order_everywhere s).trans h⟩
  obtain ⟨G,hG,hG0,he⟩ := exists_normalized_entire_factor ha hp D.at_zero D.product_at_zero hord
  obtain ⟨Cx,hCx,hX⟩ := mellin_envelope_circle_log hg
  obtain ⟨Cp,hCp,hP⟩ := D.product_posLog_growth hsum
  have hgd : Differentiable ℂ G := fun z => (hG z).differentiableAt
  have hmean (R : ℝ) (hR : 3 ≤ R) : meanAbsRe G R ≤ 2*(Cx+Cp)*(R*Real.sqrt R) := by
    have hr : 0 < R := by linarith
    have hpr (s : ℂ) (hs : s ∈ Metric.sphere (0:ℂ) R) :
        Real.log ‖D.product s‖ ≤ Cp*(R*Real.sqrt R) :=
      (le_max_right _ _).trans (hP R hr.le s hs)
    apply (meanAbsRe_le_of_factor ha hp D.at_zero D.product_at_zero hgd he hr (hX R hR) hpr).trans
    have hm := max_le (le_add_of_nonneg_right (show 0 ≤ Cp*(R*Real.sqrt R) by positivity))
      (le_add_of_nonneg_left (show 0 ≤ Cx*(R*Real.sqrt R) by positivity))
    calc _ ≤ 2*(Cx*(R*Real.sqrt R) + Cp*(R*Real.sqrt R)) := mul_le_mul_of_nonneg_left hm (by norm_num)
         _ = _ := by ring
  have hAffine := affine_of_subquadratic_meanAbsRe hgd (subquadratic_mean_of_three_halves_bound _ hmean)
  refine ⟨deriv G 0, fun s => ?_⟩
  rw [he s, hAffine s, hG0, zero_add]

end RHConnections.EntireCanonicalProduct.Data
