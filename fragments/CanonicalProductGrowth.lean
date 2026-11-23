import Verified

open Filter
noncomputable section
namespace RHConnections.CanonicalFactor
open SpectralTail

theorem norm_genusOne_le_exp_three_halves (w : ℂ) :
    ‖genusOne w‖ ≤ Real.exp (3 * (‖w‖ * Real.sqrt ‖w‖)) := by
  let r := ‖w‖
  have hr : 0 ≤ r := norm_nonneg _
  have hsq : (Real.sqrt r)^2 = r := Real.sq_sqrt hr
  by_cases hsmall : r ≤ 1
  · have hs1 : Real.sqrt r ≤ 1 := by simpa using Real.sqrt_le_sqrt hsmall
    have hrs : r ≤ Real.sqrt r := by
      nlinarith [Real.sqrt_nonneg r, mul_nonneg (Real.sqrt_nonneg r) (sub_nonneg.mpr hs1)]
    calc
      _ ≤ ‖genusOne w - 1‖ + 1 := by
        calc
          _ = ‖genusOne w - 1 + 1‖ := by rw [sub_add_cancel]
          _ ≤ _ := by simpa only [norm_one] using norm_add_le (genusOne w - 1) (1:ℂ)
      _ ≤ 3 * r^2 + 1 := add_le_add_left (norm_genusOne_sub_one_le hsmall) _
      _ ≤ 3 * (r * Real.sqrt r) + 1 := by nlinarith [mul_le_mul_of_nonneg_left hrs hr]
      _ ≤ _ := by
        simpa only [add_comm] using Real.add_one_le_exp (3 * (r * Real.sqrt r))
  · have h1 : 1 ≤ r := le_of_lt (lt_of_not_ge hsmall)
    have hs1 : 1 ≤ Real.sqrt r := by simpa using Real.sqrt_le_sqrt h1
    have hw : ‖(1 : ℂ)-w‖ ≤ 1+r := by simpa [r] using norm_sub_le (1:ℂ) w
    calc
      _ ≤ (1+r)*Real.exp r := by
        rw [genusOne, norm_mul, Complex.norm_exp]
        exact mul_le_mul hw (Real.exp_le_exp.mpr (Complex.re_le_norm w))
          (Real.exp_pos _).le (by positivity)
      _ ≤ Real.exp r * Real.exp r :=
        mul_le_mul_of_nonneg_right (by simpa [add_comm] using Real.add_one_le_exp r)
          (Real.exp_pos _).le
      _ ≤ _ := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hs1 hr])

theorem norm_zetaCanonicalProduct_le_exp_three_halves (s : ℂ) :
    ‖zetaCanonicalProduct s‖ ≤ Real.exp
      (3 * (‖s‖ * Real.sqrt ‖s‖) *
        ∑' r : RepeatedZetaZero, 1/(‖r.1.val‖ * Real.sqrt ‖r.1.val‖)) := by
  let u := fun r : RepeatedZetaZero => 1/(‖r.1.val‖ * Real.sqrt ‖r.1.val‖)
  let a := 3 * (‖s‖ * Real.sqrt ‖s‖)
  have h := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    zetaCanonicalProduct_locally_uniform).tendsto_at (Set.mem_univ s)
  have hterm (r : RepeatedZetaZero) : ‖zetaFactor r s‖ ≤ Real.exp (a * u r) := by
    have he := norm_genusOne_le_exp_three_halves (s/r.1.val)
    rw [norm_div, Real.sqrt_div (norm_nonneg s)] at he
    have hh : ‖s‖ / ‖r.1.val‖ * (Real.sqrt ‖s‖ / Real.sqrt ‖r.1.val‖) =
        ‖s‖ * Real.sqrt ‖s‖ * u r := by dsimp [u]; ring
    rw [hh] at he
    unfold zetaFactor
    simpa only [a, mul_assoc] using he
  have hprod (S : Finset RepeatedZetaZero) :
      (∏ r ∈ S, ‖zetaFactor r s‖) ≤ ∏ r ∈ S, Real.exp (a * u r) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert r S hr ih =>
      rw [Finset.prod_insert hr, Finset.prod_insert hr]
      exact mul_le_mul (hterm r) ih (by positivity) (Real.exp_pos _).le
  apply le_of_tendsto (continuous_norm.continuousAt.tendsto.comp h)
  filter_upwards with S
  change ‖∏ r ∈ S, zetaFactor r s‖ ≤ Real.exp (a * ∑' r, u r)
  rw [norm_prod]
  calc
    _ ≤ ∏ r ∈ S, Real.exp (a * u r) := hprod S
    _ = Real.exp (a * ∑ r ∈ S, u r) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (zeta_inverse_three_halves_repeated.sum_le_tsum S (fun _ _ => by positivity))
      (by dsimp [a]; positivity))

theorem zetaCanonicalProduct_posLog_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ s ∈ Metric.sphere (0:ℂ) R,
      max 0 (Real.log ‖zetaCanonicalProduct s‖) ≤ C * (R * Real.sqrt R) := by
  let C := 3 * ∑' r : RepeatedZetaZero, 1/(‖r.1.val‖ * Real.sqrt ‖r.1.val‖)
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (tsum_nonneg fun r => by positivity)
  refine ⟨C,hC,?_⟩
  intro R hR s hs
  have hrad : ‖s‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hs
  have hnonneg : 0 ≤ C*(R * Real.sqrt R) := by positivity
  apply max_le hnonneg
  by_cases hp : zetaCanonicalProduct s = 0
  · simpa [hp] using hnonneg
  have h := Real.log_le_log (norm_pos_iff.mpr hp) (norm_zetaCanonicalProduct_le_exp_three_halves s)
  rw [Real.log_exp, hrad] at h
  exact h.trans_eq (by dsimp [C]; ring)

end RHConnections.CanonicalFactor
