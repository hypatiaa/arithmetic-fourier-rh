import AstraPrimeRightCut

open Filter Set
noncomputable section
namespace RHConnections.PrimeRightCut
open SpectralTail ChebyshevCriterion SmoothedPrimeLimit

theorem rightSet_finite (T : ℝ) : (rightSet T).Finite := by
  let H := Real.exp (T/3)
  have hH : 0 < H := Real.exp_pos _
  have hε : 0 < 1/H^2 := by positivity
  have hev : ∀ᶠ r : NontrivialZetaZero in cofinite, w2 r < 1/H^2 :=
    zeta_inverse_square_with_multiplicity.tendsto_cofinite_zero.eventually_lt
      (tendsto_const_nhds (x := 1/H^2)) hε
  apply (show {r : NontrivialZetaZero | ¬ w2 r < 1/H^2}.Finite from hev).subset
  intro r hr
  have hN : 0 < ‖r.val‖ := by
    obtain ⟨d, hd, h⟩ := zeta_zero_norm_lower
    exact hd.trans_le (h r)
  obtain ⟨ha,hord⟩ := zeta_nontrivial_zero_finite_order r
  have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta r.val := by
    exact_mod_cast (Nat.succ_le_of_lt (zero_order_positive r.property.2 ha hord))
  have hnorm : ‖r.val‖ ≤ H := hr.2
  change ¬ w2 r < 1/H^2
  apply not_lt.mpr
  calc
    _ ≤ 1/‖r.val‖^2 := div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hN)
      (pow_le_pow_left₀ hN.le hnorm 2)
    _ ≤ _ := div_le_div_of_nonneg_right hm (sq_nonneg _)

theorem rightSum_finite (T : ℝ) (f : ℝ → ℂ) :
    rightSum T f = ∑ r ∈ (rightSet_finite T).toFinset, compactZeroTerm (scaleTest T f) r := by
  classical
  unfold rightSum
  rw [tsum_eq_sum (s := (rightSet_finite T).toFinset) (fun r hr =>
    indicator_of_notMem (by simpa using hr) _)]
  apply Finset.sum_congr rfl
  intro r hr
  exact indicator_of_mem (by simpa using hr) _

theorem dyadic_endpoint_reduction_X :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, Real.exp 2 ≤ X →
      |(Chebyshev.psi (2*X)-Chebyshev.psi X)-X| ≤
        (X/Real.exp 1)*dyadicRight (Real.log X - 1) + C*X^(11/12 : ℝ) := by
  obtain ⟨C,hC,h⟩ := dyadic_endpoint_reduction
  refine ⟨C,hC,?_⟩
  intro X hX
  have hX0 := (Real.exp_pos 2).trans_le hX
  let T := Real.log X-1
  have hT : 1 ≤ T := by
    have e := Real.log_le_log (Real.exp_pos 2) hX
    rw [Real.log_exp] at e
    dsimp [T]; linarith
  have he : Real.exp (T+1) = X := by dsimp [T]; rw [sub_add_cancel,Real.exp_log hX0]
  have heT : Real.exp T = X/Real.exp 1 := by simp only [T,Real.exp_sub,Real.exp_log hX0]
  have heP : Real.exp T * Real.exp (-(T/12)) ≤ X^(11/12 : ℝ) := by
    rw [← Real.exp_add,Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.mpr
    dsimp only [T]
    linarith
  have hres := h T hT
  rw [he, mul_add] at hres
  apply hres.trans
  rw [← heT]
  exact add_le_add (le_refl _) (by
    calc
      Real.exp T * (C*Real.exp (-(T/12))) = C*(Real.exp T*Real.exp (-(T/12))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left heP hC)

#print axioms rightSet_finite
#print axioms rightSum_finite
#print axioms dyadic_endpoint_reduction_X
end RHConnections.PrimeRightCut
