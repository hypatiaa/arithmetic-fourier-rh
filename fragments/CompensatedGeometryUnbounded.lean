import Verified

open MeasureTheory Set
noncomputable section
namespace RHConnections.PrimeAtomObstruction
open EulerGeometricLimit ArchimedeanLimit

def geometricFunctional (G : ℝ → ℂ) (f : ℝ → ℂ) : ℂ :=
  (∑' m : ℕ, halfWeight m * f (Real.log m)) + ∫ x in Ioi (0:ℝ), G x*f x

def compensatedDensity (x : ℝ) : ℂ :=
  (realPlaceKernel x : ℂ) - Complex.exp ((1/2:ℂ)*(x:ℂ)) -
    Complex.exp ((-1/2:ℂ)*(x:ℂ))

theorem compensatedDensity_continuous : ContinuousOn compensatedDensity (Ioi 0) := by
  have hn : ∀ x ∈ Ioi (0:ℝ), 1-Real.exp (-2*x) ≠ 0 := by
    intro x hx
    have hp : Real.exp (-2*x) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by have : 0 < x := hx; linarith)
    exact sub_ne_zero.mpr (ne_of_gt hp)
  have hr : ContinuousOn realPlaceKernel (Ioi 0) := by
    unfold realPlaceKernel
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · exact hn
  have hrc := Complex.continuous_ofReal.continuousOn.comp hr (mapsTo_univ _ _)
  have hp : Continuous (fun x : ℝ => Complex.exp ((1/2:ℂ)*(x:ℂ))) := by fun_prop
  have hm : Continuous (fun x : ℝ => Complex.exp ((-1/2:ℂ)*(x:ℂ))) := by fun_prop
  exact (hrc.sub hp.continuousOn).sub hm.continuousOn

theorem arbitrarily_small_tests_preserve_atom {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) {G : ℝ → ℂ} (hG : ContinuousOn G (Ioi 0))
    {ε : ℝ} (hε : 0 < ε) : ∃ f : ℝ → ℂ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x ∉ Ioo 0 (Real.log 3), f x = 0) ∧
      f center = 1 ∧ 0 ≤ weightedMass w f ∧ weightedMass w f < ε ∧
      ‖geometricFunctional G f - halfWeight 2‖ < ε := by
  obtain ⟨A,hA,hMass⟩ := weightedMass_bound hw hw0
  obtain ⟨B,hB,hInt⟩ := density_integral_bound hG
  let C := A+B+1
  have hC : 0 < C := by dsimp [C]; linarith
  let r := min radius (ε/(4*C))
  have hr : 0 < r := lt_min radius_pos (div_pos hε (by positivity))
  have hr' : r ≤ radius := min_le_left _ _
  have hr'' : r ≤ ε/(4*C) := min_le_right _ _
  have he : (2*r)*C < ε := by
    have h := (le_div_iff₀ (show 0 < 4*C by positivity)).mp hr''
    nlinarith
  let f := test r hr
  have hvan : ∀ x ∉ Ioo 0 (Real.log 3), f x = 0 := fun x hx =>
    test_zero_off_interval r hr (fun h => hx (closed_support_inside (support_interval_inside hr' h)))
  have htwo : f (Real.log 2) = 1 := test_at_center r hr
  have hsum := prime_sum_eq_halfWeight_two f htwo hvan
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  refine ⟨f,test_smooth r hr,test_compact r hr,hvan,htwo,(hMass r hr hr').1,?_,?_⟩
  · exact ((hMass r hr hr').2.trans (mul_le_mul_of_nonneg_left hAC (by positivity))).trans_lt he
  · rw [geometricFunctional,hsum,add_sub_cancel_left]
    exact ((hInt r hr hr').trans (mul_le_mul_of_nonneg_left hBC (by positivity))).trans_lt he

theorem compensated_geometric_unbounded_in_strip (a b s : ℝ) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∀ x ∉ Ioo 0 (Real.log 3), f x = 0) →
      ‖geometricFunctional compensatedDensity f‖ ≤ C*Real.sqrt (weightedMass (stripWeight a b s) f) := by
  rintro ⟨C,hC,hBound⟩
  let M := ‖halfWeight 2‖
  have hM : 0 < M := norm_pos_iff.mpr halfWeight_two_ne_zero
  let q := M/(4*(C+1))
  have hq : 0 < q := div_pos hM (by positivity)
  let ε := min (M/4) (q^2)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨f,hDf,hSf,hVf,_,hf₀,hf,hG⟩ := arbitrarily_small_tests_preserve_atom
    (stripWeight_continuous a b s) (stripWeight_nonneg a b s) compensatedDensity_continuous hε
  have hSq : Real.sqrt (weightedMass (stripWeight a b s) f) ≤ q := by
    refine (Real.sqrt_le_sqrt (hf.le.trans (min_le_right _ _))).trans_eq ?_
    exact Real.sqrt_sq hq.le
  have hG' := (hBound f hDf hSf hVf).trans (mul_le_mul_of_nonneg_left hSq hC)
  have hprod : (4*(C+1))*q = M := by
    dsimp [q]
    field_simp
  have hnorm := norm_sub_le (geometricFunctional compensatedDensity f)
    (geometricFunctional compensatedDensity f - halfWeight 2)
  rw [sub_sub_cancel] at hnorm
  have hd : ε ≤ M/4 := min_le_left _ _
  change M ≤ _ at hnorm
  nlinarith only [hnorm,hG',hG,hd,hprod,hq,hM]

end RHConnections.PrimeAtomObstruction
