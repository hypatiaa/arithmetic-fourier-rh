import Verified

open MeasureTheory Set
noncomputable section
namespace RHConnections.PrimeAtomObstruction
open EulerGeometricLimit ArchimedeanLimit PoleCompensation SpectralTail

def zeroDensity (rho : NontrivialZetaZero) (x : ℝ) : ℂ :=
  (analyticOrderNatAt riemannZeta rho.val : ℂ) *
    Complex.exp ((rho.val-(1/2:ℂ))*(x:ℂ))

def zeroTest (f : ℝ → ℂ) (rho : NontrivialZetaZero) : ℂ :=
  ∫ x in Ioi (0:ℝ), zeroDensity rho x*f x

private theorem integrableOn_mul_bump {G : ℝ → ℂ} (hG : ContinuousOn G (Ioi 0))
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ radius) :
    IntegrableOn (fun x => G x * test r hr x) (Ioi (0:ℝ)) := by
  let J := Icc (center-radius) (center+radius)
  let g := fun x => G x * test r hr x
  have hJ : J ⊆ Ioi (0:ℝ) := fun _ hx => (closed_support_inside hx).1
  have hgc : ContinuousOn g J :=
    (hG.mono hJ).mul (test_smooth r hr).continuous.continuousOn
  have hi : IntegrableOn g J := hgc.integrableOn_compact isCompact_Icc
  have hJm : MeasurableSet J := measurableSet_Icc
  have he : J.indicator g = g := by
    funext x
    by_cases hx : x ∈ J
    · exact indicator_of_mem hx _
    · simp [indicator_of_notMem hx,test_zero_off_interval r hr (fun h => hx (support_interval_inside hr' h)),g]
  exact (he ▸ hi.integrable_indicator hJm).integrableOn

theorem geometric_eq_neg_full_zero_sum_on_bumps {r : ℝ} (hr : 0 < r) (hr' : r ≤ radius) :
    geometricFunctional compensatedDensity (test r hr) =
      -∑' rho : NontrivialZetaZero, zeroTest (test r hr) rho := by
  let f := test r hr
  have hf₀ : f 0 = 0 := test_zero_off_interval r hr
    (fun h => (lt_irrefl 0) (closed_support_inside (support_interval_inside hr' h)).1)
  have h := zeta_explicit_formula_compact f (test_smooth r hr) (test_compact r hr) hf₀
  let p := fun x : ℝ => Complex.exp ((1/2:ℂ)*(x:ℂ))
  let m := fun x : ℝ => Complex.exp ((-1/2:ℂ)*(x:ℂ))
  let a := fun x : ℝ => (realPlaceKernel x:ℂ)
  have hpc : Continuous p := by unfold p; fun_prop
  have hmc : Continuous m := by unfold m; fun_prop
  have hac : ContinuousOn a (Ioi 0) := by
    have h : a = fun x => compensatedDensity x + p x + m x := by
      funext x
      unfold compensatedDensity a p m
      ring
    rw [h]
    exact (compensatedDensity_continuous.add hpc.continuousOn).add hmc.continuousOn
  have hi := integrableOn_mul_bump hac hr hr'
  have hp := integrableOn_mul_bump hpc.continuousOn hr hr'
  have hm := integrableOn_mul_bump hmc.continuousOn hr hr'
  have hsplit : (∫ x in Ioi (0:ℝ), compensatedDensity x * f x) =
      (∫ x in Ioi (0:ℝ), a x*f x) - (∫ x in Ioi (0:ℝ), p x*f x) -
        ∫ x in Ioi (0:ℝ), m x*f x := by
    simp only [compensatedDensity,sub_mul]
    exact (integral_sub' (hi.sub hp) hm).trans (by rw [integral_sub' hi hp])
  have hTest (rho : NontrivialZetaZero) : zeroTest f rho =
      (analyticOrderNatAt riemannZeta rho.val : ℂ) *
        ∫ x in Ioi (0:ℝ), Complex.exp ((rho.val-(1/2:ℂ))*(x:ℂ))*f x := by
    simp only [zeroTest,zeroDensity,mul_assoc,integral_const_mul]
  change (∑' m : ℕ, halfWeight m*f (Real.log m)) + (∫ x in Ioi (0:ℝ), a x*f x) =
    (∫ x in Ioi (0:ℝ), p x*f x) + (∫ x in Ioi (0:ℝ), m x*f x) -
      (∑' rho : NontrivialZetaZero, _) at h
  rw [geometricFunctional,hsplit]
  simp_rw [← hTest] at h
  linear_combination h

theorem finite_spectral_sum_misses_prime_atom (T : Finset NontrivialZetaZero) (a b s : ℝ)
    {ε : ℝ} (hε : 0 < ε) : ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ x ∉ Ioo 0 (Real.log 3), f x = 0) ∧
      weightedMass (stripWeight a b s) f < ε ∧
      ‖∑ rho ∈ T, zeroTest f rho‖ < ε ∧
      ‖(∑' rho : NontrivialZetaZero, zeroTest f rho) + halfWeight 2‖ < ε := by
  let G := fun x => ∑ rho ∈ T, zeroDensity rho x
  have hG : Continuous G := continuous_finsetSum _ fun rho _ => by
    unfold zeroDensity
    fun_prop
  obtain ⟨A,hA,hMass⟩ := weightedMass_bound (stripWeight_continuous a b s) (stripWeight_nonneg a b s)
  obtain ⟨B,hB,hGeom⟩ := density_integral_bound compensatedDensity_continuous
  obtain ⟨D,hD,hFin⟩ := density_integral_bound hG.continuousOn
  let C := A+B+D+1
  have hC : 0 < C := by dsimp [C]; linarith
  let r := min radius (ε/(4*C))
  have hr : 0 < r := lt_min radius_pos (div_pos hε (by positivity))
  have hr' : r ≤ radius := min_le_left _ _
  have hr'' : r ≤ ε/(4*C) := min_le_right _ _
  have he : (2*r)*C < ε := by nlinarith [(le_div_iff₀ (show 0 < 4*C by positivity)).mp hr'']
  let f := test r hr
  have hvan : ∀ x ∉ Ioo 0 (Real.log 3), f x = 0 := fun x hx =>
    test_zero_off_interval r hr (fun h => hx (closed_support_inside (support_interval_inside hr' h)))
  refine ⟨f,test_smooth r hr,test_compact r hr,hvan,?_,?_,?_⟩
  · exact ((hMass r hr hr').2.trans
      (mul_le_mul_of_nonneg_left (by dsimp [C]; linarith : A ≤ C) (by positivity))).trans_lt he
  · have hsum : (∑ rho ∈ T, zeroTest f rho) = ∫ x in Ioi (0:ℝ), G x*f x := by
      unfold zeroTest
      rw [← integral_finsetSum]
      · simp only [G,Finset.sum_mul]
      · intro rho hrho
        have hρ : Continuous (zeroDensity rho) := by unfold zeroDensity; fun_prop
        exact integrableOn_mul_bump hρ.continuousOn hr hr'
    rw [hsum]
    exact ((hFin r hr hr').trans
      (mul_le_mul_of_nonneg_left (by dsimp [C]; linarith : D ≤ C) (by positivity))).trans_lt he
  · have hsum := geometric_eq_neg_full_zero_sum_on_bumps hr hr'
    have hAtom := prime_sum_eq_halfWeight_two f (test_at_center r hr) hvan
    have hd : (∑' rho : NontrivialZetaZero, zeroTest f rho) + halfWeight 2 =
        -(∫ x in Ioi (0:ℝ), compensatedDensity x*f x) := by
      change geometricFunctional compensatedDensity f =
        -(∑' rho : NontrivialZetaZero, zeroTest f rho) at hsum
      rw [geometricFunctional,hAtom] at hsum
      linear_combination hsum
    rw [hd,norm_neg]
    exact ((hGeom r hr hr').trans
      (mul_le_mul_of_nonneg_left (by dsimp [C]; linarith : B ≤ C) (by positivity))).trans_lt he

end RHConnections.PrimeAtomObstruction
