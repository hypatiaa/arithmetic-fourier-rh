import Verified

open MeasureTheory
open scoped Classical
noncomputable section
namespace RHConnections.DirichletZeroSet
open DirichletCharacter SpectralTail EntireCanonicalProduct
open FourierTestInversion PoleCompensation DirichletFourierPairing

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

theorem dirichlet_zero_square_summable (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Summable (fun r : DirichletNontrivialZero χ =>
      (analyticOrderNatAt (LFunction χ) r.val : ℝ)/‖r.val‖^2) := by
  let D := dirichletProductData χ hp hχ
  let e := normalized_dirichlet_zero_equiv χ hp hχ
  have h := ((summable_sigma_of_nonneg
    (fun r : D.RepeatedZero => by positivity : ∀ r : D.RepeatedZero, 0 ≤ 1/‖r.1.val‖^2)).mp
    D.square_summable).2
  have h' : Summable (fun r : D.Zero => (analyticOrderNatAt (LFunction χ) r.val : ℝ)/‖r.val‖^2) := by
    have he (r : D.Zero) : analyticOrderNatAt D.F r.val =
        analyticOrderNatAt (LFunction χ) r.val := by
      unfold analyticOrderNatAt
      exact congrArg ENat.toNat (normalized_completed_order χ hp hχ (e r).property.1.1)
    simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, he] using h
  apply e.summable_iff.mp
  exact h'

theorem dirichlet_nontrivial_zeros_countable (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Countable (DirichletNontrivialZero χ) := by
  let D := dirichletProductData χ hp hχ
  let e := normalized_dirichlet_zero_equiv χ hp hχ
  let b := fun r : DirichletNontrivialZero χ =>
    (analyticOrderNatAt (LFunction χ) r.val : ℝ)/‖r.val‖^2
  have hb : Summable b := dirichlet_zero_square_summable χ hp hχ
  have hpos (r : DirichletNontrivialZero χ) : 0 < b r := by
    have hr : r.val ≠ 0 := fun he => by
      have h := r.property.1.1
      rw [he, Complex.zero_re] at h
      exact (lt_irrefl _) h
    obtain ⟨ha,hfin⟩ := D.zero_finite_order (e.symm r)
    have hnat : analyticOrderNatAt (LFunction χ) r.val ≠ 0 := by
      intro he
      have horder := Nat.cast_analyticOrderNatAt hfin
      change (analyticOrderNatAt (normalizedCompletedDirichlet χ) r.val : ℕ∞) =
        analyticOrderAt (normalizedCompletedDirichlet χ) r.val at horder
      simp only [analyticOrderNatAt, normalized_completed_order χ hp hχ r.property.1.1] at horder
      have h0 : analyticOrderAt (LFunction χ) r.val = 0 := by
        rw [← horder]
        exact_mod_cast he
      rcases analyticOrderAt_eq_zero.mp h0 with hna | hn
      · exact hna ((differentiable_LFunction hχ).analyticAt _)
      · exact hn r.property.2
    exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnat)) (sq_pos_of_pos (norm_pos_iff.mpr hr))
  have hsup : Function.support b = Set.univ := by
    ext r
    simp [Function.mem_support, (hpos r).ne']
  exact Set.countable_univ_iff.mp (hsup ▸ hb.countable_support)

theorem dirichlet_explicit_formula_compact (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hzero : f 0 = 0) :
    (∑' m : ℕ, DirichletGeometricLimit.halfWeight χ m * f (Real.log m)) +
      (∫ x in Set.Ioi (0:ℝ), (parityRealPlaceKernel (if χ.Even then false else true) x:ℂ)*f x) =
      -(∑' r : DirichletNontrivialZero χ, (analyticOrderNatAt (LFunction χ) r.val : ℂ) *
        ∫ x in Set.Ioi (0:ℝ), Complex.exp ((r.val-(1/2:ℂ))*(x:ℂ))*f x) := by
  let odd := if χ.Even then false else true
  let p (v : ℝ) := testFourier f v *
    (logDeriv (LFunction χ) (3/2) - logDeriv (LFunction χ) (verticalProbe v+1/2))
  let a (v : ℝ) := testFourier f v * parityRealPlaceRelative odd (verticalProbe v) 1
  let s (v : ℝ) := testFourier f v * dirichletSpectralRelative χ (verticalProbe v) 1
  haveI : Countable (DirichletNontrivialZero χ) := dirichlet_nontrivial_zeros_countable χ hp hχ
  have hne (r : DirichletNontrivialZero χ) : r.val ≠ 0 := fun he => by
    have h := r.property.1.1
    rw [he, Complex.zero_re] at h
    exact (lt_irrefl _) h
  have hS := pair_carrierSpectralRelative (fun r : DirichletNontrivialZero χ => r.val)
    (fun r => analyticOrderNatAt (LFunction χ) r.val) (fun r => r.property.1.2)
    hne (dirichlet_zero_square_summable χ hp hχ) hf hc hzero
  obtain ⟨hPi,hP⟩ := LFunction_prime_fourier_pairing χ hf hc hzero
  obtain ⟨hAi,hA⟩ := pair_parityRealPlaceRelative odd hf hc hzero
  have hEuler (v : ℝ) : (p+a) v = (-s) v := by
    change p v + a v = -s v
    dsimp only [p,a,s,odd]
    rw [← mul_add, show (3/2:ℂ) = 1+1/2 by ring,
      dirichlet_euler_balance χ hp hχ (z := verticalProbe v) (z₀ := 1)
        (by rw [verticalProbe_re]; norm_num) (by norm_num), mul_neg]
  have hI : (∫ v : ℝ, (p+a) v) = ∫ v : ℝ, (-s) v :=
    integral_congr_ae (ae_of_all _ hEuler)
  change Integrable p at hPi
  change Integrable a at hAi
  change (∫ v : ℝ, p v) = _ at hP
  change (∫ v : ℝ, a v) = _ at hA
  change (∫ v : ℝ, s v) = _ at hS
  rw [integral_add' hPi hAi, hP, hA, integral_neg' s, hS] at hI
  exact hI

end RHConnections.DirichletZeroSet
