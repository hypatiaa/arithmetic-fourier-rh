import Verified

open MeasureTheory
namespace RHConnections.PoleCompensation
open FourierTestInversion RelativeResolvent CanonicalFactor SpectralTail
open EulerGeometricLimit ArchimedeanLimit Mollifier FourierDecay WeightedConvolution

theorem zeta_explicit_formula_compact (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hzero : f 0 = 0) :
    (∑' m : ℕ, halfWeight m*f (Real.log m)) +
        (∫ x in Set.Ioi (0:ℝ), (realPlaceKernel x:ℂ)*f x) =
      (∫ x in Set.Ioi (0:ℝ), Complex.exp ((1/2:ℂ)*(x:ℂ))*f x) +
      (∫ x in Set.Ioi (0:ℝ), Complex.exp ((-1/2:ℂ)*(x:ℂ))*f x) -
      (∑' r : NontrivialZetaZero, (analyticOrderNatAt riemannZeta r.val : ℂ) *
        ∫ x in Set.Ioi (0:ℝ), Complex.exp ((r.val-(1/2:ℂ))*(x:ℂ))*f x) := by
  let F := testFourier f
  let P := fun v : ℝ =>
    -deriv riemannZeta (verticalProbe v+1/2)/riemannZeta (verticalProbe v+1/2) +
      deriv riemannZeta (3/2)/riemannZeta (3/2)
  let A := fun v : ℝ => realPlaceRelative (verticalProbe v) 1
  let R := fun v : ℝ => relative (verticalProbe v) 1 (1/2:ℂ)
  let M := fun v : ℝ => relative (verticalProbe v) 1 (-1/2:ℂ)
  let S := fun v : ℝ => zetaSpectralRelative (verticalProbe v) 1
  have hEuler (v : ℝ) : P v + A v - R v - M v = -S v := by
    have hz : 1/2 < (verticalProbe v).re := by rw [verticalProbe_re]; norm_num
    have h1 : 1/2 < (1:ℂ).re := by norm_num
    have h := compensated_zeta_spectral_euler_match zeta_hadamard_factorization
      (verticalProbe v) 1 hz h1 (realPlaceRelative_eq_gammaDifference (by linarith) (by linarith))
    have he (w : ℂ) : 1/(w+1/2-1) = (w-1/2)⁻¹ := by
      rw [show w+1/2-1 = w-1/2 by ring, one_div]
    rw [show ((-1/2:ℝ):ℂ) = (-1/2:ℂ) by norm_num] at h
    simp only [P,A,R,M,S,relative]
    simp only [compensatedLogDerivative, he, relative] at h
    rw [show (1:ℂ)+1/2=3/2 by ring] at h
    linear_combination h
  have hphase (v x : ℝ) :
      Complex.exp ((((2*Real.pi*v : ℝ):ℂ)*Complex.I)*(x:ℂ)) = phase v x := by
    unfold phase
    congr 1
    simp only [Complex.ofReal_mul]
    ring
  have hF := testFourier_integrable hf hc
  have hFc := testFourier_integrable_cubic hf hc
  have ⟨hPi,hP⟩ := prime_fourier_pairing hf hc hzero
  have ⟨hAi,hA⟩ := realPlace_fourier_pairing F f hF.aestronglyMeasurable.aemeasurable
    (by simpa only [mul_comm] using hFc) (by
      intro x _
      simp_rw [hphase]
      simpa only [F, twistedTest, Complex.real_smul, Complex.ofReal_exp] using
        testFourier_compensated_inversion hf hc hzero x)
  have ⟨hRi,hR⟩ := pair_relative_resolvent hf hc hzero (xi := (1/2:ℂ)) (by norm_num)
  have ⟨hMi,hM⟩ := pair_relative_resolvent hf hc hzero (xi := (-1/2:ℂ)) (by norm_num)
  have hS := pair_zetaSpectralRelative hf hc hzero
  change Integrable (fun v => F v * A v) at hAi
  change (∫ v : ℝ, F v * A v) = _ at hA
  have heq :
      (∫ v : ℝ, (F v*P v + F v*A v - F v*R v - F v*M v)) =
        ∫ v : ℝ, -(F v*S v) := by
    apply integral_congr_ae
    filter_upwards with v
    rw [← mul_add, ← mul_sub, ← mul_sub, hEuler, mul_neg]
  let p := fun v => F v * P v
  let a := fun v => F v * A v
  let r := fun v => F v * R v
  let m := fun v => F v * M v
  let s := fun v => F v * S v
  change Integrable p at hPi
  change Integrable a at hAi
  change Integrable r at hRi
  change Integrable m at hMi
  change (∫ v, p v) = _ at hP
  change (∫ v, a v) = _ at hA
  change (∫ v, r v) = _ at hR
  change (∫ v, m v) = _ at hM
  change (∫ v, s v) = _ at hS
  change (∫ v, ((p+a-r-m) v)) = (∫ v, (-s) v) at heq
  rw [integral_sub' ((hPi.add hAi).sub hRi) hMi, integral_sub' (hPi.add hAi) hRi,
    integral_add' hPi hAi, hP, hA, hR, hM, integral_neg' s, hS] at heq
  linear_combination heq

theorem angular_weighted_eq_positive_laplace (f : ℝ → ℂ) (xi : ℂ)
    (hf : ∀ x ≤ 0, f x = 0) :
    angularTransform (weighted xi.re f) xi.im =
      ∫ x in Set.Ioi (0:ℝ), Complex.exp (xi*(x:ℂ))*f x := by
  rw [angular_integral, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases h : 0 < x
  · rw [Set.indicator_of_mem (show x ∈ Set.Ioi (0:ℝ) from h), weighted, Complex.real_smul, Complex.ofReal_exp,
      ← mul_assoc, ← Complex.exp_add]
    congr 2
    calc
      _ = ((xi.re:ℂ)+(xi.im:ℂ)*Complex.I)*(x:ℂ) := by push_cast; ring
      _ = _ := by rw [Complex.re_add_im]
  · simp [Set.indicator_of_notMem (show x ∉ Set.Ioi (0:ℝ) from h), weighted, hf x (le_of_not_gt h)]

theorem zeta_full_finite_trace (z₀ : ℂ) : ZetaFullFiniteTrace z₀ := by
  intro z n
  let f := fullCandidate n z z₀
  have hf (x : ℝ) (hx : x ≤ 0) : f x = 0 :=
    fullCandidate_vanishes_left n z z₀ (hx.trans (epsilon_pos n).le)
  have h := zeta_explicit_formula_compact f (fullCandidate_smooth n z z₀)
    (fullCandidate_compact n z z₀) (hf 0 le_rfl)
  have hp (a : ℝ) : poleTest a n z z₀ =
      ∫ x in Set.Ioi (0:ℝ), Complex.exp ((a:ℂ)*(x:ℂ))*f x := by
    have h := angular_weighted_eq_positive_laplace f (a:ℂ) hf
    simpa only [poleTest, Complex.ofReal_re, Complex.ofReal_im, f] using h
  have hs : zetaSpectralTest n z z₀ =
      ∑' r : NontrivialZetaZero, (analyticOrderNatAt riemannZeta r.val : ℂ) *
        ∫ x in Set.Ioi (0:ℝ), Complex.exp ((r.val-(1/2:ℂ))*(x:ℂ))*f x := by
    unfold zetaSpectralTest
    apply tsum_congr
    intro r
    rw [angular_weighted_eq_positive_laplace f _ hf]
  rw [hp, hp, hs]
  norm_num [primeTest, realPlaceTest, f] at h ⊢
  exact h

theorem cofinal_zeta_traces_iff_RH_unconditional {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) :
    (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ a < ε ∧ a < 1/2 ∧ ZetaRestrictedTrace a z₀)
      ↔ RiemannHypothesis :=
  cofinal_zeta_traces_iff_RH hz₀ (zeta_full_finite_trace z₀)

end RHConnections.PoleCompensation
