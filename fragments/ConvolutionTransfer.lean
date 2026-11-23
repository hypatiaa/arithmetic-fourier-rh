import EndpointIBP
import WeightedBulk
import RelativeAnalytic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

open MeasureTheory Set
open scoped Interval Convolution
open ContinuousLinearMap

namespace RHConnections.ConvolutionTransfer
open EndpointIBP WeightedBulk RelativeResolvent

private theorem truncate (u R : ℝ) (hR : 0 ≤ R) (k g G : ℝ → ℂ)
    (hk : ∀ y, R < y → k (u-y) = 0)
    (hpos : ∀ y, 0 < y → g y = G y) (hneg : ∀ y, y ≤ 0 → g y = 0) :
    (∫ y : ℝ, k (u-y) * g y) = ∫ y in (0:ℝ)..R, k (u-y) * G y := by
  have he : (fun y : ℝ => k (u-y) * g y) =
      (Ioc 0 R).indicator (fun y => k (u-y) * G y) := by
    funext y
    by_cases hy : 0 < y
    · by_cases hyR : y ≤ R
      · rw [indicator_of_mem (show y ∈ Set.Ioc (0:ℝ) R from ⟨hy, hyR⟩), hpos y hy]
      · rw [indicator_of_notMem (fun h => hyR h.2), hk y (lt_of_not_ge hyR), zero_mul]
    · rw [indicator_of_notMem (fun h => hy h.1), hneg y (le_of_not_gt hy), mul_zero]
  rw [he, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hR]

theorem logTest_transfers (u b : ℝ) (z z₀ : ℂ) {ρ dρ ddρ : ℝ → ℂ}
    (hρ : ∀ t, HasDerivAt ρ (dρ t) t) (hdρ : ∀ t, HasDerivAt dρ (ddρ t) t)
    (hc : Continuous ddρ)
    (hs : ∀ t, t < b → ρ t = 0 ∧ dρ t = 0 ∧ ddρ t = 0) :
    (∫ y : ℝ, dρ (u-y) * logTest z z₀ y) = (∫ y : ℝ, ρ (u-y) * bulk 1 z z₀ y) ∧
    (∫ y : ℝ, ddρ (u-y) * logTest z z₀ y) =
      ρ u * (z₀-z) + ∫ y : ℝ, ρ (u-y) * bulk 2 z z₀ y := by
  let R := max 0 (u-b) + 1
  have hR : 0 ≤ R := by dsimp [R]; linarith [le_max_left 0 (u-b)]
  have hb : u-R < b := by dsimp [R]; linarith [le_max_right 0 (u-b)]
  have hs' (y : ℝ) (hy : R < y) := hs (u-y) (by linarith : u-y < b)
  have hcd : Continuous dρ := continuous_iff_continuousAt.mpr (fun t => (hdρ t).continuousAt)
  have hreflect : Continuous (fun y : ℝ => u-y) := continuous_const.sub continuous_id
  have h := exponential_transfers u R z z₀ hρ hdρ
    ((hcd.comp hreflect).intervalIntegrable 0 R) ((hc.comp hreflect).intervalIntegrable 0 R)
    (hs _ hb).1 (hs _ hb).2.1
  have hp (y : ℝ) (hy : 0 < y) : logTest z z₀ y = positiveBranch z z₀ y := by
    simp [logTest, positiveBranch, hy]
  have hz (y : ℝ) (hy : y ≤ 0) := vanishes_left z z₀ hy
  have hbz (j : ℕ) (y : ℝ) (hy : y ≤ 0) : bulk j z z₀ y = 0 := by
    simp [bulk, not_lt.mpr hy]
  have hb1 (y : ℝ) (hy : 0 < y) : bulk 1 z z₀ y = firstBranch z z₀ y := by
    simp [bulk, positiveFormula, firstBranch, hy]
  have hb2 (y : ℝ) (hy : 0 < y) : bulk 2 z z₀ y = secondBranch z z₀ y := by
    simp [bulk, positiveFormula, secondBranch, hy]
  rw [truncate u R hR dρ _ _ (fun y hy => (hs' y hy).2.1) hp hz,
    truncate u R hR ddρ _ _ (fun y hy => (hs' y hy).2.2) hp hz,
    truncate u R hR ρ _ _ (fun y hy => (hs' y hy).1) hb1 (hbz 1),
    truncate u R hR ρ _ _ (fun y hy => (hs' y hy).1) hb2 (hbz 2)]
  exact h

theorem deriv_convolution_logTest (u : ℝ) (z z₀ : ℂ) {k : ℝ → ℝ}
    (hk : HasCompactSupport k) (hs : ContDiff ℝ 2 k) :
    deriv (k ⋆ logTest z z₀) u = (k ⋆ bulk 1 z z₀) u ∧
    deriv (deriv (k ⋆ logTest z z₀)) u = (k u : ℂ) * (z₀-z) + (k ⋆ bulk 2 z z₀) u := by
  have hd : ContDiff ℝ 1 (deriv k) := hs.deriv'
  have H : IsCompact (tsupport k ∪ (tsupport (deriv k) ∪ tsupport (deriv (deriv k)))) :=
    IsCompact.union hk (IsCompact.union hk.deriv hk.deriv.deriv)
  obtain ⟨b, hb⟩ := H.bddBelow
  have hvan (t : ℝ) (ht : t < b) :
      (k t : ℂ) = 0 ∧ Complex.ofReal (deriv k t) = 0 ∧
        Complex.ofReal (deriv (deriv k) t) = 0 := by
    have hnot (hts : t ∈ tsupport k ∪ (tsupport (deriv k) ∪ tsupport (deriv (deriv k)))) :=
      ht.not_ge (hb hts)
    have h0 := image_eq_zero_of_notMem_tsupport (f := k) (fun h => hnot (Or.inl h))
    have h1 := image_eq_zero_of_notMem_tsupport (f := deriv k) (fun h => hnot (Or.inr (Or.inl h)))
    have h2 := image_eq_zero_of_notMem_tsupport (f := deriv (deriv k)) (fun h => hnot (Or.inr (Or.inr h)))
    simp [h0, h1, h2]
  have hk1 : ContDiff ℝ 1 k := hs.of_le (by norm_num)
  have h := logTest_transfers u b z z₀
    (fun t => ((hk1.differentiable (by simp) t).hasDerivAt.ofReal_comp))
    (fun t => ((hd.differentiable (by simp) t).hasDerivAt.ofReal_comp))
    (Complex.continuous_ofReal.comp hd.continuous_deriv_one) hvan
  have hg := (logTest_continuous z z₀).locallyIntegrable (μ := volume)
  have hder : deriv (k ⋆ logTest z z₀) = (deriv k ⋆ logTest z z₀) :=
    funext fun t => (hk.hasDerivAt_convolution_left (lsmul ℝ ℝ) hk1 hg t).deriv
  have hder₂ := (hk.deriv.hasDerivAt_convolution_left (lsmul ℝ ℝ) hd hg u).deriv
  rw [hder, hder₂]
  simpa only [convolution_lsmul_swap, Complex.real_smul] using! h

#print axioms logTest_transfers
#print axioms deriv_convolution_logTest
end RHConnections.ConvolutionTransfer
