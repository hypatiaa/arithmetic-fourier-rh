import Verified

open Filter MeasureTheory
open scoped Topology Classical
noncomputable section
namespace RHConnections.DirichletZeroSet
open DirichletCharacter SpectralTail RelativeResolvent PoleCompensation
open FourierDecay WeightedConvolution Mollifier

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

abbrev DirichletStripZero (a : ℝ) :=
  {r : DirichletNontrivialZero χ | |r.val.re-1/2| ≤ a}

def dirichletRestrictedResidual (a : ℝ) (n : ℕ) (z z₀ : ℂ) : ℂ :=
  (∑' m, DirichletGeometricLimit.halfWeight χ m * fullCandidate n z z₀ (Real.log m)) +
    (∫ x in Set.Ioi (0:ℝ), (parityRealPlaceKernel (if χ.Even then false else true) x : ℂ) *
      fullCandidate n z z₀ x) +
    ∑' r : DirichletStripZero χ a, (analyticOrderNatAt (LFunction χ) r.val.val : ℂ) *
      angularTransform (weighted (r.val.val-(1/2:ℂ)).re (fullCandidate n z z₀))
        (r.val.val-(1/2:ℂ)).im

theorem parityRelative_analyticAt (odd : Bool) {z z₀ : ℂ} (hz : 0 < z.re) (hz₀ : 0 ≤ z₀.re) :
    AnalyticAt ℂ (fun w => parityRealPlaceRelative odd w z₀) z := by
  cases odd
  · simp only [parityRealPlaceRelative_even]
    exact (realPlaceRelative_differentiableOn hz₀).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re) z hz
  · simp only [parityRealPlaceRelative_odd]
    have hp : 0 ≤ (z₀+1).re := by simp; linarith
    have hq : 0 < (z+1).re := by simp; linarith
    have hA := (realPlaceRelative_differentiableOn hp).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re) (z+1) hq
    exact hA.comp (f := fun w : ℂ => w+1) (x := z) (analyticAt_id.add analyticAt_const)

theorem dirichlet_zero_free_from_euler_residual (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1/2) {z₀ : ℂ} (hz₀ : 1/2 < z₀.re)
    (hres : ∀ z : ℂ, 1/2 < z.re →
      Tendsto (fun n => dirichletRestrictedResidual χ a n z z₀) atTop (𝓝 0))
    {s : ℂ} (hs : a+1/2 < s.re) : LFunction χ s ≠ 0 := by
  let xi := fun r : DirichletStripZero χ a => r.val.val-(1/2:ℂ)
  let mult := fun r : DirichletStripZero χ a => analyticOrderNatAt (LFunction χ) r.val.val
  let S (z : ℂ) := ∑' r, (mult r : ℂ)*relative z z₀ (xi r)
  let odd := if χ.Even then false else true
  let A (z : ℂ) := parityRealPlaceRelative odd z z₀
  let U := {t : ℂ | a+1/2 < t.re}
  let g (t : ℂ) := logDeriv (LFunction χ) (z₀+1/2) + A (t-1/2) + S (t-1/2)
  obtain ⟨C,hC,hcount⟩ := dirichlet_positive_strip_count χ hχ
  let H (T : ℝ) := C*(max T 1+2)*Real.log (max T 1+2)
  have hc (T : ℝ) (u : Finset (DirichletStripZero χ a))
      (hu : ∀ r ∈ u, |(xi r).im| ≤ T) : (∑ r ∈ u, (mult r : ℝ)) ≤ H T := by
    let e : DirichletStripZero χ a ↪ DirichletNontrivialZero χ := ⟨Subtype.val,Subtype.val_injective⟩
    have hh := hcount (max T 1) (u.map e) (le_max_right _ _) (by
      intro r hr
      obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hr
      simpa [e, xi, Complex.sub_im, Complex.div_im] using (hu q hq).trans (le_max_left T 1))
    simpa only [Finset.sum_map, e, Function.Embedding.coeFn_mk, mult, H] using hh
  have hgrowth (T : ℝ) (hT : 1 ≤ T) : H T ≤ C*(T+2)*Real.log (T+2) := by simp [H,max_eq_left hT]
  have hre (t : ℂ) : (t-(1/2:ℂ)).re = t.re-1/2 := by norm_num [Complex.sub_re,Complex.div_re]
  have hstrip (r : DirichletStripZero χ a) : |(xi r).re| ≤ a := by
    change |(r.val.val-(1/2:ℂ)).re| ≤ a
    rw [hre]
    exact r.property
  have hS := relative_spectral_analytic xi mult (8*C*Real.log 2)
    (fun j u hu => (hc _ u (fun i hi => (hu i hi).le)).trans
      (cumulative_count_dyadic H C hC hgrowth j)) ha hstrip (ha₁.trans hz₀)
  have hg : AnalyticOnNhd ℂ g U := by
    intro t ht
    change a+1/2 < t.re at ht
    have ht' : a < (t-1/2).re := by rw [hre]; linarith
    have hlin : AnalyticAt ℂ (fun w : ℂ => w-1/2) t := analyticAt_id.sub analyticAt_const
    have hAz := parityRelative_analyticAt odd (ha.trans_lt ht') (by linarith : 0 ≤ z₀.re)
    exact (analyticAt_const.add (hAz.comp (f := fun w : ℂ => w-1/2) (x := t) hlin)).add
      ((hS (t-1/2) ht').comp (f := fun w : ℂ => w-1/2) (x := t) hlin)
  have heuler (t : ℂ) (ht : 1 < t.re) : g t = logDeriv (LFunction χ) t := by
    let z := t-(1/2:ℂ)
    have hz : 1/2 < z.re := by dsimp only [z]; rw [hre]; linarith
    have h₁ := dirichlet_compensated_spectral_limit χ hp hχ hz hz₀
    have h₂ := parity_realPlace_limit odd (by linarith : 0 ≤ z.re) (by linarith : 0 ≤ z₀.re)
    have h₃ := (weighted_spectral_sum_limit xi mult H C hC hc hgrowth ha hstrip z z₀
      (ha₁.trans hz) (ha₁.trans hz₀)).2.2
    have hlim : Tendsto (fun n => dirichletRestrictedResidual χ a n z z₀) atTop
        (𝓝 ((-dirichletSpectralRelative χ z z₀ - A z) + A z + S z)) := (h₁.add h₂).add h₃
    have hzero := tendsto_nhds_unique hlim (hres z hz)
    have hE := dirichlet_euler_balance χ hp hχ hz hz₀
    have he : z+(1/2:ℂ) = t := by dsimp [z]; ring
    rw [he] at hE
    change logDeriv (LFunction χ) (z₀+1/2) - logDeriv (LFunction χ) t + A z =
      -dirichletSpectralRelative χ z z₀ at hE
    change logDeriv (LFunction χ) (z₀+1/2) + A z + S z = _
    linear_combination hE + hzero
  have hne (t : ℂ) (ht : 1 < t.re) : LFunction χ t ≠ 0 := by
    rw [LFunction_eq_LSeries χ ht]
    exact LSeries_ne_zero_of_one_lt_re χ ht
  have hbase : (2:ℂ) ∈ U := by change a+1/2 < (2:ℂ).re; norm_num; linarith
  have hagree : deriv (LFunction χ) =ᶠ[𝓝 (2:ℂ)] fun t => g t * LFunction χ t := by
    have hnear : {t : ℂ | 1 < t.re} ∈ 𝓝 (2:ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnear] with t ht
    rw [heuler t ht, logDeriv_apply, div_mul_cancel₀ _ (hne t ht)]
  exact no_zero_of_logDerivative_extension
    (isOpen_lt continuous_const Complex.continuous_re) (convex_halfSpace_re_gt (a+1/2)).isPreconnected
    hbase (fun t _ => (differentiable_LFunction hχ).analyticAt t) hg (hne 2 (by norm_num))
    hagree s hs

#print axioms dirichlet_zero_free_from_euler_residual
end RHConnections.DirichletZeroSet
