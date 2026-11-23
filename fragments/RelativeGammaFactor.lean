import Verified

open Filter
namespace RHConnections.PoleCompensation
open GammaSeqUniform GammaSeqLogDerivative

theorem gammaSeq_logDerivative_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => logDeriv (fun u => Complex.GammaSeq u n) s) atTop
      (nhds (logDeriv Complex.Gamma s)) := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hG : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (fun s => Complex.GammaSeq s n) U :=
    (eventually_ne_atTop 0).mono (fun _ hn => gammaSeq_differentiableOn hn)
  have hsU : s ∈ U := hs
  have hno (m : ℕ) : s ≠ -(m : ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.neg_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) m]
  exact ((gammaSeq_tendstoLocallyUniformlyOn.deriv hG hU).tendsto_at hsU).div
    (gammaSeq_tendstoLocallyUniformlyOn.tendsto_at hsU) (Complex.Gamma_ne_zero hno)

theorem gammaReal_logDerivative {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s =
      -(1/2 : ℂ) * Complex.log (Real.pi : ℂ) + (1/2 : ℂ) * logDeriv Complex.Gamma (s/2) := by
  let f := fun s : ℂ => (Real.pi : ℂ)^(-s/2)
  let g := fun s : ℂ => Complex.Gamma (s/2)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hlin : HasDerivAt (fun t : ℂ => t/2) (1/2) s := by
    simpa only [id_eq] using (hasDerivAt_id s).div_const (2:ℂ)
  have hlin' : HasDerivAt (fun t : ℂ => -t/2) (-1/2) s := by
    convert (hasDerivAt_id s).neg.div_const (2:ℂ) using 1 <;> rfl
  have hd := hlin'.const_cpow (Or.inl hp)
  have hn (m : ℕ) : s/2 ≠ -(m : ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.div_re, Complex.neg_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hf0 : f s ≠ 0 := by simp [f, Complex.cpow_def_of_ne_zero hp]
  have hg0 : g s ≠ 0 := Complex.Gamma_ne_zero hn
  have hgD : DifferentiableAt ℂ g s := (Complex.differentiableAt_Gamma _ hn).comp s hlin.differentiableAt
  have hfD : DifferentiableAt ℂ f s := hd.differentiableAt
  change logDeriv (f*g) s = _
  rw [logDeriv_mul s hf0 hg0 hfD hgD, logDeriv_apply f, hd.deriv]
  have hh : logDeriv g s = (1/2 : ℂ)*logDeriv Complex.Gamma (s/2) :=
    by
      have hdg := (Complex.differentiableAt_Gamma _ hn).hasDerivAt.comp s hlin
      change deriv (Complex.Gamma ∘ fun t : ℂ => t/2) s / Complex.Gamma (s/2) = _
      rw [hdg.deriv, logDeriv_apply]
      ring
  rw [hh]
  dsimp [f] at hf0 ⊢
  field_simp
  <;> ring

theorem realPlaceRelative_eq_gammaDifference {z z₀ : ℂ} (hz : 0 ≤ z.re) (hz₀ : 0 ≤ z₀.re) :
    realPlaceRelative z z₀ =
      logDeriv Complex.Gammaℝ (z₀+1/2) - logDeriv Complex.Gammaℝ (z+1/2) := by
  let s := z+1/2
  let s₀ := z₀+1/2
  have hs : 0 < s.re := by norm_num [s, Complex.add_re, Complex.div_re]; linarith
  have hs₀ : 0 < s₀.re := by norm_num [s₀, Complex.add_re, Complex.div_re]; linarith
  have htwo (w : ℂ) : (w/2).re = w.re/2 := by norm_num [Complex.div_re]
  have hsh : 0 < (s/2).re := by rw [htwo]; positivity
  have hsh₀ : 0 < (s₀/2).re := by rw [htwo]; positivity
  have hG := (gammaSeq_logDerivative_tendsto hsh₀).sub (gammaSeq_logDerivative_tendsto hsh)
  have hG' := tendsto_const_nhds.mul hG (a := (1/2:ℂ))
  have h₁ : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n+1),
       ((z+1/2+2*k)⁻¹ - (z₀+1/2+2*k)⁻¹)) atTop (nhds (realPlaceRelative z z₀)) :=
    (realPlaceRelative_hasSum hz hz₀).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h₂ := hG'.congr' (f₂ := fun n : ℕ => ∑ k ∈ Finset.range (n+1),
       ((z+1/2+2*k)⁻¹ - (z₀+1/2+2*k)⁻¹)) (by
    filter_upwards [eventually_ne_atTop 0] with n hn
    try dsimp only
    rw [gammaSeq_logDeriv hn hsh₀, gammaSeq_logDeriv hn hsh]
    rw [show Complex.log (n : ℂ) - (∑ k ∈ Finset.range (n+1), (s₀/2+k)⁻¹) -
      (Complex.log (n : ℂ) - (∑ k ∈ Finset.range (n+1), (s/2+k)⁻¹)) =
      (∑ k ∈ Finset.range (n+1), (s/2+k)⁻¹) -
      (∑ k ∈ Finset.range (n+1), (s₀/2+k)⁻¹) by ring,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have he (w : ℂ) : ((w/2+(k:ℂ))⁻¹) = 2*(w+2*k)⁻¹ := by
      rw [show w/2+(k:ℂ) = (w+2*k)/2 by ring, inv_div, div_eq_mul_inv]
    rw [he s, he s₀]
    dsimp [s,s₀]
    ring)
  change _ = logDeriv Complex.Gammaℝ s₀ - logDeriv Complex.Gammaℝ s
  rw [gammaReal_logDerivative hs₀, gammaReal_logDerivative hs]
  have hh := tendsto_nhds_unique h₁ h₂
  rw [hh]
  ring

end RHConnections.PoleCompensation
