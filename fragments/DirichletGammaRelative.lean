import Verified
import Mathlib.NumberTheory.LSeries.DirichletContinuation

noncomputable section
open MeasureTheory Filter DirichletCharacter
open scoped Topology
namespace RHConnections.PoleCompensation
open ArchimedeanLimit RelativeResolvent

def parityRealPlaceRelative (odd : Bool) (z z₀ : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), (parityRealPlaceKernel odd x : ℂ) * logTest z z₀ x

theorem parityRealPlaceRelative_even (z z₀ : ℂ) :
    parityRealPlaceRelative false z z₀ = realPlaceRelative z z₀ := by
  simp only [parityRealPlaceRelative, parityRealPlaceKernel_even, realPlaceRelative]

theorem parityRealPlaceRelative_odd (z z₀ : ℂ) :
    parityRealPlaceRelative true z z₀ = realPlaceRelative (z+1) (z₀+1) := by
  unfold parityRealPlaceRelative realPlaceRelative
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change 0 < x at hx
  simp only [parityRealPlaceKernel_odd, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_neg, logTest, if_pos hx]
  have he (w : ℂ) : Complex.exp (-(w+1)*(x:ℂ)) =
      Complex.exp (-(x:ℂ)) * Complex.exp (-w*(x:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1 <;> ring
  rw [he z, he z₀]
  ring

private theorem differentiableAt_gammaReal_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hn (m : ℕ) : s/2 ≠ -(m:ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.div_re, Complex.neg_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hlin : DifferentiableAt ℂ (fun w : ℂ => w/2) s := by fun_prop
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold Complex.Gammaℝ
  simp only [Complex.cpow_def_of_ne_zero hpi]
  exact (show DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Complex.log (Real.pi : ℂ)*(-w/2))) s
    by fun_prop).mul ((Complex.differentiableAt_Gamma _ hn).comp s hlin)

private theorem shifted_gammaReal_logDeriv {s : ℂ} (hs : 0 < (s+1).re) :
    logDeriv (fun w => Complex.Gammaℝ (w+1)) s = logDeriv Complex.Gammaℝ (s+1) := by
  have hlin : HasDerivAt (fun w : ℂ => w+1) 1 s := by
    simpa only [id_eq] using (hasDerivAt_id s).add_const (1:ℂ)
  have h := (differentiableAt_gammaReal_pos hs).hasDerivAt.comp s hlin
  change deriv (Complex.Gammaℝ ∘ fun w : ℂ => w+1) s / Complex.Gammaℝ (s+1) = _
  rw [h.deriv, logDeriv_apply]
  simp

local instance (N : ℕ) (χ : DirichletCharacter ℂ N) : Decidable χ.Even := Classical.propDecidable _

theorem parityRealPlaceRelative_eq_gammaFactor {N : ℕ} (χ : DirichletCharacter ℂ N)
    {z z₀ : ℂ} (hz : 0 ≤ z.re) (hz₀ : 0 ≤ z₀.re) :
    parityRealPlaceRelative (if χ.Even then false else true) z z₀ =
      logDeriv (gammaFactor χ) (z₀+1/2) - logDeriv (gammaFactor χ) (z+1/2) := by
  classical
  by_cases hχ : χ.Even
  · have hfun : gammaFactor χ = Complex.Gammaℝ := funext hχ.gammaFactor_def
    simpa [hχ, parityRealPlaceRelative_even, hfun] using realPlaceRelative_eq_gammaDifference hz hz₀
  · have hfun : gammaFactor χ = fun w => Complex.Gammaℝ (w+1) :=
      funext (χ.even_or_odd.resolve_left hχ).gammaFactor_def
    have hp (w : ℂ) (hw : 0 ≤ w.re) : 0 < (w+1/2+1).re := by
      norm_num [Complex.add_re, Complex.div_re]; linarith
    simp only [if_neg hχ, parityRealPlaceRelative_odd, hfun,
      shifted_gammaReal_logDeriv (hp z₀ hz₀), shifted_gammaReal_logDeriv (hp z hz)]
    have hs (w : ℂ) (hw : 0 ≤ w.re) : 0 ≤ (w+1).re := by simp; linarith
    simpa only [show z+1+1/2 = z+1/2+1 by ring, show z₀+1+1/2 = z₀+1/2+1 by ring] using
      realPlaceRelative_eq_gammaDifference (hs z hz) (hs z₀ hz₀)

theorem completedDirichlet_logDeriv_euler {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (completedLFunction χ) s =
      logDeriv (LFunction χ) s + logDeriv (gammaFactor χ) s := by
  classical
  have hgf (w : ℂ) (hw : 0 < w.re) :
      gammaFactor χ w ≠ 0 ∧ DifferentiableAt ℂ (gammaFactor χ) w := by
    rcases χ.even_or_odd with he | ho
    · rw [show gammaFactor χ = Complex.Gammaℝ from funext he.gammaFactor_def]
      exact ⟨Complex.Gammaℝ_ne_zero_of_re_pos hw, differentiableAt_gammaReal_pos hw⟩
    · rw [show gammaFactor χ = fun u => Complex.Gammaℝ (u+1) from funext ho.gammaFactor_def]
      have hp : 0 < (w+1).re := by simp; linarith
      exact ⟨Complex.Gammaℝ_ne_zero_of_re_pos hp,
        by
          have hlin : DifferentiableAt ℂ (fun u : ℂ => u+1) w := by fun_prop
          simpa only [Function.comp_def] using (differentiableAt_gammaReal_pos hp).comp w hlin⟩
  have heq : completedLFunction χ =ᶠ[𝓝 s] (LFunction χ * gammaFactor χ) := by
    filter_upwards [((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)] with w hw
    have hpos : 0 < w.re := by change 1 < w.re at hw; linarith
    have hn : w ≠ 0 := fun h => by simpa [h] using hpos
    exact ((eq_div_iff (hgf w hpos).1).mp (LFunction_eq_completed_div_gammaFactor χ w (.inl hn))).symm
  have hL0 : LFunction χ s ≠ 0 := by
    rw [LFunction_eq_LSeries χ hs]
    exact LSeries_ne_zero_of_one_lt_re χ hs
  have hs1 : s ≠ 1 := fun h => by simpa [h] using hs
  have hpos : 0 < s.re := by linarith
  calc
    _ = logDeriv (LFunction χ * gammaFactor χ) s := by
      simp only [logDeriv_apply, heq.deriv_eq, heq.self_of_nhds]
    _ = _ := logDeriv_mul s hL0 (hgf s hpos).1 (differentiableAt_LFunction χ s (.inl hs1))
      (hgf s hpos).2

end RHConnections.PoleCompensation
