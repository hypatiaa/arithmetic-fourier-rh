import Verified

open Filter
open scoped Topology Classical
noncomputable section
namespace RHConnections.DirichletZeroSet
open DirichletCharacter SpectralTail EntireCanonicalProduct RelativeResolvent
open PoleCompensation DirichletGeometricLimit Mollifier
open scoped LSeries.notation

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

def dirichletSpectralRelative (z z₀ : ℂ) : ℂ :=
  ∑' r : DirichletNontrivialZero χ, (analyticOrderNatAt (LFunction χ) r.val : ℂ) *
    relative z z₀ (r.val-(1/2:ℂ))

theorem normalized_dirichlet_logDeriv_euler (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (normalizedCompletedDirichlet χ) s =
      logDeriv (LFunction χ) s + logDeriv (gammaFactor χ) s := by
  have hC : (completedLFunction χ 0)⁻¹ ≠ 0 :=
    inv_ne_zero (completed_dirichlet_zero_value_nonzero χ hp hχ)
  have h := completed_dirichlet_nonzero_of_one_le χ hχ hs.le
  change logDeriv ((fun _ : ℂ => (completedLFunction χ 0)⁻¹) * completedLFunction χ) s = _
  rw [logDeriv_mul s hC h (differentiableAt_const _)
    (differentiable_completedLFunction hχ s), logDeriv_const]
  change 0 + logDeriv (completedLFunction χ) s = _
  rw [zero_add, completedDirichlet_logDeriv_euler χ hs]

theorem dirichlet_relative_match (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    {z z₀ : ℂ} (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    dirichletSpectralRelative χ z z₀ =
      logDeriv (normalizedCompletedDirichlet χ) (z+1/2) -
      logDeriv (normalizedCompletedDirichlet χ) (z₀+1/2) := by
  let D := dirichletProductData χ hp hχ
  let e := normalized_dirichlet_zero_equiv χ hp hχ
  have hn (w : ℂ) (hw : 1/2 < w.re) (r : D.Zero) : w+1/2 ≠ r.val := by
    have hR := (e r).property.1.2
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.div_re] at hr
    exact (not_le_of_gt hw) (by change r.val.re < 1 at hR; linarith)
  have hSum := D.relative_logDerivative (dirichlet_hadamard χ hp hχ) (hn z hz) (hn z₀ hz₀)
  change _ = logDeriv D.F (z+1/2) - logDeriv D.F (z₀+1/2)
  rw [← hSum.tsum_eq, hSum.summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  unfold dirichletSpectralRelative
  rw [← e.tsum_eq]
  apply tsum_congr
  intro r
  have hre (v : ℂ) : (v+(1/2:ℂ))-r.val = v-(r.val-1/2) := by ring
  have hr : 0 < r.val.re := (e r).property.1.1
  have he : analyticOrderNatAt D.F r.val = analyticOrderNatAt (LFunction χ) r.val := by
    unfold analyticOrderNatAt
    exact congrArg ENat.toNat (normalized_completed_order χ hp hχ hr)
  change (analyticOrderNatAt (LFunction χ) r.val : ℂ)*relative z z₀ (r.val-1/2) = _
  simp only [relative, hre, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, he]

theorem dirichlet_euler_balance (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    {z z₀ : ℂ} (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    logDeriv (LFunction χ) (z₀+1/2) - logDeriv (LFunction χ) (z+1/2) +
      parityRealPlaceRelative (if χ.Even then false else true) z z₀ =
      -(dirichletSpectralRelative χ z z₀) := by
  have hs (w : ℂ) (hw : 1/2 < w.re) : 1 < (w+1/2).re := by
    norm_num [Complex.add_re, Complex.div_re]
    linarith
  rw [dirichlet_relative_match χ hp hχ hz hz₀, normalized_dirichlet_logDeriv_euler χ hp hχ (hs z hz),
    normalized_dirichlet_logDeriv_euler χ hp hχ (hs z₀ hz₀),
    parityRealPlaceRelative_eq_gammaFactor χ (by linarith) (by linarith)]
  ring

theorem dirichlet_compensated_spectral_limit (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    {z z₀ : ℂ} (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    Tendsto (fun n => ∑' m, DirichletGeometricLimit.halfWeight χ m * fullCandidate n z z₀ (Real.log m))
      atTop (𝓝 (-dirichletSpectralRelative χ z z₀ -
        parityRealPlaceRelative (if χ.Even then false else true) z z₀)) := by
  have h := (twisted_vonMangoldt_candidate_limit χ z z₀ hz hz₀).2
  have hs (w : ℂ) (hw : 1/2 < w.re) : 1 < (w+1/2).re := by
    norm_num [Complex.add_re, Complex.div_re]
    linarith
  rw [← deriv_LFunction_eq_deriv_LSeries χ (hs z hz),
    ← deriv_LFunction_eq_deriv_LSeries χ (hs z₀ hz₀),
    ← LFunction_eq_LSeries χ (hs z hz), ← LFunction_eq_LSeries χ (hs z₀ hz₀)] at h
  have htarget := dirichlet_euler_balance χ hp hχ hz hz₀
  rw [show -dirichletSpectralRelative χ z z₀ -
    parityRealPlaceRelative (if χ.Even then false else true) z z₀ =
      -deriv (LFunction χ) (z+1/2)/LFunction χ (z+1/2) -
      (-deriv (LFunction χ) (z₀+1/2)/LFunction χ (z₀+1/2)) by
    rw [← htarget]
    simp only [logDeriv_apply]
    ring]
  exact h

end RHConnections.DirichletZeroSet
