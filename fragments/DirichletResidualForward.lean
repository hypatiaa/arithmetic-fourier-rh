import Verified

open MeasureTheory Filter
open scoped Topology Classical
namespace RHConnections.DirichletZeroSet
open DirichletCharacter PoleCompensation FourierDecay WeightedConvolution Mollifier

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

theorem dirichlet_residual_zero_of_containment (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    {a : ℝ} (hstrip : ∀ r : DirichletNontrivialZero χ, |r.val.re-1/2| ≤ a)
    (n : ℕ) (z z₀ : ℂ) : dirichletRestrictedResidual χ a n z z₀ = 0 := by
  let f := fullCandidate n z z₀
  have hf (x : ℝ) (hx : x ≤ 0) : f x = 0 :=
    fullCandidate_vanishes_left n z z₀ (hx.trans (epsilon_pos n).le)
  have h := dirichlet_explicit_formula_compact χ hp hχ f
    (fullCandidate_smooth n z z₀) (fullCandidate_compact n z z₀) (hf 0 le_rfl)
  let e : DirichletStripZero χ a ≃ DirichletNontrivialZero χ :=
    { toFun := Subtype.val
      invFun := fun r => ⟨r,hstrip r⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  let F (r : DirichletNontrivialZero χ) : ℂ :=
    (analyticOrderNatAt (LFunction χ) r.val : ℂ) *
      ∫ x in Set.Ioi (0:ℝ), Complex.exp ((r.val-(1/2:ℂ))*(x:ℂ))* f x
  have hs :
      (∑' r : DirichletStripZero χ a, (analyticOrderNatAt (LFunction χ) r.val.val : ℂ) *
        angularTransform (weighted (r.val.val-(1/2:ℂ)).re f) (r.val.val-(1/2:ℂ)).im) =
      ∑' r : DirichletNontrivialZero χ, F r := by
    rw [← e.tsum_eq]
    apply tsum_congr
    intro r
    rw [angular_weighted_eq_positive_laplace f _ hf]
    rfl
  change (∑' m : ℕ, DirichletGeometricLimit.halfWeight χ m * f (Real.log m)) +
    (∫ x in Set.Ioi (0:ℝ), (parityRealPlaceKernel (if χ.Even then false else true) x:ℂ)*f x) +
    (∑' r : DirichletStripZero χ a, (analyticOrderNatAt (LFunction χ) r.val.val : ℂ) *
      angularTransform (weighted (r.val.val-(1/2:ℂ)).re f) (r.val.val-(1/2:ℂ)).im) = 0
  rw [hs]
  change _ = -(∑' r : DirichletNontrivialZero χ, F r) at h
  rw [h]
  exact neg_add_cancel _

theorem dirichlet_residual_limit_of_containment (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    {a : ℝ} (hstrip : ∀ r : DirichletNontrivialZero χ, |r.val.re-1/2| ≤ a)
    (z z₀ : ℂ) :
    Tendsto (fun n : ℕ => dirichletRestrictedResidual χ a n z z₀) atTop (𝓝 0) := by
  simp_rw [dirichlet_residual_zero_of_containment χ hp hχ hstrip]
  exact tendsto_const_nhds

end RHConnections.DirichletZeroSet
