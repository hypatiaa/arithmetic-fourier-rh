import AstraLocalModeContrast

open Filter Set
open scoped Topology
noncomputable section
namespace RHConnections.LocalModeContrast

def unitRotation (w : ℂ) : ℂ := (‖w‖ : ℂ)/w

theorem unitRotation_norm {w : ℂ} (hw : w ≠ 0) : ‖unitRotation w‖ = 1 := by
  simp [unitRotation,Complex.norm_real,hw]

theorem unit_rotated_contrast {g : ℝ → ℂ} (hg : ContDiffAt ℝ 1 g 1) (hne : deriv g 1 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ {a b c e d : ℝ},
      a ∈ Ioo (1-r) (1+r) → b ∈ Ioo (1-r) (1+r) →
      c ∈ Ioo (1-r) (1+r) → e ∈ Ioo (1-r) (1+r) →
      0 < d → d ≤ c-a → d ≤ e-b →
      d*‖deriv g 1‖/2 ≤
        (unitRotation (deriv g 1)*(normalizedMean g c e - normalizedMean g a b)).re := by
  obtain ⟨L,U,hU,hL,hgL⟩ := contDiffAt_one_iff.mp hg
  let v (y : ℝ) := L y 1
  have hv : ContinuousAt v 1 := (hL.continuousAt hU).clm_apply continuousAt_const
  have hd : ∀ᶠ y in 𝓝 (1:ℝ), HasDerivAt g (v y) y := by
    filter_upwards [hU] with y hy
    exact (hgL y hy).hasDerivAt
  have h1 : deriv g 1 = v 1 := hd.self_of_nhds.deriv
  obtain ⟨r,hr,h⟩ := local_mean_contrast hd hv (h1 ▸ hne)
  refine ⟨r,hr,?_⟩
  intro a b c e d ha hb hc he hd0 hca heb
  have hbound := h ha hb hc he hd0 hca heb
  rw [← h1] at hbound
  let w := deriv g 1
  let D := normalizedMean g c e - normalizedMean g a b
  change d/2 ≤ (D/w).re at hbound
  change d*‖w‖/2 ≤ (unitRotation w*D).re
  have hu : unitRotation w*D = (‖w‖ : ℂ)*(D/w) := by unfold unitRotation; ring
  simp only [hu,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  linarith [mul_le_mul_of_nonneg_left hbound (norm_nonneg w)]

#print axioms unitRotation_norm
#print axioms unit_rotated_contrast
end RHConnections.LocalModeContrast
