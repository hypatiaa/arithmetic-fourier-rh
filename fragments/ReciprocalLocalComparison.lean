import Verified
open Metric Set
noncomputable section
namespace RHConnections.ReciprocalLocalComparison
open ZetaDiskLog
private theorem borel_on_centered_sphere {G : ℂ → ℂ} {c : ℂ} {R r M : ℝ}
    (hR : 0 < R) (hr : r < R) (hM : 0 < M)
    (hG : AnalyticOnNhd ℂ G (ball c R))
    (hRe : ∀ z ∈ ball c R, (G z).re ≤ M)
    {z : ℂ} (hz : z ∈ sphere c r) :
    ‖G z‖ ≤ 2*M*r/(R-r) + ‖G c‖*(R+r)/(R-r) := by
  let H := fun w => G (w+c)
  have hw (w : ℂ) (hw : w ∈ ball (0:ℂ) R) : w+c ∈ ball c R := by
    simpa [mem_ball, dist_eq_norm] using hw
  have hDiff : DifferentiableOn ℂ H (ball 0 R) := by
    intro w hw'
    have hD := (hG (w+c) (hw w hw')).differentiableAt
    exact (hD.comp w (differentiableAt_id.add_const c)).differentiableWithinAt
  have hmap : MapsTo H (ball 0 R) {x : ℂ | x.re ≤ M} := fun w hw' =>
    hRe _ (hw w hw')
  have hnr : ‖z-c‖ = r := by simpa [mem_sphere, dist_eq_norm] using hz
  have ht : z-c ∈ ball (0:ℂ) R := by simpa [mem_ball,dist_eq_norm,hnr] using hr
  have h := Complex.borelCaratheodory hM hDiff hmap hR ht
  simpa [H,hnr] using h

theorem reciprocal_le_exp_disk {f : ℂ → ℂ} {c z : ℂ} {r R U V : ℝ}
    (hR : 0 < R) (hr : r < R) (hs : z ∈ sphere c r)
    (hf : AnalyticOnNhd ℂ f (ball c R)) (hn : ∀ w ∈ ball c R, f w ≠ 0)
    (hu : ∀ w ∈ ball c R, ‖f w‖ ≤ Real.exp U)
    (hv : ‖(f c)⁻¹‖ ≤ Real.exp V) (hUV : 0 < U+V) :
    ‖(f z)⁻¹‖ ≤ Real.exp (V+2*(U+V)*r/(R-r)) := by
  obtain ⟨G,hG,_,hGe⟩ := analytic_log_on_ball hR hf hn
  have hc := hGe c (mem_ball_self hR)
  have hcv : -(G c).re ≤ V := by
    apply Real.exp_le_exp.mp
    simpa [← hc, norm_inv, Complex.norm_exp, Real.exp_neg] using hv
  let H := fun w => G w - G c
  have hH : AnalyticOnNhd ℂ H (ball c R) := fun w hw =>
    (hG w hw).sub analyticAt_const
  have hRe (w : ℂ) (hw : w ∈ ball c R) : (H w).re ≤ U+V := by
    have h : (G w).re ≤ U := Real.exp_le_exp.mp (by
      simpa [← hGe w hw, Complex.norm_exp] using hu w hw)
    change (G w).re - (G c).re ≤ U+V
    linarith
  have hBC := borel_on_centered_sphere hR hr hUV hH hRe hs
  have hBC' : ‖H z‖ ≤ 2*(U+V)*r/(R-r) := by simpa [H] using hBC
  have hlow : -(H z).re ≤ ‖H z‖ := by simpa using Complex.re_le_norm (-(H z))
  have hz : z ∈ ball c R := Metric.mem_ball.mpr ((Metric.mem_sphere.mp hs).trans_lt hr)
  rw [← hGe z hz, norm_inv, Complex.norm_exp, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  change -((G z).re - (G c).re) ≤ ‖H z‖ at hlow
  linarith
end RHConnections.ReciprocalLocalComparison
