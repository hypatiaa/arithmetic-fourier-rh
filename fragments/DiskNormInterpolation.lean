import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Tactic

noncomputable section
namespace RHConnections.DiskNormInterpolation
open Complex Complex.HadamardThreeLines Metric Set

theorem norm_le_three_circle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) {c u : ℂ} {r₁ r r₂ R M₁ M₂ : ℝ}
    (hr₁ : 0 < r₁) (h₁ : r₁ < r) (h₂ : r < r₂) (hR : r₂ < R)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hinner : ∀ w : ℂ, ‖w‖ = r₁ → ‖f (c+w)‖ ≤ M₁)
    (houter : ∀ w : ℂ, ‖w‖ = r₂ → ‖f (c+w)‖ ≤ M₂) (hu : ‖u‖ = r) :
    let θ := (Real.log r - Real.log r₁) / (Real.log r₂ - Real.log r₁)
    ‖f (c+u)‖ ≤ M₁^(1-θ) * M₂^θ := by
  dsimp only
  have hr : 0 < r := hr₁.trans h₁
  have hr₂ : 0 < r₂ := hr.trans h₂
  have hlog₁ := Real.log_lt_log hr₁ h₁
  have hlog₂ := Real.log_lt_log hr h₂
  have hu₀ : u ≠ 0 := norm_pos_iff.mp (by rwa [hu])
  let V : Set ℂ := {w | w.re ≤ Real.log r₂}
  let g := fun w : ℂ => f (c + Complex.exp w)
  have hVC : IsClosed V := isClosed_le Complex.continuous_re continuous_const
  have hball (w : ℂ) (hw : w ∈ V) : c + Complex.exp w ∈ closedBall c r₂ := by
    have h := (Real.exp_le_exp.mpr hw).trans_eq (Real.exp_log hr₂)
    simpa [Metric.mem_closedBall, dist_eq_norm, Complex.norm_exp] using h
  have hsub : closedBall c r₂ ⊆ ball c R := closedBall_subset_ball hR
  have hd (w : ℂ) (hw : w ∈ V) : DifferentiableAt ℂ g w := by
    have hfc := hf.differentiableAt (isOpen_ball.mem_nhds (hsub (hball w hw)))
    simpa only [g, Function.comp_def] using hfc.comp w
      (show DifferentiableAt ℂ (fun z : ℂ => c + Complex.exp z) w by fun_prop)
  have hs : verticalStrip (Real.log r₁) (Real.log r₂) ⊆ V := fun _ hw => hw.2.le
  have hg : DiffContOnCl ℂ g (verticalStrip (Real.log r₁) (Real.log r₂)) :=
    ⟨fun w hw => (hd w (hs hw)).differentiableWithinAt,
     fun w hw => (hd w (closure_minimal hs hVC hw)).continuousAt.continuousWithinAt⟩
  have hB : BddAbove ((norm ∘ g) '' verticalClosedStrip (Real.log r₁) (Real.log r₂)) := by
    obtain ⟨B,hB⟩ := (isCompact_closedBall c r₂).bddAbove_image
      (hf.continuousOn.norm.mono hsub)
    refine ⟨B, ?_⟩
    rintro _ ⟨w,hw,rfl⟩
    exact hB (Set.mem_image_of_mem _ (hball w hw.2))
  have hre : (Complex.log u).re = Real.log r := by rw [Complex.log_re, hu]
  have hmem : Complex.log u ∈ verticalClosedStrip (Real.log r₁) (Real.log r₂) := by
    change Real.log r₁ ≤ (Complex.log u).re ∧ (Complex.log u).re ≤ Real.log r₂
    rw [hre]
    exact ⟨hlog₁.le,hlog₂.le⟩
  have h := norm_le_interp_of_mem_verticalClosedStrip' (hlog₁.trans hlog₂) hmem hg hB
    (a := M₁) (b := M₂) (fun w hw => hinner (Complex.exp w) (by
      rw [Complex.norm_exp, (show w.re = Real.log r₁ from hw), Real.exp_log hr₁]))
    (fun w hw => houter (Complex.exp w) (by
      rw [Complex.norm_exp, (show w.re = Real.log r₂ from hw), Real.exp_log hr₂]))
  simpa only [g, hre, Complex.exp_log hu₀] using h

end RHConnections.DiskNormInterpolation
