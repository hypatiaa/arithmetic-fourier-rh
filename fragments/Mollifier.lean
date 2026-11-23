import RelativeAnalytic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff
noncomputable section
namespace RHConnections.Mollifier
open RelativeResolvent

def epsilon (n : ℕ) : ℝ := 1 / ((n : ℝ)+1)

theorem epsilon_pos (n : ℕ) : 0 < epsilon n := by unfold epsilon; positivity

def bump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := epsilon n / 2
  rOut := epsilon n
  rIn_pos := by have := epsilon_pos n; positivity
  rIn_lt_rOut := by have := epsilon_pos n; linarith

theorem epsilon_tendsto : Tendsto epsilon atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem kernel_mass (n : ℕ) : (∫ x : ℝ, (bump n).normed volume x) = 1 :=
  (bump n).integral_normed

def smoothDelayed (n : ℕ) (z z₀ : ℂ) (x : ℝ) : ℂ :=
  ((bump n).normed volume ⋆[lsmul ℝ ℝ, volume] logTest z z₀) (x-2*epsilon n)

theorem smoothDelayed_smooth (n : ℕ) (z z₀ : ℂ) :
    ContDiff ℝ ∞ (smoothDelayed n z z₀) := by
  have hc : ContDiff ℝ ∞
      ((bump n).normed volume ⋆[lsmul ℝ ℝ, volume] logTest z z₀) := by
    exact (bump n).hasCompactSupport_normed.contDiff_convolution_left
      (L := lsmul ℝ ℝ) (bump n).contDiff_normed
      (logTest_continuous z z₀).locallyIntegrable
  exact hc.comp (contDiff_id.sub contDiff_const)

theorem smoothDelayed_limit (z z₀ : ℂ) (x : ℝ) :
    Tendsto (fun n => smoothDelayed n z z₀ x) atTop (nhds (logTest z z₀ x)) := by
  have hk : Tendsto (fun n => x-2*epsilon n) atTop (nhds x) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul epsilon_tendsto)
  exact ContDiffBump.convolution_tendsto_right (μ := volume) (φ := bump)
    epsilon_tendsto (Eventually.of_forall fun n =>
      (logTest_continuous z z₀).aestronglyMeasurable)
    (((logTest_continuous z z₀).tendsto x).comp tendsto_snd) hk

#print axioms epsilon_pos
#print axioms epsilon_tendsto
#print axioms kernel_mass
#print axioms smoothDelayed_smooth
#print axioms smoothDelayed_limit
end RHConnections.Mollifier
