import Verified
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.SummableUniformlyOn

noncomputable section
open Filter Set
namespace RHConnections.RelativeSpectrumAnalytic
open RelativeResolvent

def spectrum {ι : Type*} (ρ b : ι → ℂ) (z₀ z : ℂ) : ℂ :=
  ∑' i, b i * relative z z₀ (ρ i)

theorem relative_hasSum_locallyUniformlyOn {ι : Type*} (ρ b : ι → ℂ) (z₀ : ℂ)
    (hfinite : ∀ R : ℝ, Set.Finite {i | b i ≠ 0 ∧ ‖ρ i‖ ≤ R})
    (hs : Summable (fun i => ‖b i‖ / ‖ρ i‖^2)) {U : Set ℂ} (hU : IsOpen U) :
    HasSumLocallyUniformlyOn (fun i z => b i * relative z z₀ (ρ i)) (spectrum ρ b z₀) U := by
  classical
  apply hasSumLocallyUniformlyOn_of_forall_compact hU
  intro K _ hK
  obtain ⟨L, hL⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let T := 2 * max (max L ‖z₀‖) 1
  let C := 4 * (‖z₀‖ + max L 0)
  have hfar : ∀ᶠ i in cofinite, i ∉ {i | b i ≠ 0 ∧ ‖ρ i‖ ≤ T} :=
    (hfinite T).compl_mem_cofinite
  apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually (hs.mul_left C)
  filter_upwards [hfar] with i hi
  intro z hz
  by_cases hb : b i = 0
  · simp [hb]
  · have hρ : T < ‖ρ i‖ := lt_of_not_ge fun h => hi ⟨hb,h⟩
    have hzL : ‖z‖ ≤ L := hL (Set.mem_image_of_mem _ hz)
    have hl : L ≤ max (max L ‖z₀‖) 1 := (le_max_left _ _).trans (le_max_left _ _)
    have h₀ : ‖z₀‖ ≤ max (max L ‖z₀‖) 1 := (le_max_right _ _).trans (le_max_left _ _)
    have ht : 1 ≤ max (max L ‖z₀‖) 1 := le_max_right _ _
    dsimp only [T] at hρ
    have hrel := relative_tail_bound z z₀ (ρ i) (by linarith) (by linarith) (by linarith)
    have hC : 4*‖z₀-z‖ ≤ C := by
      dsimp [C]
      linarith [norm_sub_le z₀ z, le_max_left L (0:ℝ)]
    rw [norm_mul]
    calc
      _ ≤ ‖b i‖ * (C/‖ρ i‖^2) := mul_le_mul_of_nonneg_left
        (hrel.trans (div_le_div_of_nonneg_right hC (by positivity))) (norm_nonneg _)
      _ = _ := by ring

theorem spectrum_analyticOnNhd {ι : Type*} (ρ b : ι → ℂ) (z₀ : ℂ)
    (hfinite : ∀ R : ℝ, Set.Finite {i | b i ≠ 0 ∧ ‖ρ i‖ ≤ R})
    (hs : Summable (fun i => ‖b i‖ / ‖ρ i‖^2)) {U : Set ℂ} (hU : IsOpen U)
    (haway : ∀ z ∈ U, ∀ i, b i ≠ 0 → z ≠ ρ i) :
    AnalyticOnNhd ℂ (spectrum ρ b z₀) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  apply (relative_hasSum_locallyUniformlyOn ρ b z₀ hfinite hs hU).summableLocallyUniformlyOn.differentiableOn hU
  intro i z hz
  by_cases hb : b i = 0
  · simp [hb]
  · have hn : z - ρ i ≠ 0 := sub_ne_zero.mpr (haway z hz i hb)
    unfold relative
    fun_prop (disch := assumption)

end RHConnections.RelativeSpectrumAnalytic
