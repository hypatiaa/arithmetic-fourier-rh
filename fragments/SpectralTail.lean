import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace RHConnections.SpectralTail

def dyadicWeight (j : ℕ) : ℝ := ((j : ℝ)+1) * (1/2 : ℝ)^j

theorem dyadic_summable : Summable dyadicWeight := by
  have hn := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
    (r := (1/2 : ℝ)) (by norm_num)
  have hg := summable_geometric_of_norm_lt_one (x := (1/2 : ℝ)) (by norm_num)
  convert hn.add hg using 1
  ext j
  simp [dyadicWeight, add_mul]

theorem shell_norm_summable (shell : ℕ → ℂ) (C : ℝ)
    (hbound : ∀ j, ‖shell j‖ ≤ C * dyadicWeight j) :
    Summable (fun j => ‖shell j‖) := by
  exact (dyadic_summable.mul_left C).of_nonneg_of_le
    (fun j => norm_nonneg _) hbound

theorem shells_summable (shell : ℕ → ℂ) (C : ℝ)
    (hbound : ∀ j, ‖shell j‖ ≤ C * dyadicWeight j) : Summable shell :=
  (shell_norm_summable shell C hbound).of_norm

theorem approximation_limit {F : ℕ → ℕ → ℂ} {g : ℕ → ℂ} (C : ℝ)
    (hpoint : ∀ j, Filter.Tendsto (fun n => F n j) Filter.atTop (nhds (g j)))
    (hbound : ∀ n j, ‖F n j‖ ≤ C * dyadicWeight j) :
    Filter.Tendsto (fun n => ∑' j, F n j) Filter.atTop (nhds (∑' j, g j)) := by
  exact tendsto_tsum_of_dominated_convergence (dyadic_summable.mul_left C)
    hpoint (Filter.Eventually.of_forall hbound)

theorem individual_spectral_summable {ι : Type*} (multiplicity : ι → ℕ)
    (g : ι → ℂ) (bound : ι → ℝ) (hs : Summable bound)
    (hbound : ∀ i, ‖(multiplicity i : ℂ)*g i‖ ≤ bound i) :
    Summable (fun i => (multiplicity i : ℂ)*g i) := by
  have hn : Summable (fun i => ‖(multiplicity i : ℂ)*g i‖) :=
    hs.of_nonneg_of_le (fun i => norm_nonneg _) hbound
  exact hn.of_norm

theorem individual_spectral_limit {ι : Type*} (multiplicity : ι → ℕ)
    {F : ℕ → ι → ℂ} {g : ι → ℂ} (bound : ι → ℝ) (hs : Summable bound)
    (hpoint : ∀ i, Filter.Tendsto (fun n => F n i) Filter.atTop (nhds (g i)))
    (hbound : ∀ n i, ‖(multiplicity i : ℂ)*F n i‖ ≤ bound i) :
    Filter.Tendsto (fun n => ∑' i, (multiplicity i : ℂ)*F n i) Filter.atTop
      (nhds (∑' i, (multiplicity i : ℂ)*g i)) := by
  exact tendsto_tsum_of_dominated_convergence hs
    (fun i => tendsto_const_nhds.mul (hpoint i)) (Filter.Eventually.of_forall hbound)

theorem arbitrarily_narrow_strip {x : ℝ}
    (h : ∀ a : ℝ, 0 < a → |x| ≤ a) : x = 0 := by
  have hn := abs_nonneg x
  by_contra hx
  have hp : 0 < |x| := abs_pos.mpr hx
  have hh := h (|x|/2) (by linarith)
  linarith

theorem cofinal_narrow_strip {x : ℝ}
    (h : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ a : ℝ, 0 < a ∧ a < epsilon ∧ |x| ≤ a) : x = 0 := by
  apply arbitrarily_narrow_strip
  intro epsilon hepsilon
  obtain ⟨a, ha, he, hx⟩ := h epsilon hepsilon
  exact hx.trans he.le

#print axioms dyadic_summable
#print axioms shell_norm_summable
#print axioms shells_summable
#print axioms approximation_limit
#print axioms individual_spectral_summable
#print axioms individual_spectral_limit
#print axioms arbitrarily_narrow_strip
#print axioms cofinal_narrow_strip
end RHConnections.SpectralTail
