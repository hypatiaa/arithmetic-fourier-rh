import Verified
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

open scoped ContDiff

noncomputable section
namespace RHConnections.Mollifier

def cutoffScaled (n : ℕ) (x : ℝ) : ℝ := cutoff 0 (x / ((n : ℝ) + 1))

theorem cutoffScaled_eq (n : ℕ) : cutoffScaled n = (cutoff n : ℝ → ℝ) := by
  have hratio (k : ℕ) : (cutoff k).rOut / (cutoff k).rIn = 2 := by
    change 2 * ((k : ℝ) + 1) / ((k : ℝ) + 1) = 2
    exact mul_div_cancel_right₀ 2 (by positivity)
  funext x
  unfold cutoffScaled
  rw [(cutoff 0).apply, (cutoff n).apply, hratio 0, hratio n]
  simp [cutoff, smul_eq_mul, div_eq_inv_mul]

theorem cutoff_iteratedDeriv_scale (j n : ℕ) (x : ℝ) :
    iteratedDeriv j (cutoff n) x =
      iteratedDeriv j (cutoff 0) (x / ((n : ℝ) + 1)) / (((n : ℝ) + 1) ^ j) := by
  have hscale := iteratedDeriv_comp_const_mul
    ((cutoff 0).contDiff : ContDiff ℝ j (cutoff 0 : ℝ → ℝ)) (((n : ℝ) + 1)⁻¹)
  have hfun : cutoffScaled n = (fun y : ℝ => cutoff 0 (((n : ℝ) + 1)⁻¹ * y)) := by
    funext y
    change cutoff 0 (y / ((n : ℝ) + 1)) = cutoff 0 (((n : ℝ) + 1)⁻¹ * y)
    rw [div_eq_inv_mul]
  rw [← cutoffScaled_eq n, hfun]
  simpa only [div_eq_inv_mul, inv_pow] using congrFun hscale x

theorem cutoff_deriv_scale (n : ℕ) (x : ℝ) :
    deriv (cutoff n) x = deriv (cutoff 0) (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
  simpa only [iteratedDeriv_one, pow_one] using cutoff_iteratedDeriv_scale 1 n x

theorem cutoff_deriv_deriv_scale (n : ℕ) (x : ℝ) :
    deriv (deriv (cutoff n)) x =
      deriv (deriv (cutoff 0)) (x / ((n : ℝ) + 1)) / (((n : ℝ) + 1) ^ 2) := by
  simpa only [iteratedDeriv_succ (n := 1), iteratedDeriv_one] using
    cutoff_iteratedDeriv_scale (1 + 1) n x

theorem cutoff_iteratedDeriv_uniform (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ),
      ‖iteratedDeriv j (cutoff n) x‖ ≤ C / (((n : ℝ) + 1) ^ j) ∧
      ‖iteratedDeriv j (cutoff n) x‖ ≤ C := by
  have hcompact : HasCompactSupport (iteratedDeriv j (cutoff 0 : ℝ → ℝ)) := by
    induction j with
    | zero => simpa only [iteratedDeriv_zero] using (cutoff 0).hasCompactSupport
    | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hs : ContDiff ℝ ∞ (cutoff 0 : ℝ → ℝ) := (cutoff 0).contDiff
  have hcont := hs.continuous_iteratedDeriv j (by simp)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcompact
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, hC₀, ?_⟩
  intro n x
  have hr : 1 ≤ ((n : ℝ) + 1) ^ j := by
    apply one_le_pow₀
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hr₀ : 0 ≤ ((n : ℝ) + 1) ^ j := zero_le_one.trans hr
  have hbound : ‖iteratedDeriv j (cutoff n) x‖ ≤ C / (((n : ℝ) + 1) ^ j) := by
    rw [cutoff_iteratedDeriv_scale, norm_div, Real.norm_of_nonneg hr₀]
    exact div_le_div_of_nonneg_right (hC _) hr₀
  exact ⟨hbound, hbound.trans (div_le_self hC₀ hr)⟩

#print axioms cutoffScaled_eq
#print axioms cutoff_iteratedDeriv_scale
#print axioms cutoff_deriv_scale
#print axioms cutoff_deriv_deriv_scale
#print axioms cutoff_iteratedDeriv_uniform

end RHConnections.Mollifier
