import ScaledCutoff
import WeightedRegularity
import AnalyticObligations
import ActualDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace RHConnections.Mollifier
open AnalyticObligations

theorem fullCandidate_leibniz_mass (n j : ℕ) (z z₀ : ℂ) (sigma : ℝ) (C M : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i)
    (hcut : ∀ i x, ‖iteratedDeriv i (cutoff n) x‖ ≤ C i)
    (hdel : ∀ k, k ≤ j →
      Integrable (fun x : ℝ => Real.exp (sigma*x)*‖iteratedDeriv k (smoothDelayed n z z₀) x‖) ∧
      weightedDerivativeMass sigma k (smoothDelayed n z z₀) ≤ M k) :
    weightedDerivativeMass sigma j (fullCandidate n z z₀) ≤
      ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * C i * M (j-i) := by
  let F (i : ℕ) (x : ℝ) := Real.exp (sigma*x)*‖iteratedDeriv (j-i) (smoothDelayed n z z₀) x‖
  let A (i : ℕ) := (j.choose i : ℝ) * C i
  have hA (i : ℕ) : 0 ≤ A i := mul_nonneg (Nat.cast_nonneg _) (hC i)
  have hi (i : ℕ) : Integrable (fun x => A i * F i x) :=
    (hdel (j-i) (Nat.sub_le j i)).1.const_mul (A i)
  have hpt (x : ℝ) : Real.exp (sigma*x)*‖iteratedDeriv j (fullCandidate n z z₀) x‖ ≤
      ∑ i ∈ Finset.range (j+1), A i * F i x := by
    have hh := norm_iteratedFDeriv_smul_le
      ((cutoff n).contDiff : ContDiff ℝ ∞ (cutoff n : ℝ → ℝ))
      (smoothDelayed_smooth n z z₀) x (n := j) (by simp)
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
    apply (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    dsimp [A, F]
    calc
      _ ≤ Real.exp (sigma*x) * (((j.choose i : ℝ) * C i) *
          ‖iteratedDeriv (j-i) (smoothDelayed n z z₀) x‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcut i x) (Nat.cast_nonneg _)) (norm_nonneg _))
          (Real.exp_pos _).le
      _ = _ := by ring
  calc
    _ ≤ ∫ x : ℝ, ∑ i ∈ Finset.range (j+1), A i * F i x :=
      integral_mono (fullCandidate_weighted_iteratedDeriv_integrable sigma j n z z₀)
        (integrable_finsetSum _ (fun i _ => hi i)) hpt
    _ = ∑ i ∈ Finset.range (j+1), A i * ∫ x : ℝ, F i x := by
      rw [integral_finsetSum _ (fun i _ => hi i)]
      simp only [integral_const_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hdel (j-i) (Nat.sub_le j i)).2 (hA i)

theorem fullCandidate_weighted_derivative_bounds {a beta L : ℝ}
    (ha : 0 ≤ a) (hgap : a < beta) :
    ∃ B : Fin 3 → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (n : ℕ) (z z₀ : ℂ), beta ≤ z.re → beta ≤ z₀.re → ‖z‖ ≤ L → ‖z₀‖ ≤ L →
        ∀ sigma : ℝ, |sigma| ≤ a → ∀ j : Fin 3,
          Integrable (fun x : ℝ => Real.exp (sigma*x)*‖iteratedDeriv j.val (fullCandidate n z z₀) x‖) ∧
          weightedDerivativeMass sigma j.val (fullCandidate n z z₀) ≤ B j := by
  classical
  choose C hC hcut using cutoff_iteratedDeriv_uniform
  let M (k : ℕ) := Real.exp (3*a)*(2*L^k/(beta-a) + if k = 2 then 2*L else 0)
  let B (j : Fin 3) := ∑ i ∈ Finset.range (j.val+1), (j.val.choose i : ℝ) * C i * M (j.val-i)
  refine ⟨fun j => max 0 (B j), fun _ => le_max_left _ _, ?_⟩
  intro n z z₀ hz hz₀ hLz hLz₀ sigma hsigma j
  refine ⟨fullCandidate_weighted_iteratedDeriv_integrable sigma j.val n z z₀, ?_⟩
  apply le_trans _ (le_max_right _ _)
  apply fullCandidate_leibniz_mass n j.val z z₀ sigma C M hC (fun i x => (hcut i n x).2)
  intro k hk
  have hj : j.val ≤ 2 := by omega
  exact smoothDelayed_weighted_iteratedDeriv_bound n z z₀ hz hz₀ hgap ha hsigma hLz hLz₀
    k (hk.trans hj)

#print axioms fullCandidate_leibniz_mass
#print axioms fullCandidate_weighted_derivative_bounds
end RHConnections.Mollifier
