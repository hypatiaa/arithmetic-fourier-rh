import CompactDerivativeBounds
import WeightedConvolution
import AngularDecay
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory
open scoped ContDiff
namespace RHConnections.FourierDecay
open Mollifier AnalyticObligations WeightedConvolution

theorem weighted_iteratedDeriv_mass (sigma a : ℝ) (hsigma : |sigma| ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (j : ℕ) (M : ℕ → ℝ)
    (hm : ∀ k, k ≤ j →
      Integrable (fun x : ℝ => Real.exp (sigma*x)*‖iteratedDeriv k f x‖) ∧
        weightedDerivativeMass sigma k f ≤ M k) :
    (∫ x : ℝ, ‖iteratedDeriv j (weighted sigma f) x‖) ≤
      ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*a^i*M (j-i) := by
  let F (i : ℕ) (x : ℝ) := Real.exp (sigma*x)*‖iteratedDeriv (j-i) f x‖
  let A (i : ℕ) := (j.choose i : ℝ)*a^i
  have ha : 0 ≤ a := (abs_nonneg _).trans hsigma
  have hA (i : ℕ) : 0 ≤ A i := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha i)
  have hexp : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (sigma*x)) := by fun_prop
  have hw : ContDiff ℝ ∞ (weighted sigma f) := hexp.smul hf
  have hc' : HasCompactSupport (weighted sigma f) :=
    hc.smul_left (f := fun x : ℝ => Real.exp (sigma*x))
  have hi (i : ℕ) : Integrable (fun x => A i * F i x) :=
    (hm (j-i) (Nat.sub_le j i)).1.const_mul _
  have hpt (x : ℝ) : ‖iteratedDeriv j (weighted sigma f) x‖ ≤
      ∑ i ∈ Finset.range (j+1), A i * F i x := by
    have hh := norm_iteratedFDeriv_smul_le hexp hf x (n := j) (by simp)
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul,
      norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hh
    apply hh.trans
    apply Finset.sum_le_sum
    intro i _
    dsimp [A, F]
    calc
      _ ≤ (j.choose i : ℝ)*(a^i*Real.exp (sigma*x))*‖iteratedDeriv (j-i) f x‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hsigma i)
            (Real.exp_pos _).le) (Nat.cast_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∫ x : ℝ, ∑ i ∈ Finset.range (j+1), A i * F i x :=
      integral_mono (iteratedDeriv_integrable j hw hc').norm
        (integrable_finsetSum _ (fun i _ => hi i)) hpt
    _ = ∑ i ∈ Finset.range (j+1), A i * ∫ x : ℝ, F i x := by
      rw [integral_finsetSum _ (fun i _ => hi i)]
      simp only [integral_const_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hm (j-i) (Nat.sub_le j i)).2 (hA i)

theorem fullCandidate_weighted_angular_decay {a : ℝ} {z₀ : ℂ} (ha : 0 ≤ a)
    (hz₀ : a < z₀.re) (K : Set ℂ) (hK : IsCompact K) (hsub : K ⊆ halfPlane a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (n : ℕ) (z : ℂ), z ∈ K → ∀ sigma : ℝ, |sigma| ≤ a →
      ∀ tau : ℝ, ‖angularTransform (weighted sigma (fullCandidate n z z₀)) tau‖ ≤
        D/(1+tau^2) := by
  obtain ⟨B, hB, hmass⟩ := fullCandidate_compact_derivative_bounds ha hz₀ K hK hsub
  let D₂ := B 2 + 2*a*B 1 + a^2*B 0
  refine ⟨4*Real.pi^2*B 0 + D₂, ?_, ?_⟩
  · dsimp [D₂]
    have hB₀ := hB 0
    have hB₁ := hB 1
    have hB₂ := hB 2
    positivity
  intro n z hz sigma hsigma tau
  let f := fullCandidate n z z₀
  have hf : ContDiff ℝ ∞ f := fullCandidate_smooth n z z₀
  have hc : HasCompactSupport f := fullCandidate_compact n z z₀
  have hexp : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (sigma*x)) := by fun_prop
  have hw : ContDiff ℝ ∞ (weighted sigma f) := hexp.smul hf
  have hcw : HasCompactSupport (weighted sigma f) :=
    hc.smul_left (f := fun x : ℝ => Real.exp (sigma*x))
  have h0 : (∫ x : ℝ, ‖weighted sigma f x‖) ≤ B 0 := by
    simpa [norm_weighted, weightedDerivativeMass, f] using
      (hmass n z hz sigma hsigma 0).2
  let M (k : ℕ) := B ⟨min k 2, by omega⟩
  have h2 := weighted_iteratedDeriv_mass sigma a hsigma hf hc 2 M (by
    intro k hk
    have h := hmass n z hz sigma hsigma ⟨k, by omega⟩
    simpa only [M, min_eq_left hk] using h)
  have hD : (∫ x : ℝ, ‖iteratedDeriv 2 (weighted sigma f) x‖) ≤ D₂ := by
    convert h2 using 1
    norm_num [D₂, M, Finset.sum_range_succ, Nat.choose]
    <;> ring
  exact uniform_angular_quadratic_decay (fun _ : Unit => weighted sigma f) (B 0) D₂
    (fun _ => hw.of_le (by simp))
    (fun _ k _ => iteratedDeriv_integrable k hw hcw) (fun _ => h0) (fun _ => hD) () tau

#print axioms weighted_iteratedDeriv_mass
#print axioms fullCandidate_weighted_angular_decay
end RHConnections.FourierDecay
