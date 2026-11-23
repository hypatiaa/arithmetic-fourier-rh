import Verified

namespace RHConnections.SpectralTail
open FourierDecay WeightedConvolution RelativeResolvent

theorem weighted_spectral_sum_limit {ι : Type*} (xi : ι → ℂ) (mult : ι → ℕ)
    (N : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ (T : ℝ) (s : Finset ι), (∀ i ∈ s, |(xi i).im| ≤ T) →
      (∑ i ∈ s, (mult i : ℝ)) ≤ N T)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → N T ≤ C * (T+2) * Real.log (T+2))
    {a : ℝ} (ha : 0 ≤ a) (hstrip : ∀ i, |(xi i).re| ≤ a)
    (z z₀ : ℂ) (hz : a < z.re) (hz₀ : a < z₀.re) :
    let F := fun n i => angularTransform
      (weighted (xi i).re (Mollifier.fullCandidate n z z₀)) (xi i).im
    (∀ n, Summable (fun i => ‖(mult i : ℂ) * F n i‖)) ∧
      Summable (fun i => ‖(mult i : ℂ) * relative z z₀ (xi i)‖) ∧
      Filter.Tendsto (fun n => ∑' i, (mult i : ℂ) * F n i) Filter.atTop
        (nhds (∑' i, (mult i : ℂ) * relative z z₀ (xi i))) := by
  classical
  dsimp only
  let F := fun n i => angularTransform
    (weighted (xi i).re (Mollifier.fullCandidate n z z₀)) (xi i).im
  have hK : ({z} : Set ℂ) ⊆ AnalyticObligations.halfPlane a := by
    intro w hw
    simpa [AnalyticObligations.halfPlane, Set.mem_singleton_iff.mp hw] using hz
  obtain ⟨D, hD, hdecay⟩ :=
    fullCandidate_weighted_angular_decay ha hz₀ {z} isCompact_singleton hK
  let B := fun i => D * ((mult i : ℝ)/(1+(xi i).im^2))
  have hB : Summable B :=
    (multiplicity_majorant_summable (fun i => (xi i).im) mult (8*C*Real.log 2)
      (fun j s hs => (hcount _ s (fun i hi => (hs i hi).le)).trans
        (cumulative_count_dyadic N C hC hgrowth j))).mul_left D
  have hb (n : ℕ) (i : ι) : ‖(mult i : ℂ)*F n i‖ ≤ B i := by
    have h := hdecay n z (Set.mem_singleton z) (xi i).re (hstrip i) (xi i).im
    rw [norm_mul, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)).trans_eq (by
      dsimp [B]; ring)
  have hp (i : ι) : Filter.Tendsto (fun n => F n i) Filter.atTop
      (nhds (relative z z₀ (xi i))) :=
    fullCandidate_weighted_angular_limit z z₀ (xi i)
      (((le_abs_self _).trans (hstrip i)).trans_lt hz)
      (((le_abs_self _).trans (hstrip i)).trans_lt hz₀)
  refine ⟨fun n => hB.of_nonneg_of_le (fun _ => norm_nonneg _) (hb n), ?_,
    individual_spectral_limit mult B hB hp hb⟩
  apply hB.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  exact le_of_tendsto ((tendsto_const_nhds.mul (hp i)).norm)
    (Filter.Eventually.of_forall (fun n => hb n i))

end RHConnections.SpectralTail
