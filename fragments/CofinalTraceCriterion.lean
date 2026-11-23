import Verified

namespace RHConnections.PoleCompensation

theorem riemannHypothesis_of_cofinal_restricted_finite_traces
    {ι : ℝ → Type*} (xi : ∀ a : ℝ, ι a → ℂ) (mult : ∀ a : ℝ, ι a → ℕ)
    (N : ℝ → ℝ → ℝ) (C : ℝ → ℝ) {z₀ : ℂ} (hz₀ : 1/2 < z₀.re)
    (hcofinal : ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ a < ε ∧ a < 1/2 ∧
      0 ≤ C a ∧ (∀ i, |(xi a i).re| ≤ a) ∧
      (∀ (T : ℝ) (s : Finset (ι a)), (∀ i ∈ s, |(xi a i).im| ≤ T) →
        (∑ i ∈ s, (mult a i : ℝ)) ≤ N a T) ∧
      (∀ T : ℝ, 1 ≤ T → N a T ≤ C a * (T+2) * Real.log (T+2)) ∧
      RestrictedFiniteTrace (xi a) (mult a) a z₀) : RiemannHypothesis := by
  apply riemannHypothesis_of_right_zero_free
  intro s hs
  obtain ⟨a, ha, hgap, ha₁, hC, hstrip, hcount, hgrowth, htrace⟩ :=
    hcofinal (s.re-1/2) (by linarith)
  exact zero_free_from_restricted_finite_trace (xi a) (mult a) (N a) (C a)
    hC hcount hgrowth ha.le ha₁ hstrip hz₀ htrace (by linarith)

end RHConnections.PoleCompensation
