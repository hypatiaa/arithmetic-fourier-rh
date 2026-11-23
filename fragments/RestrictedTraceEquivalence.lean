import Verified

namespace RHConnections.PoleCompensation
open SpectralTail FourierDecay WeightedConvolution

def ZetaFullFiniteTrace (z₀ : ℂ) : Prop :=
  ∀ (z : ℂ) (n : ℕ), primeTest n z z₀ + realPlaceTest n z z₀ =
      poleTest (1/2) n z z₀ + poleTest (-1/2) n z z₀ - zetaSpectralTest n z z₀

theorem zeta_restricted_trace_of_RH (hRH : RiemannHypothesis)
    {a : ℝ} (ha : 0 ≤ a) {z₀ : ℂ} (hfull : ZetaFullFiniteTrace z₀) :
    ZetaRestrictedTrace a z₀ := by
  have hstrip (r : NontrivialZetaZero) : |r.val.re-1/2| ≤ a := by
    have hr : r.val.re = 1/2 := hRH r.val r.property.2 (by
      rintro ⟨n, hn⟩
      have hp := r.property.1.1
      have he := congrArg Complex.re hn
      simp [Complex.mul_re, Complex.add_re] at he
      linarith [Nat.cast_nonneg (α := ℝ) n]) (by
      intro h
      have hh := r.property.1.2
      rw [h, Complex.one_re] at hh
      exact (lt_irrefl _) hh)
    simpa [hr] using ha
  let e : StripZetaZero a ≃ NontrivialZetaZero :=
    { toFun := Subtype.val, invFun := fun r => ⟨r,hstrip r⟩
      left_inv := fun r => Subtype.ext rfl, right_inv := fun _ => rfl }
  intro z _ n
  have heq := e.tsum_eq (fun r =>
    (analyticOrderNatAt riemannZeta r.val : ℂ) *
      angularTransform (weighted (r.val-(1/2 : ℂ)).re (Mollifier.fullCandidate n z z₀))
        (r.val-(1/2 : ℂ)).im)
  exact (hfull z n).trans (congrArg (fun w =>
    poleTest (1/2) n z z₀ + poleTest (-1/2) n z z₀ - w) heq.symm)

theorem zeta_restricted_traces_iff_RH (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ (T : ℝ) (s : Finset NontrivialZetaZero), 1 ≤ T →
      (∀ r ∈ s, |r.val.im| ≤ T) →
      (∑ r ∈ s, (analyticOrderNatAt riemannZeta r.val : ℝ)) ≤ C * (T+2) * Real.log (T+2))
    {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) (hfull : ZetaFullFiniteTrace z₀) :
    (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ a < ε ∧ a < 1/2 ∧ ZetaRestrictedTrace a z₀)
      ↔ RiemannHypothesis := by
  refine ⟨riemannHypothesis_of_zeta_restricted_traces C hC hcount hz₀, ?_⟩
  intro hRH ε hε
  let a := min (ε/2) (1/4)
  have ha : 0 < a := lt_min (by linarith) (by norm_num)
  have haε : a < ε := (min_le_left _ _).trans_lt (by linarith)
  have ha₁ : a < 1/2 := (min_le_right _ _).trans_lt (by norm_num)
  exact ⟨a, ha, haε, ha₁, zeta_restricted_trace_of_RH hRH ha.le hfull⟩

end RHConnections.PoleCompensation
