import Verified

namespace RHConnections.PoleCompensation
open SpectralTail

abbrev StripZetaZero (a : ℝ) := {r : NontrivialZetaZero | |r.val.re - 1/2| ≤ a}

def ZetaRestrictedTrace (a : ℝ) (z₀ : ℂ) : Prop :=
  RestrictedFiniteTrace
    (fun r : StripZetaZero a => r.val.val-(1/2 : ℂ))
    (fun r => analyticOrderNatAt riemannZeta r.val.val) a z₀

theorem riemannHypothesis_of_zeta_restricted_traces (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ (T : ℝ) (s : Finset NontrivialZetaZero), 1 ≤ T →
      (∀ r ∈ s, |r.val.im| ≤ T) →
      (∑ r ∈ s, (analyticOrderNatAt riemannZeta r.val : ℝ)) ≤ C * (T+2) * Real.log (T+2))
    {z₀ : ℂ} (hz₀ : 1/2 < z₀.re)
    (htrace : ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ a < ε ∧ a < 1/2 ∧
      ZetaRestrictedTrace a z₀) : RiemannHypothesis := by
  let xi (a : ℝ) (r : StripZetaZero a) := r.val.val - (1/2 : ℂ)
  let mult (a : ℝ) (r : StripZetaZero a) := analyticOrderNatAt riemannZeta r.val.val
  let N (T : ℝ) := C * (max T 1+2) * Real.log (max T 1+2)
  apply riemannHypothesis_of_cofinal_restricted_finite_traces xi mult (fun _ => N) (fun _ => C) hz₀
  intro ε hε
  obtain ⟨a, ha, hεa, ha₁, htr⟩ := htrace ε hε
  refine ⟨a, ha, hεa, ha₁, hC, ?_, ?_, ?_, htr⟩
  · intro r
    have hh : |r.val.val.re - 1/2| ≤ a := r.property
    have hre : (r.val.val-(1/2:ℂ)).re = r.val.val.re - 1/2 := by norm_num [Complex.sub_re, Complex.div_re]
    change |(r.val.val-(1/2:ℂ)).re| ≤ a
    rw [hre]
    exact hh
  · intro T s hs
    let e : StripZetaZero a ↪ NontrivialZetaZero := ⟨Subtype.val, Subtype.val_injective⟩
    have hh := hcount (max T 1) (s.map e) (le_max_right _ _) (by
      intro r hr
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hr
      have h := (hs q hq).trans (le_max_left T 1)
      simpa [e, xi, Complex.sub_im, Complex.div_im] using h)
    simpa only [Finset.sum_map, e, Function.Embedding.coeFn_mk, mult, N] using hh
  · intro T hT
    simp [N, max_eq_left hT]

end RHConnections.PoleCompensation
