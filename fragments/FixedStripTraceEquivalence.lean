import Verified

noncomputable section
namespace RHConnections.PoleCompensation
open SpectralTail FourierDecay WeightedConvolution

theorem fixed_strip_trace_iff_of_full {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1/2)
    {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) (hfull : ZetaFullFiniteTrace z₀) :
    ZetaRestrictedTrace a z₀ ↔ ∀ r : NontrivialZetaZero, |r.val.re-1/2| ≤ a := by
  constructor
  · intro htr
    obtain ⟨C,hC,hcount⟩ := zeta_quantitative_zero_count
    let xi := fun r : StripZetaZero a => r.val.val-(1/2 : ℂ)
    let mult := fun r : StripZetaZero a => analyticOrderNatAt riemannZeta r.val.val
    let N (T : ℝ) := C * (max T 1+2) * Real.log (max T 1+2)
    have hfree (s : ℂ) (hs : a+1/2 < s.re) : riemannZeta s ≠ 0 := by
      apply zero_free_from_restricted_finite_trace xi mult N C hC (a := a) (z₀ := z₀)
      · intro T t ht
        let e : StripZetaZero a ↪ NontrivialZetaZero := ⟨Subtype.val, Subtype.val_injective⟩
        have hh := hcount (max T 1) (t.map e) (le_max_right _ _) (by
          intro r hr
          obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hr
          have h := (ht q hq).trans (le_max_left T 1)
          simpa [e, xi, Complex.sub_im, Complex.div_im] using h)
        simpa only [Finset.sum_map, e, Function.Embedding.coeFn_mk, mult, N] using hh
      · intro T hT
        simp [N, max_eq_left hT]
      · exact ha
      · exact ha₁
      · intro r
        have hre : (r.val.val-(1/2:ℂ)).re = r.val.val.re-1/2 := by norm_num [Complex.sub_re, Complex.div_re]
        change |(r.val.val-(1/2:ℂ)).re| ≤ a
        rw [hre]
        exact r.property
      · exact hz₀
      · exact htr
      · exact hs
    intro r
    have hr : entireXi r.val = 0 := (entireXi_eq_zero_iff _).2 r.property
    have href := ((entireXi_eq_zero_iff (1-r.val)).1 ((entireXi_reflection r.val).trans hr)).2
    rw [abs_le]
    constructor
    · by_contra! h
      exact hfree (1-r.val) (by simp only [Complex.sub_re, Complex.one_re]; linarith) href
    · by_contra! h
      exact hfree r.val (by linarith) r.property.2
  · intro hstrip
    let e : StripZetaZero a ≃ NontrivialZetaZero :=
      { toFun := Subtype.val, invFun := fun r => ⟨r,hstrip r⟩
        left_inv := fun r => Subtype.ext rfl, right_inv := fun _ => rfl }
    intro z _ n
    have he := e.tsum_eq (fun r => (analyticOrderNatAt riemannZeta r.val : ℂ) *
      angularTransform (weighted (r.val-(1/2 : ℂ)).re (Mollifier.fullCandidate n z z₀))
        (r.val-(1/2 : ℂ)).im)
    exact (hfull z n).trans (congrArg (fun w =>
      poleTest (1/2) n z z₀ + poleTest (-1/2) n z z₀ - w) he.symm)

theorem fixed_strip_trace_iff {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1/2)
    {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) :
    ZetaRestrictedTrace a z₀ ↔ ∀ r : NontrivialZetaZero, |r.val.re-1/2| ≤ a :=
  fixed_strip_trace_iff_of_full ha ha₁ hz₀ (zeta_full_finite_trace z₀)

#print axioms fixed_strip_trace_iff_of_full
#print axioms fixed_strip_trace_iff
end RHConnections.PoleCompensation
