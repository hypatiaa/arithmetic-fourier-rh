import Verified

open Filter
noncomputable section
namespace RHConnections.PoleCompensation
open SpectralTail RelativeResolvent FourierDecay WeightedConvolution

theorem full_zeta_euler_residual_limit (z z₀ : ℂ) (hz : 1/2 < z.re) (hz₀ : 1/2 < z₀.re) :
    Tendsto (fun n => traceResidual (fun r : NontrivialZetaZero => r.val-(1/2 : ℂ))
      (fun r => analyticOrderNatAt riemannZeta r.val) n z z₀) atTop (nhds 0) := by
  have hp := poleTest_limit (show (-1/2 : ℝ) < z.re by linarith)
    (show (-1/2 : ℝ) < z₀.re by linarith)
  have hs := (zeta_spectral_test_limit z z₀ hz hz₀).2.2
  have ha : Tendsto (fun n => realPlaceTest n z z₀) atTop (nhds (realPlaceRelative z z₀)) :=
    ArchimedeanLimit.realPlaceKernel_limit (by linarith) (by linarith)
  have h := (compensated_zeta_euler_spectral_limit z z₀ hz hz₀).sub ((hp.sub hs).sub ha)
  rw [sub_self] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  change primeTest n z z₀ - poleTest (1/2) n z z₀ -
      (poleTest (-1/2) n z z₀ - zetaSpectralTest n z z₀ - realPlaceTest n z z₀) =
    primeTest n z z₀ + realPlaceTest n z z₀ -
      (poleTest (1/2) n z z₀ + poleTest (-1/2) n z z₀ - zetaSpectralTest n z z₀)
  ring

def ZetaLineEulerResidual (z₀ : ℂ) : Prop :=
  ∀ z : ℂ, 1/2 < z.re → Tendsto (fun n =>
    traceResidual (fun r : StripZetaZero 0 => r.val.val-(1/2 : ℂ))
      (fun r => analyticOrderNatAt riemannZeta r.val.val) n z z₀) atTop (nhds 0)

theorem riemannHypothesis_iff_line_euler_residual {z₀ : ℂ} (hz₀ : 1/2 < z₀.re) :
    RiemannHypothesis ↔ ZetaLineEulerResidual z₀ := by
  constructor
  · intro hRH
    have hline (r : NontrivialZetaZero) : |r.val.re-1/2| ≤ 0 := by
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
      simp [hr]
    let e : StripZetaZero 0 ≃ NontrivialZetaZero :=
      { toFun := Subtype.val, invFun := fun r => ⟨r,hline r⟩
        left_inv := fun r => Subtype.ext rfl, right_inv := fun _ => rfl }
    intro z hz
    apply (full_zeta_euler_residual_limit z z₀ hz hz₀).congr'
    filter_upwards with n
    have he := e.tsum_eq (fun r => (analyticOrderNatAt riemannZeta r.val : ℂ) *
      angularTransform (weighted (r.val-(1/2 : ℂ)).re (Mollifier.fullCandidate n z z₀))
        (r.val-(1/2 : ℂ)).im)
    exact congrArg (fun w => primeTest n z z₀ + realPlaceTest n z z₀ -
      (poleTest (1/2) n z z₀ + poleTest (-1/2) n z z₀ - w)) he.symm
  · intro hres
    obtain ⟨C,hC,hcount⟩ := zeta_quantitative_zero_count
    let xi := fun r : StripZetaZero 0 => r.val.val-(1/2 : ℂ)
    let mult := fun r : StripZetaZero 0 => analyticOrderNatAt riemannZeta r.val.val
    let N (T : ℝ) := C * (max T 1+2) * Real.log (max T 1+2)
    apply riemannHypothesis_of_right_zero_free
    intro s hs
    apply zero_free_from_euler_residual xi mult N C hC (a := 0) (z₀ := z₀)
    · intro T t ht
      let e : StripZetaZero 0 ↪ NontrivialZetaZero := ⟨Subtype.val, Subtype.val_injective⟩
      have hh := hcount (max T 1) (t.map e) (le_max_right _ _) (by
        intro r hr
        obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hr
        have h := (ht q hq).trans (le_max_left T 1)
        simpa [e, xi, Complex.sub_im, Complex.div_im] using h)
      simpa only [Finset.sum_map, e, Function.Embedding.coeFn_mk, mult, N] using hh
    · intro T hT
      simp [N, max_eq_left hT]
    · exact le_rfl
    · norm_num
    · intro r
      have hre : (r.val.val-(1/2:ℂ)).re = r.val.val.re-1/2 := by
        norm_num [Complex.sub_re, Complex.div_re]
      change |(r.val.val-(1/2:ℂ)).re| ≤ 0
      rw [hre]
      exact r.property
    · exact hz₀
    · exact hres
    · simpa only [zero_add] using hs

#print axioms full_zeta_euler_residual_limit
#print axioms riemannHypothesis_iff_line_euler_residual
end RHConnections.PoleCompensation
