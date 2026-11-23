import Verified
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

noncomputable section
open Filter Complex
open scoped Topology ComplexConjugate
namespace RHConnections.SpectralTail

def conjugateZeroEquiv : NontrivialZetaZero ≃ NontrivialZetaZero := by
  let c (r : NontrivialZetaZero) : NontrivialZetaZero :=
    ⟨conj r.val, by exact ⟨r.property.1,by simp [r.property.2]⟩⟩
  have hc (r : NontrivialZetaZero) : c (c r)=r := by
    apply Subtype.ext
    exact Complex.conj_conj _
  exact ⟨c,c,hc,hc⟩

@[simp] theorem conjugateZeroEquiv_val (r : NontrivialZetaZero) :
    (conjugateZeroEquiv r).val=conj r.val := rfl

@[simp] theorem conjugateZeroEquiv_order (r : NontrivialZetaZero) :
    analyticOrderNatAt riemannZeta (conjugateZeroEquiv r).val =
    analyticOrderNatAt riemannZeta r.val := by
  obtain ⟨ha,hfin⟩ := zeta_nontrivial_zero_finite_order r
  obtain ⟨hac,hfinc⟩ := zeta_nontrivial_zero_finite_order (conjugateZeroEquiv r)
  obtain ⟨g,hg,hgn,hfactor⟩ := ha.analyticOrderAt_ne_top.mp hfin
  apply (hac.analyticOrderNatAt_eq_iff hfinc).mpr
  have hc : Tendsto (conj : ℂ → ℂ) (𝓝 (conj r.val)) (𝓝 r.val) := by
    simpa using (Complex.continuous_conj.continuousAt (x := conj r.val)).tendsto
  refine ⟨fun z => conj (g (conj z)),?_,?_,?_⟩
  · apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    exact (hc.eventually (Complex.analyticAt_iff_eventually_differentiableAt.mp hg)).mono
      (fun z hz => differentiableAt_conj_conj_iff.mpr hz)
  · simpa using hgn
  · filter_upwards [hc.eventually hfactor] with z hz
    have h := congrArg (conj : ℂ → ℂ) hz
    simpa [smul_eq_mul] using h

end RHConnections.SpectralTail
