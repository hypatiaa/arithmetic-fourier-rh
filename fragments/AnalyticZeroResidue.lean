import Verified
import Mathlib.Analysis.Calculus.LogDeriv

noncomputable section
namespace RHConnections.PoleCompensation
open Filter
open scoped Topology

theorem analyticOrder_logDerivative_residue {f : ℂ → ℂ} {rho : ℂ}
    (hf : AnalyticAt ℂ f rho) (hfin : analyticOrderAt f rho ≠ ⊤) :
    Tendsto (fun s => (s-rho)*(deriv f s / f s)) (𝓝[≠] rho)
      (𝓝 (analyticOrderNatAt f rho : ℂ)) := by
  let m := analyticOrderNatAt f rho
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderNatAt_eq_iff hfin (n := m)).mp rfl
  let p := fun t : ℂ => t-rho
  have hp (t : ℂ) : HasDerivAt p 1 t := (hasDerivAt_id t).sub_const rho
  have he : f =ᶠ[𝓝 rho] (fun t => p t ^ m) * g := hfg
  have hc : ContinuousAt (fun t : ℂ => (m:ℂ) + (t-rho) * logDeriv g t) rho :=
    continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul
      (hg.deriv.continuousAt.div hg.continuousAt hg0))
  have ht : Tendsto (fun t : ℂ => (m:ℂ) + (t-rho) * logDeriv g t)
      (𝓝[≠] rho) (𝓝 (m:ℂ)) := by
    simpa using (hc.tendsto.mono_left nhdsWithin_le_nhds)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (logDeriv_congr_nhds he).filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with t ht0 heq hgt hga
  have hpt : p t ≠ 0 := sub_ne_zero.mpr ht0
  change (m:ℂ) + p t * logDeriv g t = p t * logDeriv f t
  rw [heq, logDeriv_mul (f := fun u => p u ^ m) (g := g) t (pow_ne_zero m hpt) hgt ((hp t).differentiableAt.pow m)
    hga.differentiableAt, logDeriv_fun_pow (hp t).differentiableAt m, logDeriv_apply p,
    (hp t).deriv]
  field_simp [hpt] <;> ring

theorem compensated_zeta_zero_residue {rho : ℂ} (hr : rho ≠ 1)
    (hfin : analyticOrderAt riemannZeta rho ≠ ⊤) :
    Tendsto (fun s => (s-rho)*compensatedLogDerivative s) (𝓝[≠] rho)
      (𝓝 (-(analyticOrderNatAt riemannZeta rho : ℂ))) := by
  have h := analyticOrder_logDerivative_residue (analyticOn_riemannZeta rho hr) hfin
  have hc : ContinuousAt (fun s : ℂ => (s-rho) * (1/(s-1))) rho :=
    (continuousAt_id.sub continuousAt_const).mul
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hr))
  have h0 : Tendsto (fun s : ℂ => (s-rho) * (1/(s-1))) (𝓝[≠] rho) (𝓝 0) := by
    simpa using (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have H := h.neg.sub h0
  simpa only [compensatedLogDerivative, mul_sub, neg_div, mul_neg,
    Pi.neg_apply, Pi.sub_apply, sub_zero] using H

end RHConnections.PoleCompensation
