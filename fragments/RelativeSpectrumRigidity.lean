import Verified

open Filter
noncomputable section
namespace RHConnections.RelativeSpectrumAnalytic
open RelativeResolvent SpectralTail

theorem spectrum_coefficients_zero_of_germ {ι : Type*} (rho b : ι → ℂ)
    (hinj : Function.Injective rho)
    (hfinite : ∀ R : ℝ, {i | ‖rho i‖ ≤ R}.Finite)
    (hs : Summable (fun i => ‖b i‖/‖rho i‖^2)) {z₀ w : ℂ}
    (hz₀ : z₀ ∉ Set.range rho) (hw : w ∉ Set.range rho)
    (hgerm : spectrum rho b z₀ =ᶠ[nhds w] (fun _ => 0)) :
    ∀ k, b k = 0 := by
  classical
  let U := (Set.range rho)ᶜ
  have hU : IsOpen U := (range_closed_of_radially_finite rho hfinite).isOpen_compl
  have hconn : IsPreconnected U := (complement_connected_of_radially_finite rho hfinite).isPreconnected
  have hfa (R : ℝ) : {i | b i ≠ 0 ∧ ‖rho i‖ ≤ R}.Finite :=
    (hfinite R).subset (fun _ h => h.2)
  have hA := spectrum_analyticOnNhd rho b z₀ hfa hs hU
    (fun _ hz i _ he => hz ⟨i,he.symm⟩)
  have hz : Set.EqOn (spectrum rho b z₀) (fun _ => 0) U :=
    hA.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const) hconn hw hgerm
  intro k
  let K : Set ι := {k}
  let rho' := fun i : ↥(Kᶜ) => rho i.val
  let b' := fun i : ↥(Kᶜ) => b i.val
  let V := (Set.range rho')ᶜ
  have hfinite' (R : ℝ) : {i | ‖rho' i‖ ≤ R}.Finite :=
    (hfinite R).preimage Subtype.val_injective.injOn
  have hV : IsOpen V := (range_closed_of_radially_finite rho' hfinite').isOpen_compl
  have hkV : rho k ∈ V := fun ⟨i,hi⟩ => i.property (hinj hi)
  have hfa' (R : ℝ) : {i | b' i ≠ 0 ∧ ‖rho' i‖ ≤ R}.Finite :=
    (hfinite' R).subset (fun _ h => h.2)
  have hs' : Summable (fun i => ‖b' i‖/‖rho' i‖^2) := hs.subtype Kᶜ
  let rem := spectrum rho' b' z₀
  have hr : AnalyticAt ℂ rem (rho k) :=
    spectrum_analyticOnNhd rho' b' z₀ hfa' hs' hV
      (fun _ hz i _ he => hz ⟨i,he.symm⟩) _ hkV
  let G := fun z => b k + (z-rho k)*(rem z - b k*(z₀-rho k)⁻¹)
  have hG : ContinuousAt G (rho k) :=
    continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul
      (hr.continuousAt.sub continuousAt_const))
  have hnz₀ : z₀-rho k ≠ 0 := sub_ne_zero.mpr (fun he => hz₀ ⟨k,he.symm⟩)
  have hsplit (z : ℂ) :
      spectrum rho b z₀ z = b k * relative z z₀ (rho k) + rem z := by
    let f := fun i => b i * relative z z₀ (rho i)
    have hsum : Summable f :=
      ((relative_hasSum_locallyUniformlyOn rho b z₀ hfa hs isOpen_univ).hasSum (Set.mem_univ z)).summable
    have hleft : (∑' i : K, f i.val) = f k := by
      rw [_root_.tsum_subtype K f, tsum_eq_single k (fun i hi => by simp [K, hi])]
      simp [K]
    change (∑' i, f i) = f k + ∑' i : ↥(Kᶜ), f i.val
    have hboth : (∑' i : K, f i.val) + (∑' i : ↥(Kᶜ), f i.val) = ∑' i, f i :=
      (hsum.subtype K).tsum_add_tsum_compl (hsum.subtype Kᶜ)
    rw [hleft] at hboth
    exact hboth.symm
  have h0 : G =ᶠ[nhdsWithin (rho k) ({rho k}ᶜ : Set ℂ)] (fun _ => 0) := by
    filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds hkV),
      self_mem_nhdsWithin] with z hzV hzk
    have hneq : z ≠ rho k := hzk
    have hzU : z ∈ U := by
      rintro ⟨i,hi⟩
      by_cases hik : i = k
      · exact hneq (hik ▸ hi.symm)
      · exact hzV ⟨⟨i,hik⟩,hi⟩
    have hGmul : (z-rho k)*(b k*relative z z₀ (rho k) + rem z) = G z := by
      dsimp only [G,relative]
      field_simp [sub_ne_zero.mpr hneq, hnz₀]
      <;> ring
    rw [← hGmul, ← hsplit, hz hzU, mul_zero]
  have ht := tendsto_const_nhds.congr' h0.symm
  have hh := tendsto_nhds_unique (hG.mono_left nhdsWithin_le_nhds) ht
  simpa [G] using hh

end RHConnections.RelativeSpectrumAnalytic
