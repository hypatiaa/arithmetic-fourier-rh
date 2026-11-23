import Verified

open Filter
noncomputable section
namespace RHConnections.SpectralTail
open RelativeSpectrumAnalytic RelativeResolvent PoleCompensation

theorem zeta_zero_radially_finite (R : ℝ) :
    {r : NontrivialZetaZero | ‖r.val‖ ≤ R}.Finite := by
  let A := max R 1
  have hA : 0 < A := zero_lt_one.trans_le (le_max_right _ _)
  let d (r : NontrivialZetaZero) := (analyticOrderNatAt riemannZeta r.val : ℝ)/‖r.val‖^2
  have hs : Summable d := zeta_inverse_square_with_multiplicity
  have he : ∀ᶠ r in cofinite, d r < 1/A^2 :=
    hs.tendsto_cofinite_zero.eventually_lt_const (by positivity)
  have hfin : {r : NontrivialZetaZero | d r < 1/A^2}ᶜ.Finite := mem_cofinite.mp he
  apply hfin.subset
  intro r hr
  change ¬ d r < 1/A^2
  apply not_lt_of_ge
  obtain ⟨δ,hδ,hd⟩ := zeta_zero_norm_lower
  have hp := hδ.trans_le (hd r)
  obtain ⟨ha,hf⟩ := zeta_nontrivial_zero_finite_order r
  have ho : 1 ≤ (analyticOrderNatAt riemannZeta r.val : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (zero_order_positive r.property.2 ha hf))
  have hle : ‖r.val‖ ≤ A := (show ‖r.val‖ ≤ R from hr).trans (le_max_left _ _)
  calc
    1/A^2 ≤ 1/‖r.val‖^2 := one_div_le_one_div_of_le (sq_pos_of_pos hp)
      (pow_le_pow_left₀ (norm_nonneg _) hle 2)
    _ ≤ d r := div_le_div_of_nonneg_right ho (sq_nonneg _)

theorem zeta_weights_eq_multiplicities_of_euler_germ
    (b : NontrivialZetaZero → ℂ) (hb : Summable (fun r => ‖b r‖/‖r.val‖^2))
    {s₀ w : ℂ} (hs₀ : 1 < s₀.re) (hw : 1 < w.re)
    (hgerm : RelativeSpectrumAnalytic.spectrum (fun r : NontrivialZetaZero => r.val) b s₀ =ᶠ[nhds w]
      (fun s => zetaSpectralRelative (s-1/2) (s₀-1/2))) :
    ∀ r, b r = (analyticOrderNatAt riemannZeta r.val : ℂ) := by
  let rho := fun r : NontrivialZetaZero => r.val
  let m := fun r : NontrivialZetaZero => (analyticOrderNatAt riemannZeta r.val : ℂ)
  let c := fun r : NontrivialZetaZero => b r - m r
  have hm : Summable (fun r => ‖m r‖/‖rho r‖^2) := by
    simpa only [m,rho,Complex.norm_natCast] using zeta_inverse_square_with_multiplicity
  have hc : Summable (fun r => ‖c r‖/‖rho r‖^2) := by
    apply (hb.add hm).of_nonneg_of_le (fun _ => by positivity)
    intro r
    change ‖b r - m r‖/‖rho r‖^2 ≤ ‖b r‖/‖rho r‖^2 + ‖m r‖/‖rho r‖^2
    rw [← add_div]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (sq_nonneg _)
  have hsum (d : NontrivialZetaZero → ℂ) (hd : Summable (fun r => ‖d r‖/‖rho r‖^2)) (s : ℂ) :
      Summable (fun r => d r * relative s s₀ (rho r)) :=
    ((relative_hasSum_locallyUniformlyOn rho d s₀
      (fun R => (zeta_zero_radially_finite R).subset fun _ h => h.2) hd isOpen_univ).hasSum
      (Set.mem_univ s)).summable
  have hshift (s : ℂ) : zetaSpectralRelative (s-1/2) (s₀-1/2) = RelativeSpectrumAnalytic.spectrum rho m s₀ s := by
    unfold zetaSpectralRelative RelativeSpectrumAnalytic.spectrum
    apply tsum_congr
    intro r
    have he (t : ℂ) : t-1/2-(r.val-1/2) = t-r.val := by ring
    simp only [relative, he, m, rho]
  have hoff (t : ℂ) (ht : 1 < t.re) : t ∉ Set.range rho := by
    rintro ⟨r, rfl⟩
    exact (not_lt_of_ge ht.le) r.property.1.2
  have hzero : RelativeSpectrumAnalytic.spectrum rho c s₀ =ᶠ[nhds w] (fun _ => 0) := by
    filter_upwards [hgerm] with s hh
    rw [hshift s] at hh
    change RelativeSpectrumAnalytic.spectrum rho b s₀ s = RelativeSpectrumAnalytic.spectrum rho m s₀ s at hh
    change (∑' r, (b r - m r) * relative s s₀ (rho r)) = 0
    simp_rw [sub_mul]
    rw [(hsum b hb s).tsum_sub (hsum m hm s)]
    exact sub_eq_zero.mpr hh
  have hid := spectrum_coefficients_zero_of_germ rho c Subtype.val_injective
    zeta_zero_radially_finite hc (hoff s₀ hs₀) (hoff w hw) hzero
  exact fun r => sub_eq_zero.mp (hid r)

#print axioms zeta_zero_radially_finite
#print axioms zeta_weights_eq_multiplicities_of_euler_germ
end RHConnections.SpectralTail
