import Verified

namespace RHConnections.CanonicalFactor
open SpectralTail

theorem zetaFactor_eq_zero_iff (r : RepeatedZetaZero) (s : ℂ) :
    zetaFactor r s = 0 ↔ s = r.1.val := by
  obtain ⟨δ, hδ, hd⟩ := zeta_zero_norm_lower
  have hn : r.1.val ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hd r.1))
  unfold zetaFactor genusOne
  rw [mul_eq_zero]
  simp only [Complex.exp_ne_zero, or_false, sub_eq_zero]
  constructor
  · intro h
    have h' := (div_eq_iff hn).mp h.symm
    simpa using h'
  · intro h
    rw [h, div_self hn]

theorem zetaCanonicalProduct_ne_zero {s : ℂ} (h : ∀ r : NontrivialZetaZero, s ≠ r.val) :
    zetaCanonicalProduct s ≠ 0 := by
  obtain ⟨u, hu, hb⟩ := zetaFactor_majorant_on_compact {s} isCompact_singleton
  have hm : Summable (fun r => ‖zetaFactor r s-1‖) :=
    hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => hb r s (Set.mem_singleton s))
  have he (r : RepeatedZetaZero) : 1+(zetaFactor r s-1) = zetaFactor r s := by ring
  have hz : ∀ r : RepeatedZetaZero, 1+(zetaFactor r s-1) ≠ 0 := by
    intro r
    rw [he]
    exact fun hr => h r.1 ((zetaFactor_eq_zero_iff r s).mp hr)
  have hh := tprod_one_add_ne_zero_of_summable hz hm
  simpa only [he, zetaCanonicalProduct] using hh

theorem zetaCanonicalProduct_zero (r : NontrivialZetaZero) : zetaCanonicalProduct r.val = 0 := by
  obtain ⟨ha, hf⟩ := zeta_nontrivial_zero_finite_order r
  let i : RepeatedZetaZero := ⟨r, ⟨0, zero_order_positive r.property.2 ha hf⟩⟩
  exact tprod_of_exists_eq_zero
    ⟨i, (zetaFactor_eq_zero_iff i r.val).mpr rfl⟩

end RHConnections.CanonicalFactor
