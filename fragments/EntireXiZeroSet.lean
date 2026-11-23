import Verified

namespace RHConnections.SpectralTail

theorem entireXi_reflection (s : ℂ) : entireXi (1-s) = entireXi s := by
  unfold entireXi
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem entireXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : entireXi s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    simp [entireXi]
  have hs' : 0 < s.re := zero_lt_one.trans_le hs
  have h0 : s ≠ 0 := by intro he; simpa [he] using hs'
  rw [(entireXi_zeta_germ hs' h1).eq_of_nhds]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) (gamma_real_nonzero_of_re_pos hs'))
    (riemannZeta_ne_zero_of_one_le_re hs)

theorem entireXi_eq_zero_iff (s : ℂ) :
    entireXi s = 0 ↔ (0 < s.re ∧ s.re < 1) ∧ riemannZeta s = 0 := by
  constructor
  · intro h
    have hl : 0 < s.re := by
      by_contra! hn
      have hh : 1 ≤ (1-s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
      exact entireXi_ne_zero_of_one_le_re hh ((entireXi_reflection s).trans h)
    have hr : s.re < 1 := lt_of_not_ge (fun hn => entireXi_ne_zero_of_one_le_re hn h)
    have h1 : s ≠ 1 := by intro he; simpa [he] using hr
    have h0 : s ≠ 0 := by intro he; simpa [he] using hl
    rw [(entireXi_zeta_germ hl h1).eq_of_nhds] at h
    exact ⟨⟨hl,hr⟩, (mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) (gamma_real_nonzero_of_re_pos hl))⟩
  · rintro ⟨⟨hl,hr⟩, h⟩
    have h1 : s ≠ 1 := by intro he; simpa [he] using hr
    rw [(entireXi_zeta_germ hl h1).eq_of_nhds, h, mul_zero]

end RHConnections.SpectralTail
