import Verified

noncomputable section
namespace RHConnections.ZetaZeroFreeRegion
open SpectralTail CanonicalFactor

theorem completed_logDerivative_real_lower :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ s : ℂ, 1 < s.re → -C ≤ (logDeriv entireXi s).re) ∧
      (∀ (s : ℂ) (rho : NontrivialZetaZero), 1 < s.re →
        ((s-rho.val)⁻¹).re - C ≤ (logDeriv entireXi s).re) := by
  classical
  obtain ⟨B,hB⟩ := zeta_hadamard_factorization
  let C := max (-B.re) 0
  have hC : 0 ≤ C := le_max_right _ _
  have hBC : -C ≤ B.re := by dsimp [C]; linarith [le_max_left (-B.re) 0]
  have hdisjoint (s : ℂ) (hs : 1 < s.re) (rho : NontrivialZetaZero) : s ≠ rho.val := by
    intro he
    rw [he] at hs
    exact (not_lt_of_ge rho.property.1.2.le) hs
  have h₁ (s : ℂ) (hs : 1 < s.re) (rho : NontrivialZetaZero) : 0 ≤ ((s-rho.val)⁻¹).re := by
    rw [Complex.inv_re, Complex.sub_re]
    exact div_nonneg (by linarith [rho.property.1.2]) (Complex.normSq_nonneg _)
  have h₂ (rho : NontrivialZetaZero) : 0 ≤ ((rho.val)⁻¹).re := by
    rw [Complex.inv_re]
    exact div_nonneg rho.property.1.1.le (Complex.normSq_nonneg _)
  have hSum (s : ℂ) (hs : 1 < s.re) :
      HasSum (fun rho : RepeatedZetaZero => ((s-rho.1.val)⁻¹).re + (rho.1.val⁻¹).re)
        (logDeriv (zetaCanonicalProduct) s).re := by
    have h : HasSum (fun rho : RepeatedZetaZero => (s-rho.1.val)⁻¹ + rho.1.val⁻¹)
        (logDeriv zetaCanonicalProduct s) :=
      zetaCanonicalProduct_logDerivative_limit (hdisjoint s hs)
    simpa only [Complex.add_re] using Complex.hasSum_re h
  have hnonneg (s : ℂ) (hs : 1 < s.re) (rho : RepeatedZetaZero) :
      0 ≤ ((s-rho.1.val)⁻¹).re + (rho.1.val⁻¹).re :=
    add_nonneg (h₁ s hs rho.1) (h₂ rho.1)
  refine ⟨C,hC,?_,?_⟩
  · intro s hs
    rw [entireXi_logDerivative_of_hadamard hB (hdisjoint s hs),Complex.add_re,← (hSum s hs).tsum_eq]
    have ht : 0 ≤ ∑' r : RepeatedZetaZero, (((s-r.1.val)⁻¹).re + (r.1.val⁻¹).re) :=
      tsum_nonneg (hnonneg s hs)
    linarith
  · intro s rho hs
    let r : RepeatedZetaZero := ⟨rho, ⟨0,zero_order_positive rho.property.2
      (zeta_nontrivial_zero_finite_order rho).1 (zeta_nontrivial_zero_finite_order rho).2⟩⟩
    have hl := (hSum s hs).summable.sum_le_tsum {r} (fun i _ => hnonneg s hs i)
    rw [Finset.sum_singleton,(hSum s hs).tsum_eq] at hl
    change ((s-rho.val)⁻¹).re + (rho.val⁻¹).re ≤ (logDeriv zetaCanonicalProduct s).re at hl
    rw [entireXi_logDerivative_of_hadamard hB (hdisjoint s hs),Complex.add_re]
    linarith [h₂ rho]

end RHConnections.ZetaZeroFreeRegion
