import Verified
import CoherentEnergyMeasure

noncomputable section
open MeasureTheory

namespace RHConnections.CoherentEnergyMeasure

theorem mertens_eq_M (n : ℕ) :
    mertens n = RHConnections.ArithmeticFourierInversion.M n := by
  unfold mertens RHConnections.ArithmeticFourierInversion.M RHConnections.ArithmeticFourierInversion.muR
  refine Finset.sum_congr rfl fun j _ => ?_
  rfl

theorem scalarS_eq_S (B n : ℕ) :
    scalarS B n = RHConnections.ArithmeticFourierInversion.S B n := by
  rw [RHConnections.ArithmeticFourierInversion.S_from_M]
  unfold scalarS
  have heq : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [heq, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RHConnections.ArithmeticFourierInversion.g_apply, mertens_eq_M]
  split_ifs <;> ring

theorem jWeight_eq_j (r : ℕ) :
    jWeight r = RHConnections.CoherentEnergyBounds.j r := rfl

theorem norm_sq_D_eq_coherent_energy {B : ℕ} (hB : 1 ≤ B) (X : ℕ) :
    ∫ ω, ‖D B X ω‖ ^ 2 ∂primeTorusMeasure =
      RHConnections.CoherentEnergyBounds.energy
        (RHConnections.ArithmeticFourierInversion.S B) B X := by
  rw [norm_sq_D_eq_energy hB X]
  unfold RHConnections.CoherentEnergyBounds.energy RHConnections.CoherentEnergyBounds.indices
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [jWeight_eq_j, scalarS_eq_S]

theorem coherent_energy_measure_growth_iff_RH {B : ℕ} (hB : 1 ≤ B) :
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
        ∀ X : ℕ, 1 ≤ X →
          ∫ ω, ‖D B X ω‖ ^ 2 ∂primeTorusMeasure ≤ C * (X : ℝ) ^ (1 + δ)) ↔
      RiemannHypothesis := by
  simp_rw [norm_sq_D_eq_coherent_energy hB]
  exact RHConnections.ArithmeticFourierInversion.coherent_energy_growth_iff_RH B

theorem fixed_strip_iff_coherent_energy_measure_power {B : ℕ} (hB : 1 ≤ B)
    {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1) :
    (∀ s : ℂ, a < s.re → riemannZeta s ≠ 0) ↔
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
        ∀ X : ℕ, 1 ≤ X →
          ∫ ω, ‖D B X ω‖ ^ 2 ∂primeTorusMeasure ≤ C * (X : ℝ) ^ (2 * a + ε)) := by
  rw [RHConnections.ArithmeticFourierInversion.fixed_strip_iff_fourier_energy_power B ha ha1]
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hBnd⟩ := h ε hε
    refine ⟨C, hC, fun X hX => ?_⟩
    rw [norm_sq_D_eq_coherent_energy hB X]
    exact (le_abs_self _).trans (hBnd X hX)
  · intro h ε hε
    obtain ⟨C, hC, hBnd⟩ := h ε hε
    refine ⟨C, hC, fun X hX => ?_⟩
    have hnn : 0 ≤ RHConnections.CoherentEnergyBounds.energy
        (RHConnections.ArithmeticFourierInversion.S B) B X := by
      rw [← norm_sq_D_eq_coherent_energy hB X]
      exact integral_nonneg fun _ => sq_nonneg _
    rw [abs_of_nonneg hnn, ← norm_sq_D_eq_coherent_energy hB X]
    exact hBnd X hX

end RHConnections.CoherentEnergyMeasure
