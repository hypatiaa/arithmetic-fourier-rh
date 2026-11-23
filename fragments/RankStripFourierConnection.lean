import Verified
import NaturalLongRankStripEquivalence
import FixedStripFourierGrowth

noncomputable section
namespace RHConnections.LongRankPhase
open RHConnections.PhaseWindow RHConnections.ArithmeticFourierInversion
open RHConnections.MertensCriterion

theorem natural_rank_saving_forces_fourier_scalar (hDensity : ZetaDensityPremise)
    {eta delta : ℝ} (he : 0<eta) (he1 : eta<1) (hd : 0<delta) (hd1 : delta≤1/8)
    (hPower : UniformNaturalLongRowPower eta delta) (B : ℕ) :
    ∀ ε : ℝ, 0<ε →
      NaturalPowerBound (S B) (1-delta/(1+(5/2)*((1-eta)/eta))+ε) := by
  let a := 1-delta/(1+(5/2)*((1-eta)/eta))
  have hD : 0<1+(5/2)*((1-eta)/eta) := by positivity
  have hu : 0<delta/(1+(5/2)*((1-eta)/eta)) := div_pos hd hD
  have hupper : delta/(1+(5/2)*((1-eta)/eta))≤1/8 := by
    apply (div_le_iff₀ hD).mpr
    have hpos : 0<((1-eta)/eta) := by positivity
    linarith
  have ha : (1/2:ℝ)≤a := by dsimp [a]; linarith
  have ha1 : a<1 := by dsimp [a]; linarith
  exact (fixed_strip_iff_fourier_scalar_power B ha ha1).mp
    (fun _ hs => uniform_natural_long_row_power_forces_strip hDensity he he1 hd hd1 hPower hs)

theorem natural_rank_power_exists_iff_fourier_scalar (hDensity : ZetaDensityPremise)
    {eta : ℝ} (he : 0<eta) (he1 : eta<1) (B : ℕ) :
    (∃ d : ℝ, 0<d ∧ d≤1/8 ∧ UniformNaturalLongRowPower eta d) ↔
      (∃ b : ℝ, 1/2<b ∧ b<1 ∧ NaturalPowerBound (S B) b) := by
  constructor
  · rintro ⟨d,hd,hd1,hPower⟩
    let u := d/(1+(5/2)*((1-eta)/eta))
    have hD : 0<1+(5/2)*((1-eta)/eta) := by positivity
    have hu : 0<u := div_pos hd hD
    have hupper : u≤1/8 := by
      dsimp [u]
      apply (div_le_iff₀ hD).mpr
      have hpos : 0<((1-eta)/eta) := by positivity
      linarith
    exact ⟨1-u+u/2,by linarith,by linarith,
      natural_rank_saving_forces_fourier_scalar hDensity he he1 hd hd1 hPower B (u/2) (by positivity)⟩
  · rintro ⟨b,hb,hb1,hS⟩
    have hm := (M_power_bound_iff_S B (show 0<b by linarith)).mpr hS
    have hStrip := zero_free_of_natural_mertens_power (show 0≤b by linarith) hb1 hm
    apply (fixed_strip_iff_some_natural_long_row_power hDensity he he1).mp
    refine ⟨1-b,by linarith,?_⟩
    intro s hs
    exact hStrip s (by linarith)

end RHConnections.LongRankPhase
