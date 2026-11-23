import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Complex

namespace RHConnections.CoherentEnergyMeasure

def poissonKernel (ρ θ : ℝ) : ℝ :=
  (1 - ρ ^ 2) / (1 - 2 * ρ * Real.cos θ + ρ ^ 2)

theorem poissonKernel_denom_pos {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (θ : ℝ) :
    0 < 1 - 2 * ρ * Real.cos θ + ρ ^ 2 := by
  have hcos : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have h1 : (1 - ρ) ^ 2 ≤ 1 - 2 * ρ * Real.cos θ + ρ ^ 2 := by nlinarith
  have h2 : 0 < (1 - ρ) ^ 2 := sq_pos_of_pos (sub_pos.mpr hρ1)
  linarith

theorem poissonKernel_pos {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (θ : ℝ) :
    0 < poissonKernel ρ θ :=
  div_pos (sub_pos.mpr (by nlinarith)) (poissonKernel_denom_pos hρ0 hρ1 θ)

theorem poissonKernel_continuous {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Continuous (poissonKernel ρ) :=
  Continuous.div continuous_const
    ((continuous_const.sub (continuous_const.mul Real.continuous_cos)).add continuous_const)
    (fun θ => (poissonKernel_denom_pos hρ0 hρ1 θ).ne')

def poissonTerm (ρ : ℝ) (k : ℕ) (θ : ℝ) : ℂ :=
  (ρ : ℂ) ^ (k + 1) *
    (Complex.exp (Complex.I * ((k + 1 : ℕ) : ℂ) * θ) +
      Complex.exp (-(Complex.I * ((k + 1 : ℕ) : ℂ) * θ)))

private lemma norm_exp_I_mul_real (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  simp

lemma norm_poissonTerm_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (k : ℕ) (θ : ℝ) :
    ‖poissonTerm ρ k θ‖ ≤ 2 * ρ ^ (k + 1) := by
  unfold poissonTerm
  rw [norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ0]
  have h1 : ‖Complex.exp (Complex.I * ((k + 1 : ℕ) : ℂ) * θ)‖ = 1 := by
    have he : Complex.exp (Complex.I * ((k + 1 : ℕ) : ℂ) * θ) =
        Complex.exp (Complex.I * (((k + 1 : ℕ) * θ : ℝ) : ℂ)) := by
      push_cast; ring_nf
    rw [he, norm_exp_I_mul_real]
  have h2 : ‖Complex.exp (-(Complex.I * ((k + 1 : ℕ) : ℂ) * θ))‖ = 1 := by
    have he : Complex.exp (-(Complex.I * ((k + 1 : ℕ) : ℂ) * θ)) =
        Complex.exp (Complex.I * ((-((k + 1 : ℕ) * θ) : ℝ) : ℂ)) := by
      push_cast; ring_nf
    rw [he, norm_exp_I_mul_real]
  have hsum : ‖Complex.exp (Complex.I * ((k + 1 : ℕ) : ℂ) * θ) +
      Complex.exp (-(Complex.I * ((k + 1 : ℕ) : ℂ) * θ))‖ ≤ 2 := by
    calc _ ≤ _ + _ := norm_add_le _ _
      _ = 1 + 1 := by rw [h1, h2]
      _ = 2 := by norm_num
  calc ρ ^ (k + 1) * _ ≤ ρ ^ (k + 1) * 2 :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg hρ0 _)
    _ = 2 * ρ ^ (k + 1) := by ring

theorem poissonKernel_eq_tsum {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (θ : ℝ) :
    (poissonKernel ρ θ : ℂ) = 1 + ∑' k : ℕ, poissonTerm ρ k θ := by
  let z : ℂ := Complex.exp (Complex.I * (θ : ℂ))
  let w₁ : ℂ := (ρ : ℂ) * z
  let w₂ : ℂ := (ρ : ℂ) * z⁻¹
  have hz : ‖z‖ = 1 := norm_exp_I_mul_real θ
  have hzin : ‖z⁻¹‖ = 1 := by rw [norm_inv, hz, inv_one]
  have hw₁_norm : ‖w₁‖ < 1 := by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ0]; exact hρ1
  have hw₂_norm : ‖w₂‖ < 1 := by
    rw [norm_mul, hzin, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ0]; exact hρ1
  have hs₁ : Summable (fun k : ℕ => w₁ ^ k) := summable_geometric_of_norm_lt_one hw₁_norm
  have hs₂ : Summable (fun k : ℕ => w₂ ^ k) := summable_geometric_of_norm_lt_one hw₂_norm
  have hgeom₁ : (1 - w₁)⁻¹ = 1 + ∑' k : ℕ, w₁ ^ (k + 1) := by
    rw [← (hasSum_geometric_of_norm_lt_one hw₁_norm).tsum_eq, hs₁.tsum_eq_zero_add, pow_zero]
  have hgeom₂ : w₂ * (1 - w₂)⁻¹ = ∑' k : ℕ, w₂ ^ (k + 1) := by
    rw [← (hasSum_geometric_of_norm_lt_one hw₂_norm).tsum_eq, ← tsum_mul_left]
    congr 1; ext k; ring
  have hs₁' : Summable (fun k : ℕ => w₁ ^ (k + 1)) := (summable_nat_add_iff 1).mpr hs₁
  have hs₂' : Summable (fun k : ℕ => w₂ ^ (k + 1)) := (summable_nat_add_iff 1).mpr hs₂
  have hterm (k : ℕ) : w₁ ^ (k + 1) + w₂ ^ (k + 1) = poissonTerm ρ k θ := by
    dsimp [w₁, w₂, z, poissonTerm]
    have hzp : Complex.exp (Complex.I * (θ : ℂ)) ^ (k + 1) =
        Complex.exp (Complex.I * ((k + 1 : ℕ) : ℂ) * (θ : ℂ)) := by
      rw [← Complex.exp_nat_mul]; congr 1; ring
    have hzm : (Complex.exp (Complex.I * (θ : ℂ)))⁻¹ ^ (k + 1) =
        Complex.exp (-(Complex.I * ((k + 1 : ℕ) : ℂ) * (θ : ℂ))) := by
      rw [← Complex.exp_neg, ← Complex.exp_nat_mul]; congr 1; ring
    rw [mul_pow, mul_pow, hzp, hzm, mul_add]
  have hsum_eq : (1 - w₁)⁻¹ + w₂ * (1 - w₂)⁻¹ = 1 + ∑' k : ℕ, poissonTerm ρ k θ := by
    rw [hgeom₁, hgeom₂, add_assoc]
    congr 1
    rw [← hs₁'.tsum_add hs₂']
    exact tsum_congr hterm
  have hcos : 2 * (Real.cos θ : ℂ) = z + z⁻¹ := by
    have h1 : z = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
      dsimp [z]
      rw [mul_comm, Complex.exp_mul_I]
      simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have h2 : z⁻¹ = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
      dsimp [z]
      rw [← Complex.exp_neg, show -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_mul_I]
      simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, sub_eq_add_neg]
    linear_combination -h1 - h2
  have hne₁ : 1 - w₁ ≠ 0 := by
    intro h
    have hn : ‖w₁‖ = 1 := by rw [show w₁ = 1 from (sub_eq_zero.mp h).symm, norm_one]
    linarith
  have hne₂ : 1 - w₂ ≠ 0 := by
    intro h
    have hn : ‖w₂‖ = 1 := by rw [show w₂ = 1 from (sub_eq_zero.mp h).symm, norm_one]
    linarith
  have hden : ((1 - 2 * ρ * Real.cos θ + ρ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (poissonKernel_denom_pos hρ0 hρ1 θ).ne'
  have hfact : (1 - w₁) * (1 - w₂) = ((1 - 2 * ρ * Real.cos θ + ρ ^ 2 : ℝ) : ℂ) := by
    dsimp [w₁, w₂]
    have hc : ((1 - 2 * ρ * Real.cos θ + ρ ^ 2 : ℝ) : ℂ) =
        1 - (ρ : ℂ) * (2 * (Real.cos θ : ℂ)) + (ρ : ℂ) ^ 2 := by
      push_cast; ring
    rw [hc, hcos]
    calc (1 - (ρ : ℂ) * z) * (1 - (ρ : ℂ) * z⁻¹)
        = 1 - (ρ : ℂ) * (z + z⁻¹) + (ρ : ℂ) ^ 2 * (z * z⁻¹) := by ring
      _ = 1 - (ρ : ℂ) * (z + z⁻¹) + (ρ : ℂ) ^ 2 := by
          rw [mul_inv_cancel₀ (Complex.exp_ne_zero _), mul_one]
  have h1 : (1 - w₁)⁻¹ + w₂ * (1 - w₂)⁻¹ = (1 - (ρ : ℂ) ^ 2) / ((1 - w₁) * (1 - w₂)) := by
    have hnum : (1 - w₂) + (1 - w₁) * w₂ = 1 - (ρ : ℂ) ^ 2 := by
      dsimp [w₁, w₂]
      calc (1 - (ρ : ℂ) * z⁻¹) + (1 - (ρ : ℂ) * z) * ((ρ : ℂ) * z⁻¹)
          = 1 - (ρ : ℂ) ^ 2 * (z * z⁻¹) := by ring
        _ = 1 - (ρ : ℂ) ^ 2 := by rw [mul_inv_cancel₀ (Complex.exp_ne_zero _), mul_one]
    rw [← hnum]
    field_simp [hne₁, hne₂]
  rw [← hsum_eq, h1, hfact]
  unfold poissonKernel
  push_cast
  rfl

theorem fourier_orthogonality (m : ℤ) :
    ((2 * Real.pi : ℂ)⁻¹) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (Complex.I * (m : ℂ) * θ) =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      sub_zero, Complex.real_smul, mul_one, ↓reduceIte]
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (mul_pos two_pos Real.pi_pos).ne'
    push_cast
    exact inv_mul_cancel₀ hpi
  · simp only [hm, ↓reduceIte]
    let c : ℂ := Complex.I * (m : ℂ)
    have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hm)
    let F : ℝ → ℂ := fun θ => c⁻¹ * Complex.exp (c * (θ : ℂ))
    have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        HasDerivAt F (Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ))) θ := by
      intro θ _
      have hd1 : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c θ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul c
      have hd2 := (Complex.hasDerivAt_exp (c * (θ : ℂ))).comp θ hd1
      have hmul : c⁻¹ * (Complex.exp (c * (θ : ℂ)) * c) = Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) := by
        rw [mul_comm (Complex.exp _), ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      simpa [F, hmul] using hd2.const_mul c⁻¹
    have hint : IntervalIntegrable (fun θ : ℝ => Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ))) volume 0 (2 * Real.pi) :=
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hexp : Complex.exp (c * (2 * (Real.pi : ℂ))) = 1 := by
      have he : c * (2 * (Real.pi : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
        dsimp [c]; ring
      rw [he, Complex.exp_int_mul_two_pi_mul_I]
    simp [F, hexp]

private lemma fourier_orthogonality_Ioc (m : ℤ) :
    ((2 * Real.pi : ℂ)⁻¹) *
        ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), Complex.exp (Complex.I * (m : ℂ) * θ) =
      if m = 0 then 1 else 0 := by
  have hpi0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [← intervalIntegral.integral_of_le hpi0]
  exact fourier_orthogonality m

private def fourierF (ρ : ℝ) (m : ℤ) (k : ℕ) (θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (m : ℂ) * θ) * poissonTerm ρ k θ

private lemma fourierF_continuous (ρ : ℝ) (m : ℤ) (k : ℕ) : Continuous (fourierF ρ m k) := by
  unfold fourierF poissonTerm
  fun_prop

private lemma fourierF_integrable (ρ : ℝ) (m : ℤ) (k : ℕ) :
    Integrable (fourierF ρ m k) (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
  (fourierF_continuous ρ m k).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

private lemma fourier_term_integral (ρ : ℝ) (m : ℤ) (k : ℕ) :
    ((2 * Real.pi : ℂ)⁻¹) *
        ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), fourierF ρ m k θ =
      (ρ : ℂ) ^ (k + 1) *
        ((if m + ((k + 1 : ℕ) : ℤ) = 0 then (1 : ℂ) else 0) +
          (if m - ((k + 1 : ℕ) : ℤ) = 0 then 1 else 0)) := by
  have hsplit : ∀ θ : ℝ, fourierF ρ m k θ =
      (ρ : ℂ) ^ (k + 1) *
        (Complex.exp (Complex.I * ((m + ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * θ) +
          Complex.exp (Complex.I * ((m - ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * θ)) := by
    intro θ
    unfold fourierF poissonTerm
    have h1 : Complex.exp (Complex.I * (m : ℂ) * θ) *
        Complex.exp (Complex.I * ((k + 1 : ℕ) : ℂ) * θ) =
        Complex.exp (Complex.I * ((m + ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * θ) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have h2 : Complex.exp (Complex.I * (m : ℂ) * θ) *
        Complex.exp (-(Complex.I * ((k + 1 : ℕ) : ℂ) * θ)) =
        Complex.exp (Complex.I * ((m - ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * θ) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [mul_left_comm, mul_add, h1, h2]
  have hI1 : Integrable (fun θ : ℝ => Complex.exp (Complex.I * ((m + ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * θ))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hI2 : Integrable (fun θ : ℝ => Complex.exp (Complex.I * ((m - ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * θ))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  simp_rw [hsplit]
  rw [integral_const_mul, integral_add hI1 hI2]
  have fo1 := fourier_orthogonality_Ioc (m + ((k + 1 : ℕ) : ℤ))
  have fo2 := fourier_orthogonality_Ioc (m - ((k + 1 : ℕ) : ℤ))
  calc ((2 * Real.pi : ℂ)⁻¹) * ((ρ : ℂ) ^ (k + 1) *
        ((∫ θ in Set.Ioc 0 (2 * Real.pi), Complex.exp (Complex.I * ((m + ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * θ)) +
         (∫ θ in Set.Ioc 0 (2 * Real.pi), Complex.exp (Complex.I * ((m - ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * θ))))
      = (ρ : ℂ) ^ (k + 1) *
          (((2 * Real.pi : ℂ)⁻¹ * ∫ θ in Set.Ioc 0 (2 * Real.pi), Complex.exp (Complex.I * ((m + ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * θ)) +
           ((2 * Real.pi : ℂ)⁻¹ * ∫ θ in Set.Ioc 0 (2 * Real.pi), Complex.exp (Complex.I * ((m - ((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * θ))) := by ring
    _ = _ := by rw [fo1, fo2]

private lemma fourier_tsum_eval (ρ : ℝ) (m : ℤ) :
    (if m = 0 then (1 : ℂ) else 0) +
      ∑' k : ℕ, (ρ : ℂ) ^ (k + 1) *
        ((if m + ((k + 1 : ℕ) : ℤ) = 0 then (1 : ℂ) else 0) +
          (if m - ((k + 1 : ℕ) : ℤ) = 0 then 1 else 0)) =
      (ρ : ℂ) ^ m.natAbs := by
  by_cases hm0 : m = 0
  · subst hm0
    have hzero : ∀ k : ℕ,
        (ρ : ℂ) ^ (k + 1) * ((if (0 : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 then (1 : ℂ) else 0) +
          (if (0 : ℤ) - ((k + 1 : ℕ) : ℤ) = 0 then 1 else 0)) = 0 := by
      intro k
      split_ifs <;> first | omega | ring
    rw [show (if (0 : ℤ) = 0 then (1 : ℂ) else 0) = 1 from rfl, Int.natAbs_zero, pow_zero,
      tsum_congr hzero, tsum_zero, add_zero]
  · have hpos : 0 < m.natAbs := Int.natAbs_pos.mpr hm0
    have heq_single : ∀ k : ℕ, k ≠ m.natAbs - 1 →
        (ρ : ℂ) ^ (k + 1) * ((if m + ((k + 1 : ℕ) : ℤ) = 0 then (1 : ℂ) else 0) +
          (if m - ((k + 1 : ℕ) : ℤ) = 0 then 1 else 0)) = 0 := by
      intro k hk
      split_ifs <;> first | omega | ring
    have hneq : (if m = 0 then (1 : ℂ) else 0) = 0 := by simp [hm0]
    rw [hneq, zero_add, tsum_eq_single (m.natAbs - 1) heq_single]
    have hkm : m.natAbs - 1 + 1 = m.natAbs := Nat.sub_add_cancel hpos
    rw [hkm]
    split_ifs <;> first | omega | ring

private lemma poisson_fourier_swap {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (m : ℤ) :
    ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ∑' k : ℕ, fourierF ρ m k θ =
      ∑' k : ℕ, ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), fourierF ρ m k θ := by
  have hs_geom : Summable (fun k : ℕ => 2 * ρ ^ (k + 1)) :=
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hρ0 hρ1)).mul_left 2
  have h_F_int : ∀ k : ℕ, Integrable (fourierF ρ m k) (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    fourierF_integrable ρ m
  have h_norm_int_le : ∀ k : ℕ,
      ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ‖fourierF ρ m k θ‖ ≤ (2 * Real.pi) * (2 * ρ ^ (k + 1)) := by
    intro k
    have hpt : ∀ θ : ℝ, ‖fourierF ρ m k θ‖ ≤ 2 * ρ ^ (k + 1) := by
      intro θ
      unfold fourierF
      rw [norm_mul, show ‖Complex.exp (Complex.I * (m : ℂ) * θ)‖ = 1 by
        simpa [mul_assoc] using norm_exp_I_mul_real ((m : ℝ) * θ), one_mul]
      exact norm_poissonTerm_le hρ0 k θ
    calc ∫ θ in Set.Ioc 0 (2 * Real.pi), ‖fourierF ρ m k θ‖
        ≤ ∫ _ in Set.Ioc 0 (2 * Real.pi), (2 * ρ ^ (k + 1)) :=
          integral_mono (h_F_int k).norm (integrable_const _) hpt
      _ = (2 * Real.pi) * (2 * ρ ^ (k + 1)) := by
          rw [integral_const, smul_eq_mul, Measure.real_def, Measure.restrict_apply MeasurableSet.univ,
            Set.univ_inter, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  have h_F_sum : Summable (fun k : ℕ => ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ‖fourierF ρ m k θ‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      h_norm_int_le (hs_geom.mul_left (2 * Real.pi))
  exact (integral_tsum_of_summable_integral_norm h_F_int h_F_sum).symm

theorem poissonKernel_fourier_moment {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (m : ℤ) :
    ((2 * Real.pi : ℂ)⁻¹) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (Complex.I * (m : ℂ) * θ) * (poissonKernel ρ θ : ℂ) =
      (ρ : ℂ) ^ m.natAbs := by
  have hpi0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hs_geom : Summable (fun k : ℕ => 2 * ρ ^ (k + 1)) :=
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hρ0 hρ1)).mul_left 2
  have h_sum_term : ∀ θ : ℝ, Summable (fun k : ℕ => poissonTerm ρ k θ) := fun θ =>
    Summable.of_norm_bounded hs_geom (fun k => norm_poissonTerm_le hρ0 k θ)
  have h_eq : ∀ θ : ℝ,
      Complex.exp (Complex.I * (m : ℂ) * θ) * (poissonKernel ρ θ : ℂ) =
        Complex.exp (Complex.I * (m : ℂ) * θ) + ∑' k : ℕ, fourierF ρ m k θ := by
    intro θ
    rw [poissonKernel_eq_tsum hρ0 hρ1 θ, mul_add, mul_one, ← (h_sum_term θ).tsum_mul_left]
    rfl
  have h_E_cont : Continuous (fun θ : ℝ => Complex.exp (Complex.I * (m : ℂ) * θ)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have h_lhs_cont : Continuous (fun θ : ℝ => Complex.exp (Complex.I * (m : ℂ) * θ) * (poissonKernel ρ θ : ℂ)) :=
    h_E_cont.mul (Complex.continuous_ofReal.comp (poissonKernel_continuous hρ0 hρ1))
  have h_lhs_int : Integrable (fun θ : ℝ => Complex.exp (Complex.I * (m : ℂ) * θ) * (poissonKernel ρ θ : ℂ))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    h_lhs_cont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have h_E_int : Integrable (fun θ : ℝ => Complex.exp (Complex.I * (m : ℂ) * θ))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    h_E_cont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have h_tsum_fun :
      (fun θ : ℝ => ∑' k : ℕ, fourierF ρ m k θ) =
        fun θ : ℝ => Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) * (poissonKernel ρ θ : ℂ) -
          Complex.exp (Complex.I * (m : ℂ) * (θ : ℂ)) := by
    ext θ; exact eq_sub_iff_add_eq'.mpr (h_eq θ).symm
  rw [intervalIntegral.integral_of_le hpi0]
  have hsub := integral_sub h_lhs_int h_E_int
  have hadd : (∫ θ in Set.Ioc 0 (2 * Real.pi), Complex.exp (Complex.I * (m : ℂ) * θ) * (poissonKernel ρ θ : ℂ)) =
      (∫ θ in Set.Ioc 0 (2 * Real.pi), Complex.exp (Complex.I * (m : ℂ) * θ)) +
      (∫ θ in Set.Ioc 0 (2 * Real.pi), ∑' k : ℕ, fourierF ρ m k θ) := by
    rw [h_tsum_fun, hsub, add_sub_cancel]
  rw [hadd, poisson_fourier_swap hρ0 hρ1 m, mul_add, ← tsum_mul_left,
    fourier_orthogonality_Ioc, tsum_congr (fourier_term_integral ρ m), fourier_tsum_eval]

def poissonDensityNN (p : ℕ) (θ : ℝ) : ℝ≥0 :=
  Real.toNNReal ((2 * Real.pi)⁻¹ * poissonKernel ((p : ℝ)⁻¹) θ)

theorem poissonDensityNN_continuous (p : ℕ) (hp : p.Prime) :
    Continuous (poissonDensityNN p) := by
  have h2p : 2 ≤ p := hp.two_le
  have hr0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (show 1 < p by omega))
  exact continuous_real_toNNReal.comp (continuous_const.mul (poissonKernel_continuous hr0 hr1))

theorem poissonDensityNN_coe {p : ℕ} (hp : p.Prime) (θ : ℝ) :
    ((poissonDensityNN p θ : ℝ≥0) : ℝ) = (2 * Real.pi)⁻¹ * poissonKernel ((p : ℝ)⁻¹) θ := by
  have h2p : 2 ≤ p := hp.two_le
  have hr0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (show 1 < p by omega))
  exact Real.coe_toNNReal _ (mul_nonneg (by positivity) (poissonKernel_pos hr0 hr1 θ).le)

def poissonMeasure (p : ℕ) : Measure ℝ :=
  if p.Prime then
    (volume.restrict (Set.Ioc 0 (2 * Real.pi))).withDensity
      (fun θ => (poissonDensityNN p θ : ℝ≥0∞))
  else
    Measure.dirac 0

theorem integral_poissonMeasure_exp {p : ℕ} (hp : p.Prime) (m : ℤ) :
    ∫ θ, Complex.exp (Complex.I * (m : ℂ) * θ) ∂(poissonMeasure p) =
      ((p : ℂ)⁻¹) ^ m.natAbs := by
  simp only [poissonMeasure, hp, ↓reduceIte]
  have hf_meas : Measurable (poissonDensityNN p) := (poissonDensityNN_continuous p hp).measurable
  rw [integral_withDensity_eq_integral_smul hf_meas]
  have hpi0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h_eq : ∀ θ : ℝ,
      (poissonDensityNN p θ) • Complex.exp (Complex.I * (m : ℂ) * θ) =
        ((2 * Real.pi : ℂ)⁻¹) *
          (Complex.exp (Complex.I * (m : ℂ) * θ) * (poissonKernel ((p : ℝ)⁻¹) θ : ℂ)) := by
    intro θ
    rw [NNReal.smul_def, Complex.real_smul, poissonDensityNN_coe hp θ]
    push_cast
    ring
  simp_rw [h_eq]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hpi0]
  have h2p : 2 ≤ p := hp.two_le
  have hr0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (show 1 < p by omega))
  simpa using poissonKernel_fourier_moment hr0 hr1 m

instance poissonMeasure_isProbabilityMeasure (p : ℕ) :
    IsProbabilityMeasure (poissonMeasure p) := by
  by_cases hp : p.Prime
  · constructor
    simp only [poissonMeasure, hp, ↓reduceIte]
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    have h2p : 2 ≤ p := hp.two_le
    have hr0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
    have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (show 1 < p by omega))
    let f : ℝ → ℝ := fun θ => ((poissonDensityNN p θ : ℝ≥0) : ℝ)
    have hf_cont : Continuous f := NNReal.continuous_coe.comp (poissonDensityNN_continuous p hp)
    have hf_int : Integrable f (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
      hf_cont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have hf_nn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 (2 * Real.pi))] f :=
      ae_of_all _ (fun θ => NNReal.coe_nonneg _)
    have h_lint :
        (∫⁻ θ, (poissonDensityNN p θ : ℝ≥0∞) ∂volume.restrict (Set.Ioc 0 (2 * Real.pi))) =
          ENNReal.ofReal (∫ θ, f θ ∂volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
      rw [ofReal_integral_eq_lintegral_ofReal hf_int hf_nn]
      congr 1; ext θ
      exact ENNReal.ofReal_coe_nnreal.symm
    rw [h_lint]
    have hpi0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hm0 := poissonKernel_fourier_moment hr0 hr1 0
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, Int.natAbs_zero,
      pow_zero] at hm0
    have hre : ∫ θ, f θ ∂volume.restrict (Set.Ioc 0 (2 * Real.pi)) = 1 := by
      have hc : (((∫ θ, f θ ∂volume.restrict (Set.Ioc 0 (2 * Real.pi))) : ℝ) : ℂ) = 1 := by
        calc (((∫ θ, f θ ∂volume.restrict (Set.Ioc 0 (2 * Real.pi))) : ℝ) : ℂ)
            = ∫ θ, (f θ : ℂ) ∂volume.restrict (Set.Ioc 0 (2 * Real.pi)) := by
              simpa using (Complex.ofRealCLM.integral_comp_comm hf_int).symm
          _ = ((2 * Real.pi : ℂ)⁻¹) *
                ∫ θ in (0 : ℝ)..(2 * Real.pi), (poissonKernel ((p : ℝ)⁻¹) θ : ℂ) := by
              rw [intervalIntegral.integral_of_le hpi0, ← integral_const_mul]
              congr 1; ext θ
              dsimp [f]
              rw [poissonDensityNN_coe hp θ]
              push_cast; rfl
          _ = 1 := hm0
      exact_mod_cast hc
    rw [hre, ENNReal.ofReal_one]
  · simp only [poissonMeasure, hp, ↓reduceIte]
    infer_instance

def primeTorusMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi poissonMeasure

instance : IsProbabilityMeasure primeTorusMeasure := by
  unfold primeTorusMeasure
  infer_instance

theorem integral_finset_prod_primeTorus (s : Finset ℕ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ p ∈ s, AEStronglyMeasurable (f p) (poissonMeasure p)) :
    ∫ ω, (∏ p ∈ s, f p (ω p)) ∂primeTorusMeasure =
      ∏ p ∈ s, ∫ t, f p t ∂(poissonMeasure p) := by
  let g : (Π _ : s, ℝ) → ℂ := fun y => ∏ p : s, f p.1 (y p)
  have hg_meas : AEStronglyMeasurable g (Measure.pi fun p : s => poissonMeasure p.1) := by
    refine Finset.aestronglyMeasurable_fun_prod _ fun p _ => ?_
    exact (hf p.1 p.2).comp_measurePreserving
      (MeasureTheory.measurePreserving_eval (fun q : s => poissonMeasure q.1) p)
  have hpi := MeasureTheory.integral_restrict_infinitePi (μ := poissonMeasure) (s := s) (f := g) hg_meas
  have hprod : (∫ y, g y ∂Measure.pi fun p : s => poissonMeasure p.1) =
      ∏ p : s, ∫ t, f p.1 t ∂(poissonMeasure p.1) :=
    MeasureTheory.integral_fintype_prod_eq_prod (fun p : s => f p.1)
  have heq : (fun ω : ℕ → ℝ => g (s.restrict ω)) = fun ω => ∏ p ∈ s, f p (ω p) := by
    ext ω
    dsimp [g, Finset.restrict]
    exact Finset.prod_attach s (fun p => f p (ω p))
  unfold primeTorusMeasure
  rw [← heq, hpi, hprod]
  exact Finset.prod_attach s (fun p => ∫ t, f p t ∂(poissonMeasure p))

def phasor (p : ℕ) (ω : ℕ → ℝ) : ℂ :=
  Complex.exp (Complex.I * (ω p : ℂ))

def Z (n : ℕ) (ω : ℕ → ℝ) : ℂ :=
  ∏ p ∈ n.primeFactors, phasor p ω ^ n.factorization p

@[simp] theorem Z_one (ω : ℕ → ℝ) : Z 1 ω = 1 := by
  simp [Z]

theorem Z_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (ω : ℕ → ℝ) :
    Z (m * n) ω = Z m ω * Z n ω := by
  unfold Z
  rw [Nat.primeFactors_mul hm hn]
  have hm_eq : ∏ p ∈ m.primeFactors, phasor p ω ^ m.factorization p =
      ∏ p ∈ m.primeFactors ∪ n.primeFactors, phasor p ω ^ m.factorization p := by
    refine Finset.prod_subset Finset.subset_union_left fun p _ hp => ?_
    have hz : m.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
    simp [hz]
  have hn_eq : ∏ p ∈ n.primeFactors, phasor p ω ^ n.factorization p =
      ∏ p ∈ m.primeFactors ∪ n.primeFactors, phasor p ω ^ n.factorization p := by
    refine Finset.prod_subset Finset.subset_union_right fun p _ hp => ?_
    have hz : n.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
    simp [hz]
  rw [hm_eq, hn_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Nat.factorization_mul hm hn, Finsupp.coe_add, Pi.add_apply, pow_add]

@[simp] theorem Z_prime_pow {p k : ℕ} (hp : p.Prime) (ω : ℕ → ℝ) :
    Z (p ^ k) ω = phasor p ω ^ k := by
  by_cases hk : k = 0
  · subst hk; simp
  · unfold Z
    rw [Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton, hp.factorization_pow,
      Finsupp.single_eq_same]

def divisorLift (N : ℕ) (ω : ℕ → ℝ) : ℂ :=
  ∑ d ∈ N.divisors, Z d ω

def mobiusLift (N : ℕ) (ω : ℕ → ℝ) : ℂ :=
  ∑ d ∈ N.divisors, (ArithmeticFunction.moebius (N / d) : ℂ) * Z d ω

private def ZArith (ω : ℕ → ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else Z n ω, by simp⟩

private theorem ZArith_isMultiplicative (ω : ℕ → ℝ) : (ZArith ω).IsMultiplicative := by
  refine ⟨by simp [ZArith], fun {m n} _ => ?_⟩
  by_cases hm : m = 0
  · subst hm; simp [ZArith]
  · by_cases hn : n = 0
    · subst hn; simp [ZArith]
    · simp [ZArith, hm, hn, mul_ne_zero hm hn, Z_mul hm hn ω]

private theorem mobiusLift_eq_ZArith_mul {N : ℕ} (hN : N ≠ 0) (ω : ℕ → ℝ) :
    mobiusLift N ω = (ZArith ω * (↑ArithmeticFunction.moebius : ArithmeticFunction ℂ)) N := by
  unfold mobiusLift
  rw [mul_comm (ZArith ω), ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (f := fun x y => ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) x) * ZArith ω y)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hN (Nat.dvd_of_mem_divisors hd)
  simp [ZArith, hd0]

theorem mobiusLift_eq_prod {N : ℕ} (hN : N ≠ 0) (ω : ℕ → ℝ) :
    mobiusLift N ω = ∏ p ∈ N.primeFactors, phasor p ω ^ (N.factorization p - 1) * (phasor p ω - 1) := by
  let F : ArithmeticFunction ℂ := ZArith ω * (↑ArithmeticFunction.moebius : ArithmeticFunction ℂ)
  have hF : F.IsMultiplicative :=
    (ZArith_isMultiplicative ω).mul ArithmeticFunction.isMultiplicative_moebius.intCast
  have hpair : (N.primeFactors : Set ℕ).Pairwise
      (fun p q => Nat.Coprime (p ^ N.factorization p) (q ^ N.factorization q)) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  rw [mobiusLift_eq_ZArith_mul hN ω]
  change F N = _
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hN, hF.map_prod _ _ hpair]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hk_pos : 0 < N.factorization p := hprime.factorization_pos_of_dvd hN (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
  have hpk0 : p ^ N.factorization p ≠ 0 := pow_ne_zero _ hprime.ne_zero
  rw [← mobiusLift_eq_ZArith_mul hpk0 ω, hm]
  simp only [mobiusLift, Nat.sum_divisors_prime_pow hprime]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∑ i ∈ Finset.range m, (ArithmeticFunction.moebius (p ^ (m + 1) / p ^ i) : ℂ) * Z (p ^ i) ω = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have him : i < m := Finset.mem_range.mp hi
    have hdiv : p ^ (m + 1) / p ^ i = p ^ (m + 1 - i) := by
      rw [Nat.pow_div (by omega) hprime.pos]
    rw [hdiv, ArithmeticFunction.moebius_apply_prime_pow hprime (by omega)]
    have hge : m + 1 - i ≠ 1 := by omega
    simp [hge]
  have hp1 : p ^ (m + 1) / p ^ (m + 1) = 1 := Nat.div_self (pow_pos hprime.pos _)
  have hpm : p ^ (m + 1) / p ^ m = p := by
    rw [Nat.pow_div (Nat.le_succ m) hprime.pos, show m.succ - m = 1 by omega, pow_one]
  rw [hzero, zero_add, hp1, hpm]
  simp only [ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hprime,
    Int.cast_one, Int.cast_neg, Z_prime_pow hprime]
  rw [show m.succ - 1 = m by omega]
  ring

def rad (B : ℕ) : ℕ := ∏ p ∈ B.primeFactors, p

theorem rad_pos {B : ℕ} (_hB : 1 ≤ B) : 0 < rad B := by
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

theorem coprime_rad_iff {n B : ℕ} (hB : 1 ≤ B) :
    Nat.Coprime n (rad B) ↔ Nat.Coprime n B := by
  have hB0 : B ≠ 0 := by omega
  rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one]
  constructor
  · intro h
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpn : p ∣ n := hpd.trans (Nat.gcd_dvd_left n B)
    have hpB : p ∣ B := hpd.trans (Nat.gcd_dvd_right n B)
    have hmem : p ∈ B.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpB, hB0⟩
    have hpr : p ∣ rad B := Finset.dvd_prod_of_mem _ hmem
    exact hp.not_dvd_one (h ▸ Nat.dvd_gcd hpn hpr)
  · intro h
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpn : p ∣ n := hpd.trans (Nat.gcd_dvd_left n (rad B))
    have hpr : p ∣ rad B := hpd.trans (Nat.gcd_dvd_right n (rad B))
    have hmem : p ∈ B.primeFactors := by
      have : ∃ q ∈ B.primeFactors, p ∣ q := (hp.prime.dvd_finsetProd_iff _).mp hpr
      obtain ⟨q, hq, hpq⟩ := this
      have hq_prime := Nat.prime_of_mem_primeFactors hq
      rwa [(Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq]
    have hpB : p ∣ B := Nat.dvd_of_mem_primeFactors hmem
    exact hp.not_dvd_one (h ▸ Nat.dvd_gcd hpn hpB)

def sievingWindow (B X n : ℕ) : ℝ :=
  ∑ b ∈ (rad B).divisors, if n ≤ X / b then (ArithmeticFunction.moebius b : ℝ) else 0

theorem sievingWindow_91 (X n : ℕ) :
    sievingWindow 91 X n =
      (if X / 7 < n ∧ n ≤ X then (1 : ℝ) else 0) -
        (if X / 91 < n ∧ n ≤ X / 13 then 1 else 0) := by
  have h7 : Nat.Prime 7 := by norm_num
  have h13 : Nat.Prime 13 := by norm_num
  have h91_eq : (91 : ℕ) = 7 * 13 := by norm_num
  have hpf : (91 : ℕ).primeFactors = {7, 13} := by
    rw [h91_eq, Nat.primeFactors_mul (by norm_num) (by norm_num), h7.primeFactors, h13.primeFactors]
    rfl
  have hrad : rad 91 = 91 := by
    unfold rad
    rw [hpf, Finset.prod_pair (by norm_num)]
    norm_num
  have hdiv : (91 : ℕ).divisors = {1, 7, 13, 91} := by decide
  have hμ1 : ArithmeticFunction.moebius 1 = 1 := ArithmeticFunction.moebius_apply_one
  have hμ7 : ArithmeticFunction.moebius 7 = -1 := ArithmeticFunction.moebius_apply_prime h7
  have hμ13 : ArithmeticFunction.moebius 13 = -1 := ArithmeticFunction.moebius_apply_prime h13
  have hμ91 : ArithmeticFunction.moebius 91 = 1 := by
    rw [h91_eq, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.moebius_apply_prime h7, ArithmeticFunction.moebius_apply_prime h13]
    ring
  unfold sievingWindow
  rw [hrad, hdiv]
  simp only [Finset.mem_insert, Finset.mem_singleton, OfNat.one_ne_ofNat,
    Nat.reduceEqDiff, or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton,
    hμ1, hμ7, hμ13, hμ91, Int.cast_one, Int.cast_neg, Nat.div_one]
  have h1 : X / 91 ≤ X / 13 := Nat.div_le_div_left (by omega) (by omega)
  have h2 : X / 91 ≤ X / 7 := Nat.div_le_div_left (by omega) (by omega)
  have h13_7 : X / 13 ≤ X / 7 := Nat.div_le_div_left (by omega) (by omega)
  have h3 : X / 13 ≤ X := Nat.div_le_self X 13
  have h4 : X / 7 ≤ X := Nat.div_le_self X 7
  rcases le_or_gt n (X / 91) with h91 | h91
  · have h13 : n ≤ X / 13 := h91.trans h1
    have h7 : n ≤ X / 7 := h91.trans h2
    have hX : n ≤ X := h13.trans h3
    have hn7 : ¬ (X / 7 < n ∧ n ≤ X) := fun h => not_le_of_gt h.1 h7
    have hn13 : ¬ (X / 91 < n ∧ n ≤ X / 13) := fun h => not_le_of_gt h.1 h91
    rw [ite_eq_left hX, ite_eq_left h7, ite_eq_left h13, ite_eq_left h91,
      ite_eq_right hn7, ite_eq_right hn13]
    norm_num
  · rcases le_or_gt n (X / 13) with h13 | h13
    · have hn91 : ¬ n ≤ X / 91 := not_le_of_gt h91
      have h7 : n ≤ X / 7 := h13.trans h13_7
      have hX : n ≤ X := h13.trans h3
      have hn7 : ¬ (X / 7 < n ∧ n ≤ X) := fun h => not_le_of_gt h.1 h7
      have hb13 : X / 91 < n ∧ n ≤ X / 13 := ⟨h91, h13⟩
      rw [ite_eq_left hX, ite_eq_left h7, ite_eq_left h13, ite_eq_right hn91,
        ite_eq_right hn7, ite_eq_left hb13]
      norm_num
    · rcases le_or_gt n (X / 7) with h7 | h7
      · have hn91 : ¬ n ≤ X / 91 := not_le_of_gt (lt_of_le_of_lt h1 h13)
        have hn13 : ¬ n ≤ X / 13 := not_le_of_gt h13
        have hX : n ≤ X := h7.trans h4
        have hn7 : ¬ (X / 7 < n ∧ n ≤ X) := fun h => not_le_of_gt h.1 h7
        have hb13 : ¬ (X / 91 < n ∧ n ≤ X / 13) := fun h => hn13 h.2
        rw [ite_eq_left hX, ite_eq_left h7, ite_eq_right hn13, ite_eq_right hn91,
          ite_eq_right hn7, ite_eq_right hb13]
        norm_num
      · rcases le_or_gt n X with hX | hX
        · have hn91 : ¬ n ≤ X / 91 := not_le_of_gt (lt_of_le_of_lt h2 h7)
          have hn13 : ¬ n ≤ X / 13 := not_le_of_gt (lt_of_le_of_lt h13_7 h7)
          have hn7 : ¬ n ≤ X / 7 := not_le_of_gt h7
          have hbX : X / 7 < n ∧ n ≤ X := ⟨h7, hX⟩
          have hb13 : ¬ (X / 91 < n ∧ n ≤ X / 13) := fun h => hn13 h.2
          rw [ite_eq_left hX, ite_eq_right hn7, ite_eq_right hn13, ite_eq_right hn91,
            ite_eq_left hbX, ite_eq_right hb13]
          norm_num
        · have hnX : ¬ n ≤ X := not_le_of_gt hX
          have hn7 : ¬ n ≤ X / 7 := not_le_of_gt (lt_of_le_of_lt h4 hX)
          have hn13 : ¬ n ≤ X / 13 := not_le_of_gt (lt_of_le_of_lt h3 hX)
          have hn91 : ¬ n ≤ X / 91 := not_le_of_gt (lt_of_le_of_lt (h1.trans h3) hX)
          have hbX : ¬ (X / 7 < n ∧ n ≤ X) := fun h => hnX h.2
          have hb13 : ¬ (X / 91 < n ∧ n ≤ X / 13) := fun h => hn13 h.2
          rw [ite_eq_right hnX, ite_eq_right hn7, ite_eq_right hn13, ite_eq_right hn91,
            ite_eq_right hbX, ite_eq_right hb13]
          norm_num

def D (B X : ℕ) (ω : ℕ → ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 X).filter (fun n => Nat.Coprime n B),
    (sievingWindow B X n : ℂ) * mobiusLift n ω

def mertens (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc 0 n, (ArithmeticFunction.moebius j : ℝ)

private lemma rad_factorization_prod {R k : ℕ} (hR : Squarefree R) (hk : 1 ≤ k) :
    (∑ b ∈ R.divisors, ∑ m ∈ Finset.Ioc 0 k,
        if m.Coprime R ∧ b * m = k then
          (ArithmeticFunction.moebius b : ℂ) * (ArithmeticFunction.moebius m : ℂ)
        else 0) = (ArithmeticFunction.moebius k : ℂ) := by
  have hk0 : k ≠ 0 := by omega
  have hR0 : R ≠ 0 := hR.ne_zero
  by_cases hsq : Squarefree k
  · let b₀ := k.gcd R
    let m₀ := k / b₀
    have hb₀_dvd_k : b₀ ∣ k := Nat.gcd_dvd_left k R
    have hb₀_dvd_R : b₀ ∣ R := Nat.gcd_dvd_right k R
    have hm₀_eq : b₀ * m₀ = k := Nat.mul_div_cancel' hb₀_dvd_k
    have hb₀_pos : 0 < b₀ := Nat.gcd_pos_of_pos_left R (by omega)
    have hm₀_pos : 0 < m₀ := by
      by_contra h0
      have hm0 : m₀ = 0 := Nat.eq_zero_of_le_zero (not_lt.mp h0)
      rw [hm0, mul_zero] at hm₀_eq
      exact hk0 hm₀_eq.symm
    have hm₀_le : m₀ ≤ k := Nat.div_le_self k b₀
    have hcop_b₀m₀ : Nat.Coprime b₀ m₀ := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hp2 : p * p ∣ k :=
        hm₀_eq ▸ Nat.mul_dvd_mul (hpd.trans (Nat.gcd_dvd_left b₀ m₀)) (hpd.trans (Nat.gcd_dvd_right b₀ m₀))
      exact hp.ne_one (Nat.isUnit_iff.mp (hsq p hp2))
    have hcop_m₀R : Nat.Coprime m₀ R := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hpm : p ∣ m₀ := hpd.trans (Nat.gcd_dvd_left m₀ R)
      have hpR : p ∣ R := hpd.trans (Nat.gcd_dvd_right m₀ R)
      have hpb : p ∣ b₀ := Nat.dvd_gcd (hpm.trans (Dvd.intro_left b₀ hm₀_eq)) hpR
      exact hp.not_dvd_one (hcop_b₀m₀ ▸ Nat.dvd_gcd hpb hpm)
    have hb₀_mem : b₀ ∈ R.divisors := Nat.mem_divisors.mpr ⟨hb₀_dvd_R, hR0⟩
    have hm₀_mem : m₀ ∈ Finset.Ioc 0 k := Finset.mem_Ioc.mpr ⟨hm₀_pos, hm₀_le⟩
    rw [Finset.sum_eq_single b₀]
    · rw [Finset.sum_eq_single m₀]
      · rw [ite_eq_left ⟨hcop_m₀R, hm₀_eq⟩]
        exact_mod_cast (by
          rw [← ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_b₀m₀, hm₀_eq] :
          ArithmeticFunction.moebius b₀ * ArithmeticFunction.moebius m₀ = ArithmeticFunction.moebius k)
      · intro m _ hm_ne
        have hnot : ¬ (m.Coprime R ∧ b₀ * m = k) := by
          rintro ⟨_, hbm⟩
          exact hm_ne (Nat.eq_of_mul_eq_mul_left hb₀_pos (hbm.trans hm₀_eq.symm))
        rw [ite_eq_right hnot]
      · intro hm_nmem; exact absurd hm₀_mem hm_nmem
    · intro b hb hb_ne
      refine Finset.sum_eq_zero fun m _ => ?_
      have hnot : ¬ (m.Coprime R ∧ b * m = k) := by
        rintro ⟨hmR, hbm⟩
        have hb_dvd : b ∣ R := (Nat.mem_divisors.mp hb).1
        have hgcd : k.gcd R = b := by
          apply Nat.dvd_antisymm
          · have hdiv_bm : k.gcd R ∣ b * m := hbm ▸ Nat.gcd_dvd_left k R
            have hcop_gm : Nat.Coprime (k.gcd R) m :=
              (hmR.coprime_dvd_right (Nat.gcd_dvd_right k R)).symm
            exact hcop_gm.dvd_of_dvd_mul_right hdiv_bm
          · exact Nat.dvd_gcd (hbm ▸ dvd_mul_right b m) hb_dvd
        exact hb_ne hgcd.symm
      rw [ite_eq_right hnot]
    · intro hb_nmem; exact absurd hb₀_mem hb_nmem
  · have hμ0 : ArithmeticFunction.moebius k = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    rw [hμ0, Int.cast_zero]
    refine Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun m _ => ?_
    split_ifs with h
    · obtain ⟨hmR, hbm⟩ := h
      have hbR : b ∣ R := (Nat.mem_divisors.mp hb).1
      have hcop : Nat.Coprime b m := hmR.symm.coprime_dvd_left hbR
      have : (ArithmeticFunction.moebius b : ℂ) * (ArithmeticFunction.moebius m : ℂ) =
          (ArithmeticFunction.moebius (b * m) : ℂ) := by
        exact_mod_cast (ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop).symm
      rw [this, hbm, hμ0, Int.cast_zero]
    · rfl

private lemma rad_squarefree (B : ℕ) : Squarefree (rad B) := by
  unfold rad
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hp2
  have h1 : p ∣ ∏ q ∈ B.primeFactors, q := dvd_trans (dvd_mul_right p p) hp2
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp h1
  have hqp : p = q := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)).mp hpq
  subst hqp
  have hrest : p ∣ ∏ r ∈ B.primeFactors.erase p, r := by
    have hmul : ∏ r ∈ B.primeFactors, r = p * ∏ r ∈ B.primeFactors.erase p, r :=
      (Finset.mul_prod_erase B.primeFactors _ hq).symm
    rw [hmul] at hp2
    exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hp2
  obtain ⟨r, hr, hpr⟩ := (hp.prime.dvd_finsetProd_iff _).mp hrest
  have hrp := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hr).2)).mp hpr
  exact (Finset.mem_erase.mp hr).1 hrp.symm

theorem D_eq_mertens_sum {B : ℕ} (hB : 1 ≤ B) (X : ℕ) (ω : ℕ → ℝ) :
    D B X ω =
      ∑ d ∈ (Finset.Icc 1 X).filter (fun d => Nat.Coprime d B),
        (mertens (X / d) : ℂ) * Z d ω := by
  let R := rad B
  have hR_sq : Squarefree R := rad_squarefree B
  have hR_pos : 0 < R := rad_pos hB
  let u : ArithmeticFunction ℂ :=
    ⟨fun d => if d = 0 then 0 else if d.Coprime B then Z d ω else 0, by simp⟩
  let v : ArithmeticFunction ℂ :=
    ⟨fun m => if m = 0 then 0 else if m.Coprime B then (ArithmeticFunction.moebius m : ℂ) else 0, by simp⟩
  have huv_apply : ∀ n : ℕ, 1 ≤ n →
      (u * v) n = if n.Coprime B then mobiusLift n ω else 0 := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    rw [mul_comm u v, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal' (f := fun x y => v x * u y)]
    by_cases hcn : n.Coprime B
    · rw [ite_eq_left hcn]
      unfold mobiusLift
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd_dvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn0 hd_dvd
      have hnd0 : n / d ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨hd0, Nat.le_of_dvd (by omega) hd_dvd⟩
      have hcd : d.Coprime B := hcn.coprime_dvd_left hd_dvd
      have hcnd : (n / d).Coprime B := hcn.coprime_dvd_left (Nat.div_dvd_of_dvd hd_dvd)
      dsimp [u, v]
      rw [ite_eq_right hnd0, ite_eq_left hcnd, ite_eq_right hd0, ite_eq_left hcd]
    · rw [ite_eq_right hcn]
      refine Finset.sum_eq_zero fun d hd => ?_
      have hd_dvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      by_cases hcd : d.Coprime B
      · have hnd_ncop : ¬ (n / d).Coprime B := by
          intro hcnd
          have hmul : d * (n / d) = n := Nat.mul_div_cancel' hd_dvd
          exact hcn (hmul ▸ hcd.mul_left hcnd)
        by_cases hnd0 : n / d = 0
        · simp [u, v, hnd0]
        · dsimp [u, v]; rw [ite_eq_right hnd0, ite_eq_right hnd_ncop, zero_mul]
      · by_cases hd0 : d = 0
        · simp [u, v, hd0]
        · dsimp [u, v]; rw [ite_eq_right hd0, ite_eq_right hcd, mul_zero]
  have hD_swap :
      D B X ω = ∑ b ∈ R.divisors, (ArithmeticFunction.moebius b : ℂ) *
        ∑ n ∈ Finset.Ioc 0 (X / b), (u * v) n := by
    unfold D sievingWindow
    simp_rw [Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hsplit :
        (∑ n ∈ Finset.Icc 1 X,
            (if n ≤ X / b then (ArithmeticFunction.moebius b : ℂ) else 0) * mobiusLift n ω *
              (if n.Coprime B then (1 : ℂ) else 0)) =
          ∑ n ∈ Finset.Ioc 0 (X / b),
            (ArithmeticFunction.moebius b : ℂ) * (u * v) n := by
      have hX_le : X / b ≤ X := Nat.div_le_self X b
      have heq_set : Finset.Ioc 0 (X / b) = (Finset.Icc 1 X).filter (fun n => n ≤ X / b) := by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]; omega
      rw [heq_set, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [huv_apply n hn1]
      split_ifs <;> ring
    rw [Finset.sum_filter]
    trans ∑ n ∈ Finset.Icc 1 X,
        (if n ≤ X / b then (ArithmeticFunction.moebius b : ℂ) else 0) * mobiusLift n ω *
          (if n.Coprime B then (1 : ℂ) else 0)
    · refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hc : n.Coprime B <;> by_cases hnb : n ≤ X / b <;> simp [hc, hnb, mul_comm]
    · exact hsplit
  rw [hD_swap]
  have hhyper : ∀ b ∈ R.divisors,
      (∑ n ∈ Finset.Ioc 0 (X / b), (u * v) n) =
        ∑ d ∈ Finset.Ioc 0 X, u d * ∑ m ∈ Finset.Ioc 0 ((X / d) / b), v m := by
    intro b hb
    have hb_pos : 0 < b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 hR_pos
    rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum u v (X / b)]
    have hX_le : X / b ≤ X := Nat.div_le_self X b
    symm
    rw [← Finset.sum_subset (Finset.Ioc_subset_Ioc_right hX_le)]
    · refine Finset.sum_congr rfl fun d hd => ?_
      have hd_pos : 0 < d := (Finset.mem_Ioc.mp hd).1
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm b d]
    · intro d hd hd_nmem
      have hd_pos : 0 < d := (Finset.mem_Ioc.mp hd).1
      have hgt : X / b < d := by
        simp only [Finset.mem_Ioc, not_and, not_le] at hd_nmem
        exact hd_nmem hd_pos
      have hzero_div : (X / d) / b = 0 := by
        rw [Nat.div_div_eq_div_mul, mul_comm d b, ← Nat.div_div_eq_div_mul]
        exact Nat.div_eq_of_lt hgt
      rw [hzero_div, Finset.Ioc_eq_empty_of_le (le_refl 0), Finset.sum_empty, mul_zero]
  have h1 :
      (∑ b ∈ R.divisors, (ArithmeticFunction.moebius b : ℂ) * ∑ n ∈ Finset.Ioc 0 (X / b), (u * v) n) =
        ∑ d ∈ Finset.Ioc 0 X, u d *
          ∑ b ∈ R.divisors, (ArithmeticFunction.moebius b : ℂ) * ∑ m ∈ Finset.Ioc 0 ((X / d) / b), v m := by
    trans ∑ b ∈ R.divisors, ∑ d ∈ Finset.Ioc 0 X,
        (ArithmeticFunction.moebius b : ℂ) * (u d * ∑ m ∈ Finset.Ioc 0 ((X / d) / b), v m)
    · refine Finset.sum_congr rfl fun b hb => ?_
      rw [hhyper b hb, Finset.mul_sum]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => by ring
  rw [h1]
  have h_Ioc_eq_Icc : Finset.Ioc 0 X = Finset.Icc 1 X := by ext d; simp; omega
  rw [h_Ioc_eq_Icc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_pos : 0 < d := (Finset.mem_Icc.mp hd).1
  by_cases hdc : d.Coprime B
  · have hud : u d = Z d ω := by simp [u, hd_pos.ne', hdc]
    rw [ite_eq_left hdc, hud, mul_comm (Z d ω)]
    congr 1
    unfold mertens
    rw [Complex.ofReal_sum]
    have hinner :
        (∑ b ∈ R.divisors, (ArithmeticFunction.moebius b : ℂ) * ∑ m ∈ Finset.Ioc 0 ((X / d) / b), v m) =
          ∑ k ∈ Finset.Ioc 0 (X / d),
            ∑ b ∈ R.divisors, ∑ m ∈ Finset.Ioc 0 k,
              if m.Coprime R ∧ b * m = k then
                (ArithmeticFunction.moebius b : ℂ) * (ArithmeticFunction.moebius m : ℂ)
              else 0 := by
      have hL_box :
          (∑ b ∈ R.divisors, (ArithmeticFunction.moebius b : ℂ) * ∑ m ∈ Finset.Ioc 0 ((X / d) / b), v m) =
            ∑ b ∈ R.divisors, ∑ m ∈ Finset.Ioc 0 (X / d),
              if b * m ≤ X / d ∧ m.Coprime R then
                (ArithmeticFunction.moebius b : ℂ) * (ArithmeticFunction.moebius m : ℂ)
              else 0 := by
        refine Finset.sum_congr rfl fun b hb => ?_
        have hb_pos : 0 < b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 hR_pos
        rw [Finset.mul_sum]
        have hsub : Finset.Ioc 0 ((X / d) / b) ⊆ Finset.Ioc 0 (X / d) :=
          Finset.Ioc_subset_Ioc_right (Nat.div_le_self _ b)
        rw [← Finset.sum_subset hsub]
        · refine Finset.sum_congr rfl fun m hm => ?_
          have hm_pos : 0 < m := (Finset.mem_Ioc.mp hm).1
          have hm_le : m ≤ (X / d) / b := (Finset.mem_Ioc.mp hm).2
          have hbm_le : b * m ≤ X / d := by
            calc b * m = m * b := mul_comm b m
              _ ≤ X / d := (Nat.le_div_iff_mul_le hb_pos).mp hm_le
          have hmB_iff : m.Coprime R ↔ m.Coprime B := coprime_rad_iff hB
          by_cases hmR : m.Coprime R
          · have hmB : m.Coprime B := hmB_iff.mp hmR
            dsimp [v]
            rw [ite_eq_right hm_pos.ne', ite_eq_left hmB, ite_eq_left ⟨hbm_le, hmR⟩]
          · have hmB : ¬ m.Coprime B := fun h => hmR (hmB_iff.mpr h)
            dsimp [v]
            rw [ite_eq_right hm_pos.ne', ite_eq_right hmB, mul_zero, ite_eq_right (fun h => hmR h.2)]
        · intro m hm hm_nmem
          have hm_pos : 0 < m := (Finset.mem_Ioc.mp hm).1
          have hngt : ¬ (b * m ≤ X / d) := by
            intro hbm_le
            apply hm_nmem
            refine Finset.mem_Ioc.mpr ⟨hm_pos, (Nat.le_div_iff_mul_le hb_pos).mpr ?_⟩
            linarith
          simp [hngt]
      have hR_box :
          (∑ k ∈ Finset.Ioc 0 (X / d),
              ∑ b ∈ R.divisors, ∑ m ∈ Finset.Ioc 0 k,
                if m.Coprime R ∧ b * m = k then
                  (ArithmeticFunction.moebius b : ℂ) * (ArithmeticFunction.moebius m : ℂ)
                else 0) =
            ∑ b ∈ R.divisors, ∑ m ∈ Finset.Ioc 0 (X / d),
              if b * m ≤ X / d ∧ m.Coprime R then
                (ArithmeticFunction.moebius b : ℂ) * (ArithmeticFunction.moebius m : ℂ)
              else 0 := by
        have hbox :
            (∑ k ∈ Finset.Ioc 0 (X / d),
                ∑ b ∈ R.divisors, ∑ m ∈ Finset.Ioc 0 k,
                  if m.Coprime R ∧ b * m = k then
                    (ArithmeticFunction.moebius b : ℂ) * (ArithmeticFunction.moebius m : ℂ)
                  else 0) =
              ∑ k ∈ Finset.Ioc 0 (X / d),
                ∑ b ∈ R.divisors, ∑ m ∈ Finset.Ioc 0 (X / d),
                  if m.Coprime R ∧ b * m = k then
                    (ArithmeticFunction.moebius b : ℂ) * (ArithmeticFunction.moebius m : ℂ)
                  else 0 := by
          refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun b hb => ?_
          have hk_le : k ≤ X / d := (Finset.mem_Ioc.mp hk).2
          have hb_pos : 0 < b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 hR_pos
          refine Finset.sum_subset (Finset.Ioc_subset_Ioc_right hk_le) fun m hm hm_nmem => ?_
          have hm_pos : 0 < m := (Finset.mem_Ioc.mp hm).1
          have hnot : ¬ (m.Coprime R ∧ b * m = k) := by
            rintro ⟨_, hbm⟩
            apply hm_nmem
            refine Finset.mem_Ioc.mpr ⟨hm_pos, ?_⟩
            nlinarith
          rw [ite_eq_right hnot]
        rw [hbox, Finset.sum_comm]
        refine Finset.sum_congr rfl fun b hb => ?_
        have hb_pos : 0 < b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 hR_pos
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm_pos : 0 < m := (Finset.mem_Ioc.mp hm).1
        by_cases hbm_le : b * m ≤ X / d
        · by_cases hmR : m.Coprime R
          · have hmem : b * m ∈ Finset.Ioc 0 (X / d) := Finset.mem_Ioc.mpr ⟨Nat.mul_pos hb_pos hm_pos, hbm_le⟩
            rw [Finset.sum_eq_single (b * m)]
            · simp [hmR, hbm_le]
            · intro k _ hkne; simp [hmR, hkne.symm]
            · intro hk_nmem; exact absurd hmem hk_nmem
          · simp [hmR]
        · have hzero : ∀ k ∈ Finset.Ioc 0 (X / d),
              (if m.Coprime R ∧ b * m = k then
                (ArithmeticFunction.moebius b : ℂ) * (ArithmeticFunction.moebius m : ℂ)
              else 0) = 0 := by
            intro k hk
            have hnot : ¬ (m.Coprime R ∧ b * m = k) := by
              rintro ⟨_, rfl⟩
              exact hbm_le (Finset.mem_Ioc.mp hk).2
            rw [ite_eq_right hnot]
          rw [Finset.sum_eq_zero hzero, ite_eq_right (fun h => hbm_le h.1)]
      exact hL_box.trans hR_box.symm
    rw [hinner]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact rad_factorization_prod hR_sq (Finset.mem_Ioc.mp hk).1
  · have hud : u d = 0 := by simp [u, hd_pos.ne', hdc]
    simp [hdc, hud]

def innerNu (F G : (ℕ → ℝ) → ℂ) : ℂ :=
  ∫ ω, F ω * starRingEnd ℂ (G ω) ∂primeTorusMeasure

private def localExpDiff (d e p : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((d.factorization p : ℤ) - (e.factorization p : ℤ) : ℤ) : ℂ) * (t : ℂ))

private lemma conj_exp_I_mul_int (m : ℤ) (t : ℝ) :
    starRingEnd ℂ (Complex.exp (Complex.I * (m : ℂ) * (t : ℂ))) =
      Complex.exp (Complex.I * ((-m : ℤ) : ℂ) * (t : ℂ)) := by
  rw [← Complex.exp_conj, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
    show starRingEnd ℂ (m : ℂ) = (m : ℂ) from Complex.conj_ofReal (m : ℝ)]
  congr 1; push_cast; ring

theorem innerNu_Z {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    innerNu (Z d) (Z e) = ((Nat.gcd d e : ℂ) ^ 2) / ((d : ℂ) * (e : ℂ)) := by
  let S : Finset ℕ := (d * e).primeFactors
  have hS_primes : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hd_sub : d.primeFactors ⊆ S := by
    rw [show S = d.primeFactors ∪ e.primeFactors from Nat.primeFactors_mul hd he]
    exact Finset.subset_union_left
  have he_sub : e.primeFactors ⊆ S := by
    rw [show S = d.primeFactors ∪ e.primeFactors from Nat.primeFactors_mul hd he]
    exact Finset.subset_union_right
  have h_prod_eq : ∀ ω : ℕ → ℝ,
      Z d ω * starRingEnd ℂ (Z e ω) = ∏ p ∈ S, localExpDiff d e p (ω p) := by
    intro ω
    have hZd : Z d ω = ∏ p ∈ S, Complex.exp (Complex.I * ((d.factorization p : ℤ) : ℂ) * (ω p : ℂ)) := by
      unfold Z phasor
      have hp_eq : ∏ p ∈ d.primeFactors, Complex.exp (Complex.I * (ω p : ℂ)) ^ d.factorization p =
          ∏ p ∈ d.primeFactors, Complex.exp (Complex.I * ((d.factorization p : ℤ) : ℂ) * (ω p : ℂ)) := by
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
      rw [hp_eq]
      refine Finset.prod_subset hd_sub fun p _ hp => ?_
      have hz : d.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
      simp [hz]
    have hZe : starRingEnd ℂ (Z e ω) =
        ∏ p ∈ S, Complex.exp (Complex.I * ((-(e.factorization p : ℤ) : ℤ) : ℂ) * (ω p : ℂ)) := by
      unfold Z phasor
      rw [map_prod]
      have hp_eq : ∏ p ∈ e.primeFactors, starRingEnd ℂ (Complex.exp (Complex.I * (ω p : ℂ)) ^ e.factorization p) =
          ∏ p ∈ e.primeFactors, Complex.exp (Complex.I * ((-(e.factorization p : ℤ) : ℤ) : ℂ) * (ω p : ℂ)) := by
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [← Complex.exp_nat_mul, show (e.factorization p : ℂ) * (Complex.I * (ω p : ℂ)) =
          Complex.I * (((e.factorization p : ℤ) : ℂ)) * (ω p : ℂ) by push_cast; ring]
        exact conj_exp_I_mul_int (e.factorization p : ℤ) (ω p)
      rw [hp_eq]
      refine Finset.prod_subset he_sub fun p _ hp => ?_
      have hz : e.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
      simp [hz]
    rw [hZd, hZe, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Complex.exp_add]
    unfold localExpDiff
    congr 1; push_cast; ring
  have h_meas : ∀ p ∈ S, AEStronglyMeasurable (localExpDiff d e p) (poissonMeasure p) := by
    intro p _
    unfold localExpDiff
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  unfold innerNu
  simp_rw [h_prod_eq]
  rw [integral_finset_prod_primeTorus S (localExpDiff d e) h_meas]
  have h_factor_eval : ∀ p ∈ S,
      (∫ t, localExpDiff d e p t ∂(poissonMeasure p)) =
        ((p : ℂ)⁻¹) ^ ((d.factorization p : ℤ) - (e.factorization p : ℤ)).natAbs := fun p hp =>
    integral_poissonMeasure_exp (hS_primes p hp) ((d.factorization p : ℤ) - (e.factorization p : ℤ))
  rw [Finset.prod_congr rfl h_factor_eval]
  have hde_ne : ((d : ℂ) * (e : ℂ)) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hd) (Nat.cast_ne_zero.mpr he)
  rw [eq_div_iff hde_ne]
  have hgcd0 : Nat.gcd d e ≠ 0 := Nat.gcd_ne_zero_left hd
  have hgcd_sub : (Nat.gcd d e).primeFactors ⊆ S := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ d := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.gcd_dvd_left d e)
    exact hd_sub (Nat.mem_primeFactors.mpr ⟨hp_prime, hpd, hd⟩)
  have hd_prod : (d : ℂ) = ∏ p ∈ S, (p : ℂ) ^ d.factorization p := by
    have h := congr_arg (Nat.cast : ℕ → ℂ) (Nat.prod_primeFactors_pow_factorization hd)
    simp only [Nat.cast_prod, Nat.cast_pow] at h
    rw [h]
    refine Finset.prod_subset hd_sub fun p _ hp => ?_
    have hz : d.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
    simp [hz]
  have he_prod : (e : ℂ) = ∏ p ∈ S, (p : ℂ) ^ e.factorization p := by
    have h := congr_arg (Nat.cast : ℕ → ℂ) (Nat.prod_primeFactors_pow_factorization he)
    simp only [Nat.cast_prod, Nat.cast_pow] at h
    rw [h]
    refine Finset.prod_subset he_sub fun p _ hp => ?_
    have hz : e.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
    simp [hz]
  have hgcd_prod : (Nat.gcd d e : ℂ) ^ 2 = ∏ p ∈ S, (p : ℂ) ^ (2 * min (d.factorization p) (e.factorization p)) := by
    have h := congr_arg (fun k : ℕ => (k : ℂ) ^ 2) (Nat.prod_primeFactors_pow_factorization hgcd0)
    simp only [Nat.cast_prod, ← Finset.prod_pow, Nat.cast_pow] at h
    rw [h]
    have hsub_eq : ∏ p ∈ (Nat.gcd d e).primeFactors, ((p : ℂ) ^ (Nat.gcd d e).factorization p) ^ 2 =
        ∏ p ∈ S, ((p : ℂ) ^ (Nat.gcd d e).factorization p) ^ 2 := by
      refine Finset.prod_subset hgcd_sub fun p _ hp => ?_
      have hz : (Nat.gcd d e).factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
      simp [hz]
    rw [hsub_eq]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Nat.factorization_gcd hd he, Finsupp.inf_apply, ← pow_mul, mul_comm]
  rw [hd_prod, he_prod, hgcd_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hS_primes p hp).ne_zero
  have hexp_sum : ((d.factorization p : ℤ) - (e.factorization p : ℤ)).natAbs +
      2 * min (d.factorization p) (e.factorization p) = d.factorization p + e.factorization p := by
    omega
  rw [inv_pow, ← pow_add, ← hexp_sum, pow_add, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp_ne), one_mul]

def phiLocal (p a : ℕ) (t : ℝ) : ℂ :=
  if a = 0 then 1
  else Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) -
    ((p : ℂ)⁻¹) * Complex.exp (Complex.I * ((a - 1 : ℕ) : ℂ) * (t : ℂ))

@[simp] theorem phiLocal_zero (p : ℕ) (t : ℝ) : phiLocal p 0 t = 1 := by
  simp [phiLocal]

def Psi (r : ℕ) (ω : ℕ → ℝ) : ℂ :=
  ∏ p ∈ r.primeFactors, phiLocal p (r.factorization p) (ω p)

@[simp] theorem Psi_one (ω : ℕ → ℝ) : Psi 1 ω = 1 := by
  simp [Psi]

def jWeight (r : ℕ) : ℝ :=
  ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ) ^ 2)

@[simp] theorem jWeight_one : jWeight 1 = 1 := by
  simp [jWeight]

private lemma phiLocal_continuous (p a : ℕ) : Continuous (phiLocal p a) := by
  unfold phiLocal
  split_ifs
  · exact continuous_const
  · fun_prop

private lemma single_prime_phiLocal_inner {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    ∫ t, phiLocal p a t * starRingEnd ℂ (phiLocal p b t) ∂(poissonMeasure p) =
      if a = b then (if a = 0 then (1 : ℂ) else 1 - ((p : ℂ) ^ 2)⁻¹) else 0 := by
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_int_exp : ∀ m : ℤ,
      Integrable (fun t : ℝ => Complex.exp (Complex.I * (m : ℂ) * (t : ℂ))) (poissonMeasure p) := by
    intro m
    refine Integrable.of_bound
      ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
      1 (ae_of_all _ fun t => ?_)
    rw [show ‖Complex.exp (Complex.I * (m : ℂ) * (t : ℂ))‖ = 1 by
      simpa [mul_assoc] using norm_exp_I_mul_real ((m : ℝ) * t)]
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · subst ha; subst hb
    simp [phiLocal, measure_univ]
  · subst ha
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    have hfun : (fun t : ℝ => phiLocal p 0 t * starRingEnd ℂ (phiLocal p b t)) =
        fun t : ℝ =>
          Complex.exp (Complex.I * ((-(b : ℤ) : ℤ) : ℂ) * (t : ℂ)) -
          ((p : ℂ)⁻¹) * Complex.exp (Complex.I * ((-((b - 1 : ℕ) : ℤ) : ℤ) : ℂ) * (t : ℂ)) := by
      ext t
      simp only [phiLocal, ↓reduceIte, hb, one_mul, map_sub, map_mul, Complex.conj_natCast, map_inv₀]
      have c1 := conj_exp_I_mul_int (b : ℤ) t
      have c2 := conj_exp_I_mul_int ((b - 1 : ℕ) : ℤ) t
      push_cast at c1 c2 ⊢
      rw [c1, c2]
    rw [hfun, integral_sub (h_int_exp _) ((h_int_exp _).const_mul _), integral_const_mul,
      integral_poissonMeasure_exp hp (-(b : ℤ)), integral_poissonMeasure_exp hp (-((b - 1 : ℕ) : ℤ))]
    have hnab1 : (-(b : ℤ)).natAbs = b := by omega
    have hnab2 : (-((b - 1 : ℕ) : ℤ)).natAbs = b - 1 := by omega
    have h0b : (0 : ℕ) ≠ b := Ne.symm hb
    rw [hnab1, hnab2]
    simp only [h0b, ↓reduceIte]
    have hpow : ((p : ℂ)⁻¹) ^ b = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) ^ (b - 1) := by
      conv_lhs => rw [show b = 1 + (b - 1) by omega, pow_add, pow_one]
    rw [hpow, sub_self]
  · subst hb
    have hapos : 0 < a := Nat.pos_of_ne_zero ha
    have hfun : (fun t : ℝ => phiLocal p a t * starRingEnd ℂ (phiLocal p 0 t)) =
        fun t : ℝ =>
          Complex.exp (Complex.I * ((a : ℤ) : ℂ) * (t : ℂ)) -
          ((p : ℂ)⁻¹) * Complex.exp (Complex.I * (((a - 1 : ℕ) : ℤ) : ℂ) * (t : ℂ)) := by
      ext t
      simp only [phiLocal, ha, ↓reduceIte, map_one, mul_one]
      push_cast; rfl
    rw [hfun, integral_sub (h_int_exp _) ((h_int_exp _).const_mul _), integral_const_mul,
      integral_poissonMeasure_exp hp (a : ℤ), integral_poissonMeasure_exp hp ((a - 1 : ℕ) : ℤ)]
    have hnab1 : ((a : ℤ)).natAbs = a := by omega
    have hnab2 : (((a - 1 : ℕ) : ℤ)).natAbs = a - 1 := by omega
    rw [hnab1, hnab2]
    simp only [ha, ↓reduceIte]
    have hpow : ((p : ℂ)⁻¹) ^ a = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) ^ (a - 1) := by
      conv_lhs => rw [show a = 1 + (a - 1) by omega, pow_add, pow_one]
    rw [hpow, sub_self]
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    have hfun : (fun t : ℝ => phiLocal p a t * starRingEnd ℂ (phiLocal p b t)) =
        fun t : ℝ =>
          (Complex.exp (Complex.I * (((a : ℤ) - (b : ℤ) : ℤ) : ℂ) * (t : ℂ)) -
           ((p : ℂ)⁻¹) * Complex.exp (Complex.I * (((a : ℤ) - ((b - 1 : ℕ) : ℤ) : ℤ) : ℂ) * (t : ℂ))) -
          (((p : ℂ)⁻¹) * Complex.exp (Complex.I * ((((a - 1 : ℕ) : ℤ) - (b : ℤ) : ℤ) : ℂ) * (t : ℂ)) -
           ((p : ℂ)⁻¹ * (p : ℂ)⁻¹) *
             Complex.exp (Complex.I * ((((a - 1 : ℕ) : ℤ) - ((b - 1 : ℕ) : ℤ) : ℤ) : ℂ) * (t : ℂ))) := by
      ext t
      simp only [phiLocal, ha, hb, ↓reduceIte, map_sub, map_mul, map_inv₀, Complex.conj_natCast]
      have c1 := conj_exp_I_mul_int (b : ℤ) t
      have c2 := conj_exp_I_mul_int ((b - 1 : ℕ) : ℤ) t
      push_cast at c1 c2 ⊢
      rw [c1, c2]
      have m11 : Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) * Complex.exp (Complex.I * (-(b : ℂ)) * (t : ℂ)) =
          Complex.exp (Complex.I * (((a : ℤ) - (b : ℤ) : ℤ) : ℂ) * (t : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      have m12 : Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) * Complex.exp (Complex.I * (-((b - 1 : ℕ) : ℂ)) * (t : ℂ)) =
          Complex.exp (Complex.I * (((a : ℤ) - ((b - 1 : ℕ) : ℤ) : ℤ) : ℂ) * (t : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      have m21 : Complex.exp (Complex.I * ((a - 1 : ℕ) : ℂ) * (t : ℂ)) * Complex.exp (Complex.I * (-(b : ℂ)) * (t : ℂ)) =
          Complex.exp (Complex.I * ((((a - 1 : ℕ) : ℤ) - (b : ℤ) : ℤ) : ℂ) * (t : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      have m22 : Complex.exp (Complex.I * ((a - 1 : ℕ) : ℂ) * (t : ℂ)) * Complex.exp (Complex.I * (-((b - 1 : ℕ) : ℂ)) * (t : ℂ)) =
          Complex.exp (Complex.I * ((((a - 1 : ℕ) : ℤ) - ((b - 1 : ℕ) : ℤ) : ℤ) : ℂ) * (t : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      have h_alg :
          (Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) -
            (p : ℂ)⁻¹ * Complex.exp (Complex.I * ((a - 1 : ℕ) : ℂ) * (t : ℂ))) *
          (Complex.exp (Complex.I * (-(b : ℂ)) * (t : ℂ)) -
            (p : ℂ)⁻¹ * Complex.exp (Complex.I * (-((b - 1 : ℕ) : ℂ)) * (t : ℂ))) =
          (Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) * Complex.exp (Complex.I * (-(b : ℂ)) * (t : ℂ)) -
           (p : ℂ)⁻¹ * (Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) * Complex.exp (Complex.I * (-((b - 1 : ℕ) : ℂ)) * (t : ℂ)))) -
          ((p : ℂ)⁻¹ * (Complex.exp (Complex.I * ((a - 1 : ℕ) : ℂ) * (t : ℂ)) * Complex.exp (Complex.I * (-(b : ℂ)) * (t : ℂ))) -
           ((p : ℂ)⁻¹ * (p : ℂ)⁻¹) * (Complex.exp (Complex.I * ((a - 1 : ℕ) : ℂ) * (t : ℂ)) * Complex.exp (Complex.I * (-((b - 1 : ℕ) : ℂ)) * (t : ℂ)))) := by
        ring
      rw [h_alg, m11, m12, m21, m22]
      push_cast
      rfl
    rw [hfun]
    have hi1 : Integrable (fun t : ℝ =>
        Complex.exp (Complex.I * (((a : ℤ) - (b : ℤ) : ℤ) : ℂ) * (t : ℂ)) -
        (p : ℂ)⁻¹ * Complex.exp (Complex.I * (((a : ℤ) - ((b - 1 : ℕ) : ℤ) : ℤ) : ℂ) * (t : ℂ))) (poissonMeasure p) :=
      (h_int_exp _).sub ((h_int_exp _).const_mul _)
    have hi2 : Integrable (fun t : ℝ =>
        (p : ℂ)⁻¹ * Complex.exp (Complex.I * ((((a - 1 : ℕ) : ℤ) - (b : ℤ) : ℤ) : ℂ) * (t : ℂ)) -
        ((p : ℂ)⁻¹ * (p : ℂ)⁻¹) * Complex.exp (Complex.I * ((((a - 1 : ℕ) : ℤ) - ((b - 1 : ℕ) : ℤ) : ℤ) : ℂ) * (t : ℂ))) (poissonMeasure p) :=
      ((h_int_exp _).const_mul _).sub ((h_int_exp _).const_mul _)
    rw [integral_sub hi1 hi2,
      integral_sub (h_int_exp _) ((h_int_exp _).const_mul _),
      integral_sub ((h_int_exp _).const_mul _) ((h_int_exp _).const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_poissonMeasure_exp hp ((a : ℤ) - (b : ℤ)),
      integral_poissonMeasure_exp hp ((a : ℤ) - ((b - 1 : ℕ) : ℤ)),
      integral_poissonMeasure_exp hp (((a - 1 : ℕ) : ℤ) - (b : ℤ)),
      integral_poissonMeasure_exp hp (((a - 1 : ℕ) : ℤ) - ((b - 1 : ℕ) : ℤ))]
    rcases Nat.lt_trichotomy a b with hab | rfl | hab
    · have hne : a ≠ b := by omega
      rw [ite_eq_right hne]
      have h1 : ((a : ℤ) - (b : ℤ)).natAbs = b - a := by omega
      have h2 : ((a : ℤ) - ((b - 1 : ℕ) : ℤ)).natAbs = b - 1 - a := by omega
      have h3 : (((a - 1 : ℕ) : ℤ) - (b : ℤ)).natAbs = b - a + 1 := by omega
      have h4 : (((a - 1 : ℕ) : ℤ) - ((b - 1 : ℕ) : ℤ)).natAbs = b - a := by omega
      rw [h1, h2, h3, h4]
      have ha1 : ((p : ℂ)⁻¹) ^ (b - a) = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) ^ (b - 1 - a) := by
        conv_lhs => rw [show b - a = 1 + (b - 1 - a) by omega, pow_add, pow_one]
      have ha2 : ((p : ℂ)⁻¹) ^ (b - a + 1) = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) ^ (b - a) := by
        rw [pow_add, pow_one, mul_comm]
      rw [ha2, ha1]; ring
    · rw [ite_eq_left rfl, ite_eq_right ha]
      have h1 : ((a : ℤ) - (a : ℤ)).natAbs = 0 := by omega
      have h2 : ((a : ℤ) - ((a - 1 : ℕ) : ℤ)).natAbs = 1 := by omega
      have h3 : (((a - 1 : ℕ) : ℤ) - (a : ℤ)).natAbs = 1 := by omega
      have h4 : (((a - 1 : ℕ) : ℤ) - ((a - 1 : ℕ) : ℤ)).natAbs = 0 := by omega
      rw [h1, h2, h3, h4, pow_zero, pow_one, sq, mul_inv_rev]
      ring
    · have hne : a ≠ b := by omega
      rw [ite_eq_right hne]
      have h1 : ((a : ℤ) - (b : ℤ)).natAbs = a - b := by omega
      have h2 : ((a : ℤ) - ((b - 1 : ℕ) : ℤ)).natAbs = a - b + 1 := by omega
      have h3 : (((a - 1 : ℕ) : ℤ) - (b : ℤ)).natAbs = a - 1 - b := by omega
      have h4 : (((a - 1 : ℕ) : ℤ) - ((b - 1 : ℕ) : ℤ)).natAbs = a - b := by omega
      rw [h1, h2, h3, h4]
      have ha1 : ((p : ℂ)⁻¹) ^ (a - b + 1) = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) ^ (a - b) := by
        rw [pow_add, pow_one, mul_comm]
      have ha2 : ((p : ℂ)⁻¹) ^ (a - b) = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) ^ (a - 1 - b) := by
        conv_lhs => rw [show a - b = 1 + (a - 1 - b) by omega, pow_add, pow_one]
      rw [ha1, ha2]; ring

theorem innerNu_Psi {r s : ℕ} (hr : r ≠ 0) (hs : s ≠ 0) :
    innerNu (Psi r) (Psi s) = if r = s then (jWeight r : ℂ) else 0 := by
  let S : Finset ℕ := (r * s).primeFactors
  have hS_primes : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hr_sub : r.primeFactors ⊆ S := by
    rw [show S = r.primeFactors ∪ s.primeFactors from Nat.primeFactors_mul hr hs]
    exact Finset.subset_union_left
  have hs_sub : s.primeFactors ⊆ S := by
    rw [show S = r.primeFactors ∪ s.primeFactors from Nat.primeFactors_mul hr hs]
    exact Finset.subset_union_right
  have h_prod_eq : ∀ ω : ℕ → ℝ,
      Psi r ω * starRingEnd ℂ (Psi s ω) =
        ∏ p ∈ S, (phiLocal p (r.factorization p) (ω p) * starRingEnd ℂ (phiLocal p (s.factorization p) (ω p))) := by
    intro ω
    have hPr : Psi r ω = ∏ p ∈ S, phiLocal p (r.factorization p) (ω p) := by
      unfold Psi
      refine Finset.prod_subset hr_sub fun p _ hp => ?_
      have hz : r.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
      simp [hz]
    have hPs : starRingEnd ℂ (Psi s ω) = ∏ p ∈ S, starRingEnd ℂ (phiLocal p (s.factorization p) (ω p)) := by
      unfold Psi
      rw [map_prod]
      refine Finset.prod_subset hs_sub fun p _ hp => ?_
      have hz : s.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
      simp [hz]
    rw [hPr, hPs, ← Finset.prod_mul_distrib]
  have h_meas : ∀ p ∈ S,
      AEStronglyMeasurable (fun t => phiLocal p (r.factorization p) t * starRingEnd ℂ (phiLocal p (s.factorization p) t))
        (poissonMeasure p) := by
    intro p _
    exact ((phiLocal_continuous p _).mul (Complex.continuous_conj.comp (phiLocal_continuous p _))).aestronglyMeasurable
  unfold innerNu
  simp_rw [h_prod_eq]
  rw [integral_finset_prod_primeTorus S _ h_meas]
  have h_factor : ∀ p ∈ S,
      (∫ t, phiLocal p (r.factorization p) t * starRingEnd ℂ (phiLocal p (s.factorization p) t) ∂(poissonMeasure p)) =
        if r.factorization p = s.factorization p then
          (if r.factorization p = 0 then (1 : ℂ) else 1 - ((p : ℂ) ^ 2)⁻¹)
        else 0 := fun p hp => single_prime_phiLocal_inner (hS_primes p hp) _ _
  rw [Finset.prod_congr rfl h_factor]
  by_cases hrs : r = s
  · subst hrs
    simp only [↓reduceIte]
    unfold jWeight
    rw [Complex.ofReal_prod]
    have hS_eq : S = r.primeFactors := by
      dsimp [S]; rw [Nat.primeFactors_mul hr hr, Finset.union_self]
    rw [hS_eq]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpos : r.factorization p ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hr
        (Nat.dvd_of_mem_primeFactors hp)).ne'
    simp only [↓reduceIte, hpos]
    push_cast
    rw [one_div]
  · simp only [hrs, ↓reduceIte]
    have hne_fac : r.factorization ≠ s.factorization := by
      intro heq
      exact hrs (Nat.factorization_inj hr hs heq)
    have hex : ∃ p ∈ S, r.factorization p ≠ s.factorization p := by
      by_contra hall
      push Not at hall
      apply hne_fac
      ext p
      by_cases hpS : p ∈ S
      · exact hall p hpS
      · have hpr : r.factorization p = 0 :=
          Finsupp.notMem_support_iff.mp (fun hm => hpS (hr_sub (by simpa [Nat.support_factorization] using hm)))
        have hps : s.factorization p = 0 :=
          Finsupp.notMem_support_iff.mp (fun hm => hpS (hs_sub (by simpa [Nat.support_factorization] using hm)))
        exact hpr.trans hps.symm
    obtain ⟨p₀, hp₀, hne⟩ := hex
    refine Finset.prod_eq_zero hp₀ ?_
    simp [hne]

private lemma Psi_prime_pow {p k : ℕ} (hp : p.Prime) (ω : ℕ → ℝ) :
    Psi (p ^ k) ω = phiLocal p k (ω p) := by
  by_cases hk : k = 0
  · subst hk; simp
  · unfold Psi
    rw [Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton, hp.factorization_pow,
      Finsupp.single_eq_same]

private lemma Psi_mul_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) (ω : ℕ → ℝ) :
    Psi (m * n) ω = Psi m ω * Psi n ω := by
  unfold Psi
  have hdisj : Disjoint m.primeFactors n.primeFactors := hmn.disjoint_primeFactors
  rw [Nat.primeFactors_mul hm hn, Finset.prod_union hdisj]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_mul hm hn, Finsupp.coe_add, Pi.add_apply]
    have hn0 : n.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (fun hm' => Finset.disjoint_left.mp hdisj hp
        (by simpa [Nat.support_factorization] using hm'))
    simp [hn0]
  · refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_mul hm hn, Finsupp.coe_add, Pi.add_apply]
    have hm0 : m.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (fun hm' => Finset.disjoint_right.mp hdisj hp
        (by simpa [Nat.support_factorization] using hm'))
    simp [hm0]

theorem Z_eq_sum_Psi {n : ℕ} (hn : n ≠ 0) (ω : ℕ → ℝ) :
    Z n ω = ∑ r ∈ n.divisors, ((r : ℂ) / (n : ℂ)) * Psi r ω := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  let P : ArithmeticFunction ℂ := ⟨fun r => if r = 0 then 0 else (r : ℂ) * Psi r ω, by simp⟩
  have hP_mult : P.IsMultiplicative := by
    refine ⟨by simp [P], fun {a b} hab => ?_⟩
    by_cases ha : a = 0
    · subst ha; simp [P]
    · by_cases hb : b = 0
      · subst hb; simp [P]
      · change (if a * b = 0 then (0 : ℂ) else ((a * b : ℕ) : ℂ) * Psi (a * b) ω) =
          (if a = 0 then (0 : ℂ) else (a : ℂ) * Psi a ω) *
            (if b = 0 then (0 : ℂ) else (b : ℂ) * Psi b ω)
        simp only [ha, hb, mul_ne_zero ha hb, ↓reduceIte, Psi_mul_coprime ha hb hab ω, Nat.cast_mul]
        ring
  let Q : ArithmeticFunction ℂ := P * (↑ArithmeticFunction.zeta : ArithmeticFunction ℂ)
  have hQ_mult : Q.IsMultiplicative := hP_mult.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  have hQ_apply : ∀ k : ℕ, k ≠ 0 → Q k = ∑ r ∈ k.divisors, (r : ℂ) * Psi r ω := by
    intro k hk
    have hQ_eq : Q k = ((↑ArithmeticFunction.zeta : ArithmeticFunction ℂ) * P) k := by
      simp [Q, mul_comm]
    rw [hQ_eq, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal' (f := fun x y => ((↑ArithmeticFunction.zeta : ArithmeticFunction ℂ) x) * P y)]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr0 : r ≠ 0 := ne_zero_of_dvd_ne_zero hk (Nat.dvd_of_mem_divisors hr)
    have hkr0 : k / r ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨hr0, Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.dvd_of_mem_divisors hr)⟩
    simp [ArithmeticFunction.natCoe_apply, P, hr0, hkr0]
  have hZ_mult : (ZArith ω).IsMultiplicative := ZArith_isMultiplicative ω
  have h_eq_Q : Q n = (n : ℂ) * Z n ω := by
    have hpair : (n.primeFactors : Set ℕ).Pairwise
        (fun p q => Nat.Coprime (p ^ n.factorization p) (q ^ n.factorization q)) := by
      intro p hp q hq hpq
      exact Nat.Coprime.pow _ _
        ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
    have h_scale : (n : ℂ) * Z n ω =
        ∏ p ∈ n.primeFactors, ((p ^ n.factorization p : ℕ) : ℂ) * Z (p ^ n.factorization p) ω := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
      have hz_prod : Z (∏ p ∈ n.primeFactors, p ^ n.factorization p) ω =
          ∏ p ∈ n.primeFactors, Z (p ^ n.factorization p) ω := by
        have hmult := hZ_mult.map_prod (fun p => p ^ n.factorization p) n.primeFactors hpair
        have hn_prod_nz : (∏ p ∈ n.primeFactors, p ^ n.factorization p) ≠ 0 := by
          rw [← Nat.prod_primeFactors_pow_factorization hn]; exact hn
        calc Z (∏ p ∈ n.primeFactors, p ^ n.factorization p) ω
            = ZArith ω (∏ p ∈ n.primeFactors, p ^ n.factorization p) := by
              simp [ZArith, hn_prod_nz]
          _ = ∏ p ∈ n.primeFactors, ZArith ω (p ^ n.factorization p) := hmult
          _ = ∏ p ∈ n.primeFactors, Z (p ^ n.factorization p) ω :=
              Finset.prod_congr rfl fun p hp => by
                have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
                simp [ZArith, hp0]
      rw [hz_prod, Nat.cast_prod, Finset.prod_mul_distrib]
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn, hQ_mult.map_prod _ _ hpair]
    rw [h_scale]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpk0 : p ^ n.factorization p ≠ 0 := pow_ne_zero _ hprime.ne_zero
    rw [hQ_apply _ hpk0, Nat.sum_divisors_prime_pow hprime]
    have htelescope : ∀ k : ℕ,
        ∑ i ∈ Finset.range (k + 1), ((p ^ i : ℕ) : ℂ) * Psi (p ^ i) ω =
          ((p ^ k : ℕ) : ℂ) * Z (p ^ k) ω := by
      intro k
      induction k with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih, Psi_prime_pow hprime, Z_prime_pow hprime, Z_prime_pow hprime]
        simp only [phiLocal, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel, Nat.cast_pow]
        have heq : (Complex.exp (Complex.I * (((m + 1 : ℕ) : ℂ)) * (ω p : ℂ))) = phasor p ω ^ (m + 1) := by
          unfold phasor; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
        have heq0 : (Complex.exp (Complex.I * (m : ℂ) * (ω p : ℂ))) = phasor p ω ^ m := by
          unfold phasor; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
        have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hprime.ne_zero
        rw [heq, heq0]
        field_simp [hp_ne]
        ring
    exact htelescope (n.factorization p)
  symm
  calc ∑ r ∈ n.divisors, ((r : ℂ) / (n : ℂ)) * Psi r ω
      = (∑ r ∈ n.divisors, (r : ℂ) * Psi r ω) / (n : ℂ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun r _ => by ring
    _ = Q n / (n : ℂ) := by rw [← hQ_apply n hn]
    _ = ((n : ℂ) * Z n ω) / (n : ℂ) := by rw [h_eq_Q]
    _ = Z n ω := by field_simp [hnC]

def scalarS (B n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 n).filter (fun k => Nat.Coprime k B), mertens (n / k) / (k : ℝ)

theorem D_eq_sum_Psi {B : ℕ} (hB : 1 ≤ B) (X : ℕ) (ω : ℕ → ℝ) :
    D B X ω =
      ∑ r ∈ (Finset.Icc 1 X).filter (fun r => Nat.Coprime r B),
        (scalarS B (X / r) : ℂ) * Psi r ω := by
  rw [D_eq_mertens_sum hB X ω]
  have hbox_L :
      (∑ d ∈ (Finset.Icc 1 X).filter (fun d => Nat.Coprime d B), (mertens (X / d) : ℂ) * Z d ω) =
        ∑ d ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
          if d.Coprime B ∧ r ∣ d then
            (mertens (X / d) : ℂ) * ((r : ℂ) / (d : ℂ)) * Psi r ω
          else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd_pos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hd_le : d ≤ X := (Finset.mem_Icc.mp hd).2
    by_cases hdc : d.Coprime B
    · rw [ite_eq_left hdc, Z_eq_sum_Psi hd_pos.ne' ω, Finset.mul_sum]
      have heq_set : d.divisors = (Finset.Icc 1 X).filter (fun r => r ∣ d) := by
        ext r
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro hr; exact ⟨⟨Nat.pos_of_dvd_of_pos hr.1 hd_pos, (Nat.le_of_dvd hd_pos hr.1).trans hd_le⟩, hr.1⟩
        · intro hr; exact ⟨hr.2, hd_pos.ne'⟩
      rw [heq_set, Finset.sum_filter]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hrd : r ∣ d
      · rw [ite_eq_left hrd, ite_eq_left ⟨hdc, hrd⟩]; ring
      · rw [ite_eq_right hrd, ite_eq_right (fun h => hrd h.2)]
    · rw [ite_eq_right hdc]
      symm
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [ite_eq_right (fun h => hdc h.1)]
  have hbox_R :
      (∑ r ∈ (Finset.Icc 1 X).filter (fun r => Nat.Coprime r B), (scalarS B (X / r) : ℂ) * Psi r ω) =
        ∑ r ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 X,
          if d.Coprime B ∧ r ∣ d then
            (mertens (X / d) : ℂ) * ((r : ℂ) / (d : ℂ)) * Psi r ω
          else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr_pos : 0 < r := (Finset.mem_Icc.mp hr).1
    have hr_le : r ≤ X := (Finset.mem_Icc.mp hr).2
    by_cases hrc : r.Coprime B
    · rw [ite_eq_left hrc]
      unfold scalarS
      rw [Complex.ofReal_sum, Finset.sum_filter, Finset.sum_mul]
      have h_rk :
          (∑ k ∈ Finset.Icc 1 (X / r),
              (if k.Coprime B then ((mertens ((X / r) / k) / (k : ℝ) : ℝ) : ℂ) else 0) * Psi r ω) =
            ∑ d ∈ Finset.Icc 1 X,
              if d.Coprime B ∧ r ∣ d then
                (mertens (X / d) : ℂ) * ((r : ℂ) / (d : ℂ)) * Psi r ω
              else 0 := by
        symm
        calc (∑ d ∈ Finset.Icc 1 X,
                if d.Coprime B ∧ r ∣ d then (mertens (X / d) : ℂ) * ((r : ℂ) / (d : ℂ)) * Psi r ω else 0)
            = ∑ d ∈ Finset.Icc 1 X, ∑ k ∈ Finset.Icc 1 (X / r),
                if r * k = d ∧ k.Coprime B then (mertens (X / d) : ℂ) * ((r : ℂ) / (d : ℂ)) * Psi r ω else 0 := by
              refine Finset.sum_congr rfl fun d hd => ?_
              have hd_pos : 0 < d := (Finset.mem_Icc.mp hd).1
              have hd_le : d ≤ X := (Finset.mem_Icc.mp hd).2
              by_cases hdiv : r ∣ d
              · let k₀ := d / r
                have hk₀_eq : r * k₀ = d := Nat.mul_div_cancel' hdiv
                have hk₀_pos : 0 < k₀ := Nat.div_pos (Nat.le_of_dvd hd_pos hdiv) hr_pos
                have hk₀_le : k₀ ≤ X / r := Nat.div_le_div_right hd_le
                have hk₀_mem : k₀ ∈ Finset.Icc 1 (X / r) := Finset.mem_Icc.mpr ⟨hk₀_pos, hk₀_le⟩
                rw [Finset.sum_eq_single k₀]
                · have hcop_iff : d.Coprime B ↔ k₀.Coprime B := by
                    rw [← hk₀_eq, Nat.coprime_mul_iff_left]
                    exact ⟨fun h => h.2, fun h => ⟨hrc, h⟩⟩
                  by_cases hk₀c : k₀.Coprime B
                  · rw [ite_eq_left ⟨hcop_iff.mpr hk₀c, hdiv⟩, ite_eq_left ⟨hk₀_eq, hk₀c⟩]
                  · rw [ite_eq_right (fun h => hk₀c (hcop_iff.mp h.1)), ite_eq_right (fun h => hk₀c h.2)]
                · intro k _ hkne
                  have hnot : ¬ (r * k = d ∧ k.Coprime B) := by
                    rintro ⟨hrk, _⟩
                    exact hkne (Nat.eq_of_mul_eq_mul_left hr_pos (hrk.trans hk₀_eq.symm))
                  rw [ite_eq_right hnot]
                · intro hk_nmem; exact absurd hk₀_mem hk_nmem
              · have hzero : ∀ k ∈ Finset.Icc 1 (X / r),
                    (if r * k = d ∧ k.Coprime B then (mertens (X / d) : ℂ) * ((r : ℂ) / (d : ℂ)) * Psi r ω else 0) = 0 := by
                  intro k _
                  have hnot : ¬ (r * k = d ∧ k.Coprime B) := fun ⟨hrk, _⟩ => hdiv ⟨k, hrk.symm⟩
                  rw [ite_eq_right hnot]
                rw [Finset.sum_eq_zero hzero, ite_eq_right (fun h => hdiv h.2)]
          _ = ∑ k ∈ Finset.Icc 1 (X / r), ∑ d ∈ Finset.Icc 1 X,
                if r * k = d ∧ k.Coprime B then (mertens (X / d) : ℂ) * ((r : ℂ) / (d : ℂ)) * Psi r ω else 0 :=
              Finset.sum_comm
          _ = ∑ k ∈ Finset.Icc 1 (X / r),
                (if k.Coprime B then ((mertens ((X / r) / k) / (k : ℝ) : ℝ) : ℂ) else 0) * Psi r ω := by
              refine Finset.sum_congr rfl fun k hk => ?_
              have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
              have hk_le : k ≤ X / r := (Finset.mem_Icc.mp hk).2
              have hrk_le : r * k ≤ X := by
                calc r * k = k * r := mul_comm r k
                  _ ≤ X := (Nat.le_div_iff_mul_le hr_pos).mp hk_le
              have hrk_mem : r * k ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨Nat.mul_pos hr_pos hk_pos, hrk_le⟩
              rw [Finset.sum_eq_single (r * k)]
              · by_cases hkc : k.Coprime B
                · have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk_pos.ne'
                  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr_pos.ne'
                  rw [ite_eq_left ⟨rfl, hkc⟩, ite_eq_left hkc]
                  simp only [Complex.ofReal_div, Complex.ofReal_natCast, Nat.cast_mul, Nat.div_div_eq_div_mul]
                  field_simp [hkC, hrC]
                · rw [ite_eq_right (fun h => hkc h.2), ite_eq_right hkc, zero_mul]
              · intro d _ hdne
                rw [ite_eq_right (fun h => hdne h.1.symm)]
              · intro hm; exact absurd hrk_mem hm
      exact h_rk
    · rw [ite_eq_right hrc]
      symm
      refine Finset.sum_eq_zero fun d _ => ?_
      have hnot : ¬ (d.Coprime B ∧ r ∣ d) := fun ⟨hdc, hrd⟩ => hrc (hdc.coprime_dvd_left hrd)
      rw [ite_eq_right hnot]
  rw [hbox_L, hbox_R, Finset.sum_comm]

private lemma norm_phiLocal_le_two (p a : ℕ) (t : ℝ) : ‖phiLocal p a t‖ ≤ 2 := by
  unfold phiLocal
  split_ifs
  · norm_num
  · have h1 : ‖Complex.exp (Complex.I * (a : ℂ) * (t : ℂ))‖ = 1 := by
      simpa [mul_assoc] using norm_exp_I_mul_real ((a : ℝ) * t)
    have h2 : ‖((p : ℂ)⁻¹) * Complex.exp (Complex.I * ((a - 1 : ℕ) : ℂ) * (t : ℂ))‖ ≤ 1 := by
      rw [norm_mul, norm_inv, Complex.norm_natCast,
        show ‖Complex.exp (Complex.I * ((a - 1 : ℕ) : ℂ) * (t : ℂ))‖ = 1 by
          simpa [mul_assoc] using norm_exp_I_mul_real (((a - 1 : ℕ) : ℝ) * t), mul_one]
      by_cases hp : p = 0
      · subst hp; simp
      · exact inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp)))
    calc ‖Complex.exp (Complex.I * (a : ℂ) * (t : ℂ)) -
            (p : ℂ)⁻¹ * Complex.exp (Complex.I * ((a - 1 : ℕ) : ℂ) * (t : ℂ))‖
        ≤ ‖Complex.exp (Complex.I * (a : ℂ) * (t : ℂ))‖ +
            ‖(p : ℂ)⁻¹ * Complex.exp (Complex.I * ((a - 1 : ℕ) : ℂ) * (t : ℂ))‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (le_of_eq h1) h2
      _ = 2 := by norm_num

private lemma Psi_continuous (r : ℕ) : Continuous (Psi r) := by
  unfold Psi
  exact continuous_finsetProd _ fun p _ => (phiLocal_continuous p _).comp (continuous_apply p)

private lemma norm_Psi_le (r : ℕ) (ω : ℕ → ℝ) : ‖Psi r ω‖ ≤ (2 : ℝ) ^ r.primeFactors.card := by
  unfold Psi
  rw [norm_prod]
  calc ∏ p ∈ r.primeFactors, ‖phiLocal p (r.factorization p) (ω p)‖
      ≤ ∏ _ ∈ r.primeFactors, (2 : ℝ) := by
        induction r.primeFactors using Finset.cons_induction with
        | empty => simp
        | cons p s hp ih =>
          simp only [Finset.prod_cons]
          exact mul_le_mul (norm_phiLocal_le_two _ _ _) ih
            (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by norm_num)
    _ = (2 : ℝ) ^ r.primeFactors.card := by simp

theorem norm_sq_D_eq_energy {B : ℕ} (hB : 1 ≤ B) (X : ℕ) :
    ∫ ω, ‖D B X ω‖ ^ 2 ∂primeTorusMeasure =
      ∑ r ∈ (Finset.Icc 1 X).filter (fun r => Nat.Coprime r B),
        jWeight r * (scalarS B (X / r)) ^ 2 := by
  let T := (Finset.Icc 1 X).filter (fun r => Nat.Coprime r B)
  have hD_eq : ∀ ω : ℕ → ℝ, D B X ω = ∑ r ∈ T, (scalarS B (X / r) : ℂ) * Psi r ω :=
    fun ω => D_eq_sum_Psi hB X ω
  have hPsi_pair_int : ∀ r s : ℕ,
      Integrable (fun ω : ℕ → ℝ =>
        ((scalarS B (X / r) : ℂ) * Psi r ω) *
          starRingEnd ℂ ((scalarS B (X / s) : ℂ) * Psi s ω)) primeTorusMeasure := by
    intro r s
    have hc : Continuous (fun ω : ℕ → ℝ =>
        ((scalarS B (X / r) : ℂ) * Psi r ω) *
          starRingEnd ℂ ((scalarS B (X / s) : ℂ) * Psi s ω)) :=
      (continuous_const.mul (Psi_continuous r)).mul
        (Complex.continuous_conj.comp (continuous_const.mul (Psi_continuous s)))
    refine Integrable.of_bound hc.aestronglyMeasurable
      ((|scalarS B (X / r)| * (2 : ℝ) ^ r.primeFactors.card) *
        (|scalarS B (X / s)| * (2 : ℝ) ^ s.primeFactors.card)) (ae_of_all _ fun ω => ?_)
    rw [norm_mul, RCLike.norm_conj, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (norm_Psi_le r ω) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (norm_Psi_le s ω) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      (mul_nonneg (abs_nonneg _) (by positivity))
  have hD_cont : Continuous (fun ω : ℕ → ℝ => D B X ω) := by
    simp_rw [hD_eq]
    exact continuous_finsetSum _ fun r _ => continuous_const.mul (Psi_continuous r)
  have hD_norm_int : Integrable (fun ω : ℕ → ℝ => ‖D B X ω‖ ^ 2) primeTorusMeasure := by
    have hD_bound : ∃ C : ℝ, ∀ ω : ℕ → ℝ, ‖D B X ω‖ ^ 2 ≤ C := by
      refine ⟨(∑ r ∈ T, |scalarS B (X / r)| * (2 : ℝ) ^ r.primeFactors.card) ^ 2, fun ω => ?_⟩
      have htri : ‖D B X ω‖ ≤ ∑ r ∈ T, |scalarS B (X / r)| * (2 : ℝ) ^ r.primeFactors.card := by
        rw [hD_eq ω]
        calc ‖∑ r ∈ T, (scalarS B (X / r) : ℂ) * Psi r ω‖
            ≤ ∑ r ∈ T, ‖(scalarS B (X / r) : ℂ) * Psi r ω‖ := norm_sum_le _ _
          _ ≤ ∑ r ∈ T, |scalarS B (X / r)| * (2 : ℝ) ^ r.primeFactors.card := by
              refine Finset.sum_le_sum fun r _ => ?_
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left (norm_Psi_le r ω) (abs_nonneg _)
      exact pow_le_pow_left₀ (norm_nonneg _) htri 2
    obtain ⟨C, hC⟩ := hD_bound
    refine Integrable.of_bound ((hD_cont.norm.pow 2).aestronglyMeasurable) C (ae_of_all _ fun ω => ?_)
    simpa [Real.norm_of_nonneg (sq_nonneg ‖D B X ω‖)] using hC ω
  have h_complex :
      ((∫ ω, ‖D B X ω‖ ^ 2 ∂primeTorusMeasure : ℝ) : ℂ) =
        ∑ r ∈ T, ((jWeight r * (scalarS B (X / r)) ^ 2 : ℝ) : ℂ) := by
    calc ((∫ ω, ‖D B X ω‖ ^ 2 ∂primeTorusMeasure : ℝ) : ℂ)
        = ∫ ω, ((‖D B X ω‖ ^ 2 : ℝ) : ℂ) ∂primeTorusMeasure := by
          simpa using (Complex.ofRealCLM.integral_comp_comm hD_norm_int).symm
      _ = ∫ ω, D B X ω * starRingEnd ℂ (D B X ω) ∂primeTorusMeasure := by
          congr 1; ext ω; push_cast; exact (Complex.mul_conj' (D B X ω)).symm
      _ = ∫ ω, ∑ r ∈ T, ∑ s ∈ T,
            ((scalarS B (X / r) : ℂ) * Psi r ω) *
              starRingEnd ℂ ((scalarS B (X / s) : ℂ) * Psi s ω) ∂primeTorusMeasure := by
          congr 1; ext ω
          rw [hD_eq ω, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ => Finset.mul_sum _ _ _
      _ = ∑ r ∈ T, ∫ ω, ∑ s ∈ T,
            ((scalarS B (X / r) : ℂ) * Psi r ω) *
              starRingEnd ℂ ((scalarS B (X / s) : ℂ) * Psi s ω) ∂primeTorusMeasure := by
          refine integral_finsetSum T fun r _ => ?_
          exact integrable_finsetSum T fun s _ => hPsi_pair_int r s
      _ = ∑ r ∈ T, ∑ s ∈ T, ∫ ω,
            ((scalarS B (X / r) : ℂ) * Psi r ω) *
              starRingEnd ℂ ((scalarS B (X / s) : ℂ) * Psi s ω) ∂primeTorusMeasure := by
          refine Finset.sum_congr rfl fun r _ => integral_finsetSum T fun s _ => hPsi_pair_int r s
      _ = ∑ r ∈ T, ∑ s ∈ T,
            ((scalarS B (X / r) : ℂ) * (scalarS B (X / s) : ℂ)) * innerNu (Psi r) (Psi s) := by
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
          have heq : (fun ω : ℕ → ℝ =>
              ((scalarS B (X / r) : ℂ) * Psi r ω) *
                starRingEnd ℂ ((scalarS B (X / s) : ℂ) * Psi s ω)) =
              fun ω => ((scalarS B (X / r) : ℂ) * (scalarS B (X / s) : ℂ)) *
                (Psi r ω * starRingEnd ℂ (Psi s ω)) := by
            ext ω
            simp only [map_mul, Complex.conj_ofReal]
            ring
          rw [heq, integral_const_mul]
          rfl
      _ = ∑ r ∈ T, ((jWeight r * (scalarS B (X / r)) ^ 2 : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          have hr_pos : 0 < r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
          rw [Finset.sum_eq_single r]
          · rw [innerNu_Psi hr_pos.ne' hr_pos.ne']
            simp only [↓reduceIte]
            push_cast; ring
          · intro s hs hrs
            have hs_pos : 0 < s := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
            rw [innerNu_Psi hr_pos.ne' hs_pos.ne']
            simp only [hrs.symm, ↓reduceIte, mul_zero]
          · intro hr_nmem; exact absurd hr hr_nmem
  rw [← Complex.ofReal_sum] at h_complex
  exact_mod_cast h_complex

end RHConnections.CoherentEnergyMeasure