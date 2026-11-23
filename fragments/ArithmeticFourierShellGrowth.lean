import Verified
import Mathlib.Data.Nat.Log

noncomputable section
namespace RHConnections.ArithmeticFourierShell
open ArithmeticFourierInversion MertensCriterion

def ShellLongGrowth : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 ≤ K ∧ ∀ (X y : ℕ) (A : Finset ℕ), 1 ≤ X →
    A ⊆ upperOddShell X → (∑ n ∈ A,muR n) = 0 →
    |shellLongContribution X (Nat.log 2 X) y (upperOddShell X \ A)| ≤ K*(X:ℝ)^(1+δ)

private theorem shell_log_mul_le (X : ℕ) (hX : 1 ≤ X) :
    (Nat.log 2 X : ℝ)*Real.log 2 ≤ Real.log X := by
  have hpow : (2:ℝ)^(Nat.log 2 X) ≤ (X:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : X ≠ 0)
  have hl := Real.log_le_log (by positivity) hpow
  rwa [Real.log_pow] at hl

private theorem nonzero_shell_card_le {X : ℕ} (A : Finset ℕ) :
    (nonzeroMobius (upperOddShell X \ A)).card ≤ X := by
  have h : nonzeroMobius (upperOddShell X \ A) ⊆ Finset.Icc 1 X := by
    intro n hn
    have hs := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).1).1
    have h' := upper_odd_shell_iff.mp hs
    exact Finset.mem_Icc.mpr ⟨h'.1,h'.2.1⟩
  simpa [Nat.card_Icc] using Finset.card_le_card h

private theorem shell_weight_bounds (H : ℕ) : 0 ≤ shellWeight H ∧ shellWeight H ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun _ _ => by positivity),?_⟩
  rw [shellWeight_eq]
  linarith [show 0 ≤ ((2:ℝ)^H)⁻¹ by positivity]

private theorem half_le_shell_weight {H : ℕ} (h : 0 < H) : 1/2 ≤ shellWeight H := by
  have hh : (2:ℝ) ≤ (2:ℝ)^H := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show 1≤H from h))
  rw [shellWeight_eq]
  have he := inv_anti₀ (by norm_num : (0:ℝ)<2) hh
  norm_num at he ⊢
  linarith

theorem shell_long_error_power_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X y : ℕ) (A : Finset ℕ), 1 ≤ X →
      A ⊆ upperOddShell X → (∑ n ∈ A,muR n) = 0 →
      |shellLongContribution X (Nat.log 2 X) y (upperOddShell X \ A) -
          shellWeight (Nat.log 2 X)*(M X)^2| ≤ K*(X:ℝ)^(1+δ) := by
  let K : ℝ := 1+2/(δ*Real.log 2)
  have hl2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro X y A hX hA hb
  let H := Nat.log 2 X
  let w := shellWeight H
  have hXp : 0 < (X:ℝ) := Nat.cast_pos.mpr (by omega)
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast hX
  have h := complement_long_pair_bound hA hb H y
  have hc : ((nonzeroMobius (upperOddShell X \ A)).card:ℝ) ≤ (X:ℝ) := by
    exact_mod_cast nonzero_shell_card_le (X := X) A
  have hLog := (shell_log_mul_le X hX).trans (Real.log_le_rpow_div hXp.le hδ)
  have hH : (H:ℝ) ≤ (X:ℝ)^δ/(δ*Real.log 2) := by
    rw [← _root_.div_div]
    exact (le_div_iff₀ hl2).mpr hLog
  have hw := shell_weight_bounds H
  have hXpδ : 1 ≤ (X:ℝ)^δ := Real.one_le_rpow hX1 hδ.le
  have hH' : 1+2*(H:ℝ) ≤ K*(X:ℝ)^δ := by
    calc
      _ ≤ (X:ℝ)^δ+2*((X:ℝ)^δ/(δ*Real.log 2)) := by linarith
      _ = _ := by dsimp [K]; ring
  exact h.trans (calc
    _ ≤ 1*(K*(X:ℝ)^δ)*(X:ℝ) := by gcongr; exact hw.2
    _ = K*(X:ℝ)^(1+δ) := by rw [Real.rpow_add hXp,Real.rpow_one]; ring)

theorem shell_long_growth_iff_RH : ShellLongGrowth ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_mertens
    apply mertensCancellation_of_natural_power_bounds
    intro ε hε
    let δ := 2*ε
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨K,hK,hB⟩ := h δ hδ
    obtain ⟨L,hL,hE⟩ := shell_long_error_power_bound hδ
    let C := Real.sqrt (2*(K+L))
    refine ⟨max C 1,by positivity,?_⟩
    intro X hX
    by_cases hX2 : 2 ≤ X
    · let H := Nat.log 2 X
      let w := shellWeight H
      let R := shellLongContribution X H 0 (upperOddShell X)
      have hXp : 0 < (X:ℝ) := Nat.cast_pos.mpr (by omega)
      have hr : |R| ≤ K*(X:ℝ)^(1+δ) := by
        simpa [R,H] using hB X 0 ∅ hX (by simp) (by simp)
      have herr : |R-w*(M X)^2| ≤ L*(X:ℝ)^(1+δ) := by
        simpa [R,H,w] using hE X 0 ∅ hX (by simp) (by simp)
      have hw : (1/2:ℝ) ≤ w := half_le_shell_weight (Nat.log_pos (by norm_num) hX2)
      have hMW : w*(M X)^2 ≤ (K+L)*(X:ℝ)^(1+δ) := by
        have hl := le_abs_self R
        have hle := neg_le_abs (R-w*(M X)^2)
        linarith
      have hM2 : (M X)^2 ≤ 2*(K+L)*(X:ℝ)^(1+δ) := by
        nlinarith only [hMW,mul_le_mul_of_nonneg_right hw (sq_nonneg (M X))]
      have hpow : ((X:ℝ)^(1/2+ε))^2 = (X:ℝ)^(1+δ) := by
        rw [pow_two,← Real.rpow_add hXp]
        congr 1
        dsimp [δ]
        ring
      have hM0 : |M X| ≤ C*(X:ℝ)^(1/2+ε) := by
        apply le_of_pow_le_pow_left₀ (by norm_num : (2:ℕ) ≠ 0) (by positivity)
        rw [sq_abs,mul_pow,Real.sq_sqrt (show (0:ℝ) ≤ 2*(K+L) by positivity),hpow]
        exact hM2
      exact hM0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have h1 : X = 1 := by omega
      subst X
      have hM : M 1 = 1 := by simp [M,muR]
      simpa [hM] using (le_max_right C (1:ℝ))
  · intro hRH δ hδ
    obtain ⟨K,hK,hM⟩ := natural_mertens_bounds_of_RH hRH (δ/2) (by linarith)
    obtain ⟨L,hL,hE⟩ := shell_long_error_power_bound hδ
    refine ⟨K^2+L,by positivity,?_⟩
    intro X y A hX hA hz
    let w := shellWeight (Nat.log 2 X)
    let R := shellLongContribution X (Nat.log 2 X) y (upperOddShell X \ A)
    have hXp : 0 < (X:ℝ) := Nat.cast_pos.mpr (by omega)
    have hpow : ((X:ℝ)^(1/2+δ/2))^2 = (X:ℝ)^(1+δ) := by
      rw [pow_two,← Real.rpow_add hXp]
      congr 1
      ring
    have hM2 := pow_le_pow_left₀ (abs_nonneg (M X)) (hM X hX) 2
    rw [sq_abs,mul_pow,hpow] at hM2
    have hw := shell_weight_bounds (Nat.log 2 X)
    have hAerr := hE X y A hX hA hz
    have hre : R = (R-w*(M X)^2)+w*(M X)^2 := by ring
    change |R| ≤ _
    rw [hre]
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (mul_nonneg hw.1 (sq_nonneg _))]
    have hB : w*(M X)^2 ≤ K^2*(X:ℝ)^(1+δ) := by
      exact ((mul_le_mul_of_nonneg_right hw.2 (sq_nonneg _)).trans_eq (one_mul _)).trans hM2
    linarith

end RHConnections.ArithmeticFourierShell
