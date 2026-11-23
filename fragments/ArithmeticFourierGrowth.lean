import Verified
import Mathlib.Analysis.PSeries

noncomputable section
namespace RHConnections.ArithmeticFourierInversion

def NaturalPowerBound (F : ℕ → ℝ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |F n| ≤ C*(n:ℝ)^θ

theorem abs_g_le (B k : ℕ) : |g B k| ≤ 1/(k:ℝ) := by
  rw [g_apply]
  have hk : 0 ≤ (k : ℝ)⁻¹ := by positivity
  split_ifs
  · rw [abs_of_nonneg hk, one_div]
  · rw [abs_zero, one_div]
    exact hk

theorem abs_h_le (B k : ℕ) : |h B k| ≤ 1/(k:ℝ) := by
  rw [h_apply]
  split_ifs
  · rw [abs_div, show |(k : ℝ)| = (k : ℝ) from abs_of_nonneg (Nat.cast_nonneg k)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
  · simp

theorem quotient_sum_power_bound {F G w : ℕ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hw : ∀ k : ℕ, |w k| ≤ 1/(k:ℝ))
    (hG : ∀ n, G n = ∑ k ∈ Finset.Ioc 0 n, w k * F (n/k))
    (hF : NaturalPowerBound F θ) : NaturalPowerBound G θ := by
  obtain ⟨A,hA,hF⟩ := hF
  let p (k : ℕ) := 1/(k:ℝ)^(1+θ)
  have hp : Summable p := Real.summable_one_div_nat_rpow.mpr (by linarith)
  refine ⟨A * ∑' k, p k, mul_nonneg hA (tsum_nonneg fun k => by dsimp [p]; positivity), ?_⟩
  intro n hn
  have hterm (k : ℕ) (hk : k ∈ Finset.Ioc 0 n) :
      |w k * F (n/k)| ≤ (A*(n:ℝ)^θ)*p k := by
    have hi := Finset.mem_Ioc.mp hk
    have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr hi.1
    have hq : |F (n/k)| ≤ A*((n:ℝ)/(k:ℝ))^θ :=
      (hF _ (Nat.div_pos hi.2 hi.1)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le hθ.le) hA)
    rw [abs_mul]
    calc
      _ ≤ (1/(k:ℝ))*(A*((n:ℝ)/(k:ℝ))^θ) :=
        mul_le_mul (hw k) hq (abs_nonneg _) (by positivity)
      _ = _ := by
        dsimp only [p]
        rw [Real.div_rpow (Nat.cast_nonneg n) hk'.le, Real.rpow_add hk', Real.rpow_one]
        simp only [div_eq_mul_inv, _root_.mul_inv_rev]
        ring
  rw [hG n]
  calc
    _ ≤ ∑ k ∈ Finset.Ioc 0 n, |w k * F (n/k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ioc 0 n, (A*(n:ℝ)^θ)*p k := Finset.sum_le_sum hterm
    _ = (A*(n:ℝ)^θ) * ∑ k ∈ Finset.Ioc 0 n, p k := (Finset.mul_sum ..).symm
    _ ≤ (A*(n:ℝ)^θ) * ∑' k, p k := mul_le_mul_of_nonneg_left
      (hp.sum_le_tsum _ (fun k _ => by dsimp [p]; positivity)) (by positivity)
    _ = _ := by ring

theorem M_power_bound_iff_S (B : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    NaturalPowerBound M θ ↔ NaturalPowerBound (S B) θ :=
  ⟨quotient_sum_power_bound hθ (abs_g_le B) (S_from_M B),
    quotient_sum_power_bound hθ (abs_h_le B) (M_from_S B)⟩

theorem M_all_epsilon_iff_S (B : ℕ) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |M n| ≤ C*(n:ℝ)^(1/2+ε)) ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |S B n| ≤ C*(n:ℝ)^(1/2+ε)) :=
  ⟨fun h ε hε => (M_power_bound_iff_S B (by linarith : 0 < 1/2+ε)).mp (h ε hε),
    fun h ε hε => (M_power_bound_iff_S B (by linarith : 0 < 1/2+ε)).mpr (h ε hε)⟩

#print axioms M_power_bound_iff_S
#print axioms M_all_epsilon_iff_S
end RHConnections.ArithmeticFourierInversion
