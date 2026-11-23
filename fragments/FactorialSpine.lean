import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.Ring

open Finset
open scoped ArithmeticFunction.vonMangoldt
noncomputable section
namespace RHConnections.FactorialSpine

theorem log_factorial (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ n ∈ Ioc 0 N, Real.log (n : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), ih,
      Finset.sum_Ioc_succ_top (Nat.zero_le N)]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem legendre_log_factorial (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Λ n * (N / n : ℕ) = Real.log (N.factorial : ℝ) := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.vonMangoldt) N
  rw [ArithmeticFunction.vonMangoldt_mul_zeta] at h
  rw [log_factorial]
  exact h.symm

def fractional (x : ℝ) : ℝ := x - (⌊x⌋₊ : ℝ)

theorem fractional_eq_fract {x : ℝ} (hx : 0 ≤ x) : fractional x = Int.fract x := by
  rw [fractional, natCast_floor_eq_intCast_floor hx, Int.fract]

theorem decomposition (y : ℝ) :
    (∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (y / (n : ℝ) - 1)) =
      Real.log ((⌊y⌋₊).factorial : ℝ) +
      (∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * fractional (y / (n : ℝ))) -
      ∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n := by
  rw [← legendre_log_factorial]
  simp only [fractional, Nat.floor_div_natCast]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem decomposition_fract {y : ℝ} (hy : 0 ≤ y) :
    (∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (y / (n : ℝ) - 1)) =
      Real.log ((⌊y⌋₊).factorial : ℝ) +
      (∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * Int.fract (y / (n : ℝ))) -
      ∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n := by
  have hf : ∀ n : ℕ, fractional (y / (n : ℝ)) = Int.fract (y / (n : ℝ)) :=
    fun n => fractional_eq_fract (div_nonneg hy (Nat.cast_nonneg n))
  simpa only [hf] using decomposition y

#print axioms log_factorial
#print axioms legendre_log_factorial
#print axioms decomposition
#print axioms decomposition_fract
end RHConnections.FactorialSpine
