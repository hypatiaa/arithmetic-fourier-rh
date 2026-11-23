import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section
namespace RHConnections.ArithmeticFourierInversion

def g (B : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k.Coprime B then (k : ℝ)⁻¹ else 0, by simp⟩

theorem g_apply (B k : ℕ) : g B k = if k.Coprime B then (k : ℝ)⁻¹ else 0 := rfl

theorem g_mul (B j k : ℕ) : g B (j*k) = g B j * g B k := by
  simp only [g_apply, Nat.coprime_mul_iff_left, Nat.cast_mul]
  by_cases hj : j.Coprime B <;> by_cases hk : k.Coprime B
  · simp only [if_pos (And.intro hj hk), if_pos hj, if_pos hk, _root_.mul_inv_rev] <;> ring
  all_goals simp [hj,hk,mul_comm]

def muR : ArithmeticFunction ℝ := ↑ArithmeticFunction.moebius

def h (B : ℕ) : ArithmeticFunction ℝ := (g B).pmul muR

theorem h_apply (B k : ℕ) :
    h B k = if k.Coprime B then (ArithmeticFunction.moebius k : ℝ) / k else 0 := by
  simp only [h, ArithmeticFunction.pmul_apply, g_apply]
  by_cases hk : k.Coprime B <;> simp [hk, muR, div_eq_mul_inv, mul_comm]

theorem twist_convolution (B : ℕ) (u v : ArithmeticFunction ℝ) :
    (g B).pmul u * (g B).pmul v = (g B).pmul (u*v) := by
  ext n
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he : p.1*p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← he, g_mul]
  ring

theorem g_convolution_h (B : ℕ) : g B * h B = 1 := by
  have he := twist_convolution B (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) muR
  rw [ArithmeticFunction.pmul_zeta, show
    (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)*muR=1 from
      ArithmeticFunction.coe_zeta_mul_coe_moebius] at he
  rw [h, he]
  ext n
  by_cases hn : n = 1
  · subst n
    simp [ArithmeticFunction.pmul_apply, g_apply]
  · simp [ArithmeticFunction.pmul_apply,ArithmeticFunction.one_apply,hn]

def M (n : ℕ) : ℝ := ∑ j ∈ Finset.Ioc 0 n, muR j

def S (B n : ℕ) : ℝ := ∑ j ∈ Finset.Ioc 0 n, (g B * muR) j

theorem S_from_M (B n : ℕ) :
    S B n = ∑ k ∈ Finset.Ioc 0 n, g B k * M (n/k) :=
  ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (g B) muR n

theorem M_from_S (B n : ℕ) :
    M n = ∑ k ∈ Finset.Ioc 0 n, h B k * S B (n/k) := by
  have hi : h B * (g B * muR) = muR := by
    rw [← mul_assoc, mul_comm (h B) (g B), g_convolution_h, one_mul]
  calc
    M n = ∑ j ∈ Finset.Ioc 0 n, (h B * (g B * muR)) j := by rw [hi]; rfl
    _ = _ := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (h B) (g B * muR) n

#print axioms g_convolution_h
#print axioms S_from_M
#print axioms M_from_S
end RHConnections.ArithmeticFourierInversion
