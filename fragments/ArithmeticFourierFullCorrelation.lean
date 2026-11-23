import Verified

open ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierShortBlocks
open ArithmeticFourierInversion

private def logDeriv (u : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  u.pmul ArithmeticFunction.log

private theorem logDeriv_mul (u v : ArithmeticFunction ℝ) :
    logDeriv (u*v) = logDeriv u*v + u*logDeriv v := by
  ext n
  simp only [logDeriv,ArithmeticFunction.pmul_apply,ArithmeticFunction.add_apply,
    ArithmeticFunction.mul_apply,ArithmeticFunction.log_apply,Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨he,hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hp1 : p.1 ≠ 0 := fun h => hn (by simpa [h] using he.symm)
  have hp2 : p.2 ≠ 0 := fun h => hn (by simpa [h] using he.symm)
  rw [← he,Nat.cast_mul,Real.log_mul (by exact_mod_cast hp1) (by exact_mod_cast hp2)]
  ring

private theorem logDeriv_one : logDeriv (1 : ArithmeticFunction ℝ) = 0 := by
  ext n
  by_cases hn : n = 1 <;>
    simp [logDeriv,ArithmeticFunction.pmul_apply,ArithmeticFunction.log_apply,hn]

private def Z : ArithmeticFunction ℝ := ↑ArithmeticFunction.zeta

private theorem logDeriv_zeta : logDeriv Z = vonMangoldt*Z := by
  rw [Z,ArithmeticFunction.vonMangoldt_mul_zeta,logDeriv,ArithmeticFunction.pmul_comm,
    ArithmeticFunction.pmul_zeta]

private theorem logDeriv_mu : logDeriv muR = -(muR*vonMangoldt) := by
  have hz : muR*Z = 1 := coe_moebius_mul_coe_zeta
  have h := logDeriv_mul muR Z
  rw [hz,logDeriv_one,logDeriv_zeta,← mul_assoc] at h
  have hm := congrArg (fun u : ArithmeticFunction ℝ => u*muR) h
  rw [zero_mul,add_mul,mul_assoc (logDeriv muR),mul_assoc (muR*vonMangoldt),
    mul_comm Z muR,hz] at hm
  simp only [mul_one] at hm
  exact eq_neg_of_add_eq_zero_left hm.symm

private theorem logDeriv_g (B : ℕ) : logDeriv (g B) = g B*((g B).pmul vonMangoldt) := by
  calc
    _ = (g B).pmul (Z*vonMangoldt) := by
      rw [Z,mul_comm,ArithmeticFunction.vonMangoldt_mul_zeta]; rfl
    _ = _ := by rw [← twist_convolution,Z,ArithmeticFunction.pmul_zeta]

private def centeredAR (B : ℕ) : ArithmeticFunction ℝ :=
  vonMangoldt - (g B).pmul vonMangoldt - Z

private theorem centeredAR_apply (B q : ℕ) (hq : q ≠ 0) :
    centeredAR B q = shortWeight B q-1 := by
  simp only [centeredAR,shortWeight,sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply,ArithmeticFunction.pmul_apply,
    Z,ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hq,Nat.cast_one]
  ring

theorem complete_centered_convolution (B : ℕ) :
    centeredAR B * coeff B = -logDeriv (coeff B)-g B := by
  have hz : muR*Z = 1 := coe_moebius_mul_coe_zeta
  unfold coeff
  rw [logDeriv_mul,logDeriv_g,logDeriv_mu]
  have hneg : g B * -(muR*vonMangoldt) = -(g B*(muR*vonMangoldt)) := by
    ext n
    simp only [ArithmeticFunction.mul_apply,ArithmeticFunction.neg_apply,_root_.mul_neg,
      Finset.sum_neg_distrib]
  rw [hneg]
  simp only [centeredAR,_root_.sub_mul,neg_add,neg_neg]
  have hzg : Z*(g B*muR) = g B := by
    calc
      _ = g B*(muR*Z) := by ac_rfl
      _ = _ := by rw [hz,mul_one]
  rw [hzg]
  have hb : vonMangoldt*(g B*muR) = g B*(muR*vonMangoldt) := by ac_rfl
  have hc : (g B).pmul vonMangoldt*(g B*muR) = (g B*(g B).pmul vonMangoldt)*muR := by ac_rfl
  rw [hb,hc]
  abel

theorem complete_centered_cutoff (B X : ℕ) :
    (∑ q ∈ Finset.Ioc 0 X,(shortWeight B q-1)*S B (X/q)) =
      -(∑ n ∈ Finset.Ioc 0 X, coeff B n * Real.log (n:ℝ)) -
        ∑ n ∈ Finset.Ioc 0 X,g B n := by
  calc
    _ = ∑ q ∈ Finset.Ioc 0 X,centeredAR B q * (∑ n ∈ Finset.Ioc 0 (X/q),coeff B n) :=
      Finset.sum_congr rfl (fun _ hq => by rw [centeredAR_apply _ _ (Finset.mem_Ioc.mp hq).1.ne']; rfl)
    _ = ∑ n ∈ Finset.Ioc 0 X, (centeredAR B * coeff B) n :=
      (ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (centeredAR B) (coeff B) X).symm
    _ = _ := by
      rw [complete_centered_convolution]
      simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply,logDeriv,
        ArithmeticFunction.pmul_apply,ArithmeticFunction.log_apply,Finset.sum_add_distrib,
        Finset.sum_neg_distrib]

end RHConnections.ArithmeticFourierShortBlocks
