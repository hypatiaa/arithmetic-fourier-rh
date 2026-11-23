import Verified

noncomputable section
namespace RHConnections.RankContrast

theorem quarter_row_cost_algebra {m t n₁ n₂ U E : ℝ}
    (hm : 0<m) (hmt : m≤t) (hn₁ : m/8≤n₁) (hn₂ : m/8≤n₂)
    (hU : 0≤U) (hE : 0≤E) :
    (U*Real.sqrt t)*((Real.sqrt n₁*(m/(2*t)))⁻¹+(Real.sqrt n₂*(m/(2*t)))⁻¹)
        +2*E/(m/(2*t)) ≤
      (12*U+4*E)*(t/m)*Real.sqrt (t/m) := by
  have ht := hm.trans_le hmt
  have hrootm : 0<Real.sqrt m := Real.sqrt_pos_of_pos hm
  have hroot (n : ℝ) (hn : m/8≤n) : Real.sqrt m/3≤Real.sqrt n := by
    apply (Real.le_sqrt (by positivity) (by linarith)).mpr
    rw [div_pow,Real.sq_sqrt hm.le]
    linarith
  have hinv (n : ℝ) (hn : m/8≤n) :
      (Real.sqrt n*(m/(2*t)))⁻¹≤6*t/(m*Real.sqrt m) := by
    have hsmall : 0<(Real.sqrt m/3)*(m/(2*t)) := by positivity
    have hm' := mul_le_mul_of_nonneg_right (hroot n hn) (by positivity : 0≤m/(2*t))
    refine (inv_anti₀ hsmall hm').trans_eq ?_
    field_simp
    <;> ring
  have h := add_le_add (hinv n₁ hn₁) (hinv n₂ hn₂)
  have h₁ : (U*Real.sqrt t)*((Real.sqrt n₁*(m/(2*t)))⁻¹+(Real.sqrt n₂*(m/(2*t)))⁻¹)
      ≤ (12*U)*(t/m)*Real.sqrt (t/m) := by
    refine (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_
    rw [Real.sqrt_div ht.le]
    field_simp
    <;> ring
  have hratio : 1≤t/m := (le_div_iff₀ hm).mpr (by simpa using hmt)
  have hroot1 : 1≤Real.sqrt (t/m) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hratio
  have h₂ : 2*E/(m/(2*t))≤(4*E)*(t/m)*Real.sqrt (t/m) := by
    rw [show 2*E/(m/(2*t))=(4*E)*(t/m) by field_simp <;> ring]
    exact le_mul_of_one_le_right (by positivity) hroot1
  exact (add_le_add h₁ h₂).trans_eq (by ring)

theorem ratio_cost_to_power {t m K C Q beta delta : ℝ}
    (hm : 0<m) (ht : 0<t) (hQ : 0<Q)
    (hK : 0<K) (hC : 0≤C)
    (h : K*Q^beta*(m/t) ≤ C*Q^(1-delta)*(t/m)*Real.sqrt (t/m)) :
    Q^beta*(m/t)^(5/2:ℝ) ≤ (C/K)*Q^(1-delta) := by
  let d := m/t
  have hd : 0<d := by positivity
  have hInv : t/m=d⁻¹ := by dsimp [d]; rw [inv_div]
  have hEq : (t/m)*Real.sqrt (t/m)*d^(3/2:ℝ)=1 := by
    have hInv' : t/m=d^(-1:ℝ) := by rw [Real.rpow_neg_one,hInv]
    have hS : Real.sqrt (t/m)=d^(-(1/2):ℝ) := by
      rw [Real.sqrt_eq_rpow,hInv',←Real.rpow_mul hd.le]
      congr 1
      ring
    rw [hS,hInv',←Real.rpow_add hd,←Real.rpow_add hd]
    rw [show (-1:ℝ)+ -(1/2)+3/2=0 by norm_num,Real.rpow_zero]
  have h' := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hd.le (3/2:ℝ))
  change K*Q^beta*d*d^(3/2:ℝ)≤C*Q^(1-delta)*(t/m)*Real.sqrt (t/m)*d^(3/2:ℝ) at h'
  calc
    _ ≤ (C/K)*Q^(1-delta) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hK).mpr
      have hleft : K*Q^beta*d*d^(3/2:ℝ) = (Q^beta*d^(5/2:ℝ))*K := by
        calc
          _ = (Q^beta*(d^(1:ℝ)*d^(3/2:ℝ)))*K := by rw [Real.rpow_one]; ring
          _ = _ := by rw [←Real.rpow_add hd,show (1:ℝ)+3/2=5/2 by norm_num]
      have hright : C*Q^(1-delta)*(t/m)*Real.sqrt (t/m)*d^(3/2:ℝ) = C*Q^(1-delta) := by
        calc
          _ = C*Q^(1-delta)*((t/m)*Real.sqrt (t/m)*d^(3/2:ℝ)) := by ring
          _ = _ := by rw [hEq,mul_one]
      rw [hleft,hright] at h'
      linarith

end RHConnections.RankContrast
