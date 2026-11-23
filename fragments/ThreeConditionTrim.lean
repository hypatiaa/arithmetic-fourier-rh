import Verified

noncomputable section
namespace RHConnections.PhaseWindow

def retainedRow {ι : Type*} (roots : Finset ι) (beta gamma : ι → ℝ)
    (term : ι → ℂ) (Q delta s : ℝ) : ℂ :=
  if Q^(-delta)<s then
    ∑ r ∈ roots.filter (fun r => 1-delta<beta r ∧ gamma r<Q^delta),term r
  else 0

theorem discard_three_conditions {ι : Type*} (roots : Finset ι)
    (beta gamma : ι → ℝ) (term : ι → ℂ) {Q delta s L C₁ C₂ : ℝ}
    (hQ : 1≤Q) (hs : 0≤s) (hL : 0≤L) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hg : ∀ r∈roots, 0<gamma r)
    (hlength : ∀ r∈roots, ‖term r‖≤L*Q^(beta r)*s)
    (hheight : ∀ r∈roots, ‖term r‖≤L*Q^(beta r)/(gamma r))
    (hweight : (∑ r∈roots,Q^(beta r-1)) ≤ C₁)
    (hheightSum : (∑ r∈roots,(gamma r)⁻¹) ≤ C₂) :
    ‖(∑ r∈roots,term r)-retainedRow roots beta gamma term Q delta s‖ ≤
      L*Q^(1-delta)*(C₁+C₂) := by
  classical
  have hQp : 0<Q := zero_lt_one.trans_le hQ
  let W := Q^(1-delta)
  have hW : 0≤W := Real.rpow_nonneg hQp.le _
  have hpow (r : ι) : Q^(beta r)*Q^(-delta)=W*Q^(beta r-1) := by
    rw [←Real.rpow_add hQp,←Real.rpow_add hQp]
    congr 1
    ring
  by_cases hlong : Q^(-delta)<s
  · rw [retainedRow,ite_eq_left hlong,Finset.sum_filter,←Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hbound (r) (hr : r∈roots) :
        ‖term r-(if 1-delta<beta r ∧ gamma r<Q^delta then term r else 0)‖ ≤
          (L*W)*(Q^(beta r-1)+(gamma r)⁻¹) := by
      by_cases hk : 1-delta<beta r ∧ gamma r<Q^delta
      · rw [ite_eq_left hk,sub_self,norm_zero]
        exact mul_nonneg (mul_nonneg hL hW) (add_nonneg (by positivity) (inv_nonneg.mpr (hg r hr).le))
      rw [ite_eq_right hk,sub_zero]
      by_cases hb : beta r≤1-delta
      · have hp : Q^(beta r)≤W := Real.rpow_le_rpow_of_exponent_le hQ hb
        calc
          _ ≤ L*Q^(beta r)/(gamma r) := hheight r hr
          _ ≤ (L*W)*(gamma r)⁻¹ := by
            rw [←div_eq_mul_inv]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hL) (hg r hr).le
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
      · have hrγ : Q^delta≤gamma r :=
          le_of_not_gt (fun hc => hk ⟨lt_of_not_ge hb,hc⟩)
        calc
          _ ≤ L*Q^(beta r)/(gamma r) := hheight r hr
          _ ≤ L*Q^(beta r)/Q^delta :=
            div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hQp _) hrγ
          _ = (L*W)*Q^(beta r-1) := by
            rw [div_eq_mul_inv,←Real.rpow_neg hQp.le,mul_assoc,hpow r]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (inv_nonneg.mpr (hg r hr).le)) (by positivity)
    calc
      _ ≤ ∑ r∈roots,(L*W)*(Q^(beta r-1)+(gamma r)⁻¹) := Finset.sum_le_sum hbound
      _ = (L*W)*((∑ r∈roots,Q^(beta r-1))+(∑ r∈roots,(gamma r)⁻¹)) := by
        rw [←Finset.mul_sum,Finset.sum_add_distrib]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hweight hheightSum) (by positivity)
  · rw [retainedRow,ite_eq_right hlong,sub_zero]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ r∈roots,L*Q^(beta r)*Q^(-delta) :=
        Finset.sum_le_sum (fun r hr => (hlength r hr).trans
          (mul_le_mul_of_nonneg_left (le_of_not_gt hlong) (by positivity)))
      _ = (L*W)*(∑ r∈roots,Q^(beta r-1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [mul_assoc,hpow r,←mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hweight.trans (le_add_of_nonneg_right hC₂)) (by positivity)

end RHConnections.PhaseWindow
