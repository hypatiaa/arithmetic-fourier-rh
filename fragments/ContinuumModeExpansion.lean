import Verified
import ZeroPrimitiveMean
import RankGroupMean

noncomputable section
open Set
namespace RHConnections.RankContrast
open LocalModeContrast

variable {ι κ : Type*}

theorem mean_mul_const (A : Finset ι) (c : ℂ) (v : ι → ℂ) :
    mean A (fun i => c*v i) = c*mean A v := by
  simp only [mean,←Finset.mul_sum]
  ring

theorem mean_finite_sum (A : Finset ι) (roots : Finset κ) (f : κ → ι → ℂ) :
    mean A (fun i => ∑ rho∈roots,f rho i)=∑ rho∈roots,mean A (f rho) := by
  unfold mean
  rw [Finset.sum_comm,Finset.sum_div]

def modeContrast (A B : Finset ι) (a b : ι → ℝ) (rho : ℂ) : ℂ :=
  mean A (fun i => normalizedMean (logMode rho) (a i) (b i)) -
    mean B (fun i => normalizedMean (logMode rho) (a i) (b i))

theorem continuum_zero_mode_expansion (A B : Finset ι) (roots : Finset κ)
    (a b : ι → ℝ) (hpos : ∀ i, i∈A ∨ i∈B → 0<a i ∧ a i<b i)
    (rho M : κ → ℂ) (hrho : ∀ r∈roots,rho r≠0) {L₀ : ℝ} (hL : 0<L₀)
    (z : ℝ) :
    let L := L₀*Real.exp z
    let rows (i : ι) := ∑ r∈roots,M r*
      (zeroPrimitive (rho r) (L*b i)-zeroPrimitive (rho r) (L*a i))
    contrast A B (fun i => b i-a i) rows =
      ∑ r∈roots,(M r*Complex.exp (rho r*(Real.log L₀:ℂ))*modeContrast A B a b (rho r))*
        Complex.exp (rho r*(z:ℂ)) := by
  let L := L₀*Real.exp z
  let rows (i : ι) := ∑ r∈roots,M r*
    (zeroPrimitive (rho r) (L*b i)-zeroPrimitive (rho r) (L*a i))
  let f (r : κ) (i : ι) :=
    (M r*Complex.exp (rho r*(Real.log L:ℂ))) * normalizedMean (logMode (rho r)) (a i) (b i)
  have hl : 0<L := by dsimp [L]; positivity
  have hrow (i) (hi : i∈A ∨ i∈B) : rows i / ((b i-a i:ℝ):ℂ) = ∑ r∈roots,f r i := by
    obtain ⟨ha,hab⟩ := hpos i hi
    have hne := Complex.ofReal_ne_zero.mpr (sub_pos.mpr hab).ne'
    unfold rows
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    rw [scaled_zero_primitive_difference (hrho r hr) hl ha (ha.trans hab)]
    dsimp only [f]
    field_simp
    <;> ring
  have hmean (S : Finset ι) (hS : ∀ i∈S, i∈A ∨ i∈B) :
      mean S (fun i => rows i / ((b i-a i:ℝ):ℂ)) =
        ∑ r∈roots,(M r*Complex.exp (rho r*(Real.log L:ℂ)))*
          mean S (fun i => normalizedMean (logMode (rho r)) (a i) (b i)) := by
    rw [show mean S (fun i => rows i/((b i-a i:ℝ):ℂ)) = mean S (fun i => ∑ r∈roots,f r i) by
      unfold mean; rw [Finset.sum_congr rfl (fun i hi => hrow i (hS i hi))] ]
    rw [mean_finite_sum]
    exact Finset.sum_congr rfl (fun r _ => mean_mul_const S _ _)
  change contrast A B (fun i => b i-a i) rows = _
  rw [contrast,hmean A (fun i hi => Or.inl hi),hmean B (fun i hi => Or.inr hi),
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [←mul_sub,show Real.log L=Real.log L₀+z by
    dsimp [L]; rw [Real.log_mul hL.ne' (Real.exp_pos _).ne',Real.log_exp],
    Complex.ofReal_add,mul_add,Complex.exp_add]
  dsimp [modeContrast]
  ring

theorem mode_contrast_lower_near_one (rho : ℂ) (hrho : rho≠1) :
    ∃ R : ℝ, 0<R ∧ ∀ (A B : Finset ι) (hA : A.Nonempty) (hB : B.Nonempty)
      (a b : ι → ℝ) {d : ℝ}, 0<d →
      (∀ i, i∈A ∨ i∈B → a i∈Ioo (1-R) (1+R) ∧ b i∈Ioo (1-R) (1+R)) →
      (∀ i∈A, ∀ j∈B, d≤a i-a j ∧ d≤b i-b j) →
      d*‖rho-1‖/2≤‖modeContrast A B a b rho‖ := by
  obtain ⟨R,hR,hc⟩ := logMode_mean_contrast rho hrho
  refine ⟨R,hR,?_⟩
  intro A B hA hB a b d hd hw hg
  have he := lower_group_contrast A B hA hB
    (fun i => normalizedMean (logMode rho) (a i) (b i)) (rho-1)⁻¹ (d/2) (by
      intro i hi j hj
      obtain ⟨hai,hbi⟩ := hw i (Or.inl hi)
      obtain ⟨haj,hbj⟩ := hw j (Or.inr hj)
      rw [mul_comm,←div_eq_mul_inv]
      exact hc haj hbj hai hbi hd (hg i hi j hj).1 (hg i hi j hj).2)
  have hnorm := he.trans (Complex.re_le_norm _)
  rw [mul_comm,←div_eq_mul_inv,norm_div] at hnorm
  have hpos : 0<‖rho-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hrho)
  exact ((le_div_iff₀ hpos).mp hnorm).trans' (by ring_nf; exact le_rfl)

end RHConnections.RankContrast
