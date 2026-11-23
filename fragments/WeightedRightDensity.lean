import Verified
import ExponentialCountTransfer

noncomputable section
namespace RHConnections.PhaseWindow

theorem weighted_rank_density_bound {ι : Type*} (s : Finset ι) (beta : ι → ℝ)
    {Q T C : ℝ} (hQ : 1<Q) (hT : 1≤T) (hTQ : T≤Q^(1/6:ℝ)) (hC : 0≤C)
    (hbeta : ∀ i∈s, 1/2≤beta i ∧ beta i≤1)
    (hIngham : ∀ u : ℝ, 0≤u → u≤1/2 →
      (((s.filter (fun i => 1-u≤beta i)).card:ℕ):ℝ) ≤
        C*(Real.log T)^5*T^(3*u/(1+u))) :
    (∑ i∈s,Q^(beta i-1)) ≤
      (C*(Real.log T)^5*Real.exp (1/2))*(1-Real.exp (-(1/2)))⁻¹ := by
  classical
  let c := C*(Real.log T)^5
  let a (i : ι) := (1-beta i)*Real.log Q
  have hl : 0<Real.log Q := Real.log_pos hQ
  have hq : 0<Q := zero_lt_one.trans hQ
  have hc : 0≤c := by dsimp [c]; positivity [Real.log_nonneg hT]
  have hcases (u : ℝ) (hu : 0≤u) :
      ((s.filter (fun i => 1-u≤beta i)).card:ℝ)≤c*Q^(u/2) := by
    by_cases h : u≤1/2
    · have hu3 : 0≤3*u/(1+u) := by positivity
      have hun : 3*u/(1+u)≤3*u := div_le_self (by positivity) (by linarith)
      calc
        _ ≤ c*T^(3*u/(1+u)) := hIngham u hu h
        _ ≤ c*(Q^(1/6:ℝ))^(3*u/(1+u)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (zero_le_one.trans hT) hTQ hu3) hc
        _ = c*Q^((1/6:ℝ)*(3*u/(1+u))) := by rw [Real.rpow_mul hq.le]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith only [hun])) hc
    · have hAll : s.filter (fun i => 1-(1/2:ℝ)≤beta i)=s := by
        apply Finset.filter_true_of_mem
        intro i hi
        linarith only [(hbeta i hi).1]
      have hhalf : (s.card:ℝ)≤c*Q^((1/2:ℝ)/2) := by
        have ht := hIngham (1/2) (by norm_num) le_rfl
        rw [hAll] at ht
        have hh : (3*(1/2:ℝ)/(1+1/2))≤3*(1/2:ℝ) := by norm_num
        calc
          _ ≤ c*T^(3*(1/2:ℝ)/(1+1/2)) := ht
          _ ≤ c*(Q^(1/6:ℝ))^(3*(1/2:ℝ)/(1+1/2)) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (zero_le_one.trans hT) hTQ (by norm_num)) hc
          _ = c*Q^((1/6:ℝ)*(3*(1/2:ℝ)/(1+1/2))) := by rw [Real.rpow_mul hq.le]
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith only [hh])) hc
      exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (hhalf.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith)) hc))
  have hcount (v : ℝ) (hv : 0≤v) : ((s.filter (fun i => a i≤v)).card:ℝ)≤c*Real.exp (v/2) := by
    have he : s.filter (fun i => a i≤v) = s.filter (fun i => 1-v/Real.log Q ≤ beta i) := by
      ext i
      constructor
      · intro h
        obtain ⟨hi,hv'⟩ := Finset.mem_filter.mp h
        change (1-beta i)*Real.log Q≤v at hv'
        have hh := (le_div_iff₀ hl).mpr hv'
        exact Finset.mem_filter.mpr ⟨hi,by linarith⟩
      · intro h
        obtain ⟨hi,hb⟩ := Finset.mem_filter.mp h
        refine Finset.mem_filter.mpr ⟨hi,?_⟩
        change (1-beta i)*Real.log Q≤v
        exact (le_div_iff₀ hl).mp (by linarith)
    rw [he]
    refine (hcases (v/Real.log Q) (by positivity)).trans_eq ?_
    rw [Real.rpow_def_of_pos hq]
    congr 2
    field_simp
    <;> ring
  have h := weighted_exponential_from_counts s a
    (fun i hi => mul_nonneg (sub_nonneg.mpr (hbeta i hi).2) hl.le) hc hcount
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos hq]
  congr 1
  dsimp [a]
  ring

end RHConnections.PhaseWindow
