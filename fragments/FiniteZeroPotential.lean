import Verified
import ZeroPrimitiveBounds

noncomputable section
open Set
namespace RHConnections.LocalModeContrast

def finiteZeroPotential {ι : Type*} (s : Finset ι) (rho : ι → ℂ) (mult : ι → ℝ)
    (x : ℝ) : ℂ :=
  ∑ i∈s,(mult i:ℂ)*zeroPrimitive (rho i) x

theorem finite_zero_potential_lipschitz {ι : Type*} (s : Finset ι)
    (rho : ι → ℂ) (mult : ι → ℝ) (hr : ∀ i∈s,rho i≠0)
    (hbeta : ∀ i∈s,(rho i).re≤1) (hm : ∀ i∈s,0≤mult i)
    {Q a b : ℝ} (hQ : 0<Q) (ha : Q≤a) (hb : Q≤b) :
    ‖finiteZeroPotential s rho mult a-finiteZeroPotential s rho mult b‖ ≤
      |a-b| *(∑ i∈s,mult i*Q^((rho i).re-1)) := by
  have hterm (i) (hi : i∈s) :
      ‖zeroPrimitive (rho i) a-zeroPrimitive (rho i) b‖ ≤
        |a-b| *Q^((rho i).re-1) := by
    rcases le_total a b with hab | hba
    · rw [norm_sub_rev,abs_of_nonpos (sub_nonpos.mpr hab),neg_sub]
      exact zero_interval_length_bound (hr i hi) (hbeta i hi) hQ ha hab
    · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
      exact zero_interval_length_bound (hr i hi) (hbeta i hi) hQ hb hba
  unfold finiteZeroPotential
  rw [←Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hm i hi)]
  exact (mul_le_mul_of_nonneg_left (hterm i hi) (hm i hi)).trans_eq (by ring)

theorem finite_zero_potential_high_height {ι : Type*} (s : Finset ι)
    (rho : ι → ℂ) (mult : ι → ℝ)
    (hbeta : ∀ i∈s,0≤(rho i).re ∧ (rho i).re≤1) (hm : ∀ i∈s,0≤mult i)
    {Q a b T : ℝ} (hQ : 0<Q) (ha : a∈Icc Q (2*Q)) (hb : b∈Icc Q (2*Q))
    (hT : 0<T) (ht : ∀ i∈s, T≤ |(rho i).im|) :
    ‖finiteZeroPotential s rho mult b-finiteZeroPotential s rho mult a‖ ≤
      (4*Q/T)*(∑ i∈s,mult i*Q^((rho i).re-1)) := by
  unfold finiteZeroPotential
  rw [←Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hm i hi)]
  have h := zero_interval_height_bound (hbeta i hi).1 (hbeta i hi).2 hQ ha hb
    (hT.trans_le (ht i hi))
  have he : Q^((rho i).re)=Q*Q^((rho i).re-1) := by
    calc
      _ = Q^(1+((rho i).re-1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hQ,Real.rpow_one]
  calc
    _ ≤ mult i*(4*Q^((rho i).re)/ |(rho i).im|) := mul_le_mul_of_nonneg_left h (hm i hi)
    _ ≤ mult i*(4*Q^((rho i).re)/T) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hT (ht i hi)) (hm i hi)
    _ = _ := by rw [he]; ring

end RHConnections.LocalModeContrast
