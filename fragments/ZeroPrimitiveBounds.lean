import Verified
import ZeroPrimitiveMean

noncomputable section
open Set MeasureTheory
namespace RHConnections.LocalModeContrast

theorem log_mode_norm (rho : ℂ) {x : ℝ} (hx : 0<x) :
    ‖logMode rho x‖ = x^(rho.re-1) := by
  rw [logMode,Complex.norm_exp,Real.rpow_def_of_pos hx]
  simp [Complex.mul_re,mul_comm]

theorem zero_primitive_norm (rho : ℂ) {x : ℝ} (hx : 0<x) :
    ‖zeroPrimitive rho x‖ = x^rho.re / ‖rho‖ := by
  rw [zeroPrimitive,norm_div,Complex.norm_exp,Real.rpow_def_of_pos hx]
  simp [Complex.mul_re,mul_comm]

theorem zero_interval_length_bound {rho : ℂ} (hr : rho≠0) (hbeta : rho.re≤1)
    {Q a b : ℝ} (hQ : 0<Q) (ha : Q≤a) (hab : a≤b) :
    ‖zeroPrimitive rho b-zeroPrimitive rho a‖ ≤ (b-a)*Q^(rho.re-1) := by
  rw [zero_primitive_difference_eq_mean hr (hQ.trans_le ha) (hQ.trans_le (ha.trans hab)),norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)]
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
  unfold normalizedMean
  have hh : ∀ s ∈ Icc (0:ℝ) 1, Q≤segment a b s := by
    intro s hs
    dsimp [segment]
    nlinarith only [ha, mul_nonneg hs.1 (sub_nonneg.mpr hab)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := (1:ℝ))
    (f := fun s => logMode rho (segment a b s)) (C := Q^(rho.re-1)) (by
      intro s hs
      rw [uIoc_of_le zero_le_one] at hs
      have h := hh s ⟨hs.1.le,hs.2⟩
      rw [log_mode_norm rho (hQ.trans_le h)]
      exact Real.rpow_le_rpow_of_nonpos hQ h (sub_nonpos.mpr hbeta))
  simpa using hi

theorem zero_interval_height_bound {rho : ℂ} (hbeta : 0≤rho.re) (hbeta1 : rho.re≤1)
    {Q a b : ℝ} (hQ : 0<Q) (ha : a∈Icc Q (2*Q)) (hb : b∈Icc Q (2*Q))
    (hgamma : 0< |rho.im|) :
    ‖zeroPrimitive rho b-zeroPrimitive rho a‖ ≤ 4*Q^rho.re/ |rho.im| := by
  have hpow : (2:ℝ)^rho.re≤2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ)≤2) hbeta1
  have hn (x : ℝ) (hx : x∈Icc Q (2*Q)) : ‖zeroPrimitive rho x‖ ≤ 2*Q^rho.re/ |rho.im| := by
    rw [zero_primitive_norm rho (hQ.trans_le hx.1)]
    have h1 := Real.rpow_le_rpow (hQ.le.trans hx.1) hx.2 hbeta
    have hd : |rho.im|≤‖rho‖ := Complex.abs_im_le_norm rho
    have h2 : x^rho.re≤2*Q^rho.re := by
      refine h1.trans ?_
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hQ.le]
      exact mul_le_mul_of_nonneg_right hpow (by positivity)
    exact (div_le_div_of_nonneg_right h2 (hgamma.trans_le hd).le).trans
      (div_le_div_of_nonneg_left (by positivity) hgamma hd)
  exact ((norm_sub_le _ _).trans (add_le_add (hn b hb) (hn a ha))).trans_eq (by ring)

end RHConnections.LocalModeContrast
