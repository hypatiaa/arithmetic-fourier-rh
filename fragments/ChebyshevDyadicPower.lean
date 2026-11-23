import Verified
import DyadicEndpointPower

noncomputable section
open Filter Asymptotics

namespace RHConnections.DyadicEndpoint
open ChebyshevCriterion

def dyadicChebyshevError (x : ℝ) : ℂ :=
  psiError (2*x)-psiError x

private theorem chebyshev_trivial_error (x : ℝ) (hx : 0≤x) :
    ‖psiError x‖ ≤ (Real.log 4+5)*x := by
  have hpsi : psi x = (Chebyshev.psi x:ℂ) := by
    rw [Chebyshev.psi_eq_sum_Icc,Complex.ofReal_sum]
    unfold psi mangoldtCoeff
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Icc.mp hn).2⟩
    · intro n hn hx
      have hz : n=0 := by
        by_contra hd
        exact hx (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd,(Finset.mem_Icc.mp hn).2⟩)
      simp [hz]
  have hnorm : ‖psi x‖ = Chebyshev.psi x := by
    rw [hpsi,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Chebyshev.psi_nonneg _)]
  have he := norm_sub_le (psi x) (x:ℂ)
  rw [hnorm,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx] at he
  exact he.trans (by linarith [Chebyshev.psi_le_const_mul_self hx])

theorem dyadic_chebyshev_power_iff {θ : ℝ} (hθ : 0<θ) :
    dyadicChebyshevError =O[atTop] (fun x : ℝ => x^θ) ↔
      psiError =O[atTop] (fun x : ℝ => x^θ) := by
  constructor
  · intro h
    obtain ⟨A,hA0,hA⟩ := h.exists_nonneg
    obtain ⟨Y,hY⟩ := eventually_atTop.1 hA.bound
    let W := max 1 Y
    have hW : 1≤W := le_max_left _ _
    have hWp : 0<W := zero_lt_one.trans_le hW
    have hWC (x : ℝ) (hx : 1≤x) : Y≤W*x :=
      (le_max_right _ _).trans (le_mul_of_one_le_right hWp.le hx)
    have hL : 0≤Real.log (4:ℝ)+5 := by linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
    let g (x : ℝ) := psiError (W*x)
    have hbase (x : ℝ) (hx : 1≤x) (hx2 : x<2) :
        ‖g x‖≤(Real.log 4+5)*(2*W) :=
      (chebyshev_trivial_error (W*x) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hx2.le hWp.le]) hL)
    have hstep (x : ℝ) (hx : 1≤x) :
        ‖g (2*x)-g x‖≤(A*W^θ)*x^θ := by
      have hb := hY (W*x) (hWC x hx)
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.mul_rpow hWp.le (by positivity),←mul_assoc] at hb
      change ‖psiError (W*(2*x))-psiError (W*x)‖ ≤ _
      simpa only [dyadicChebyshevError,mul_left_comm W] using hb
    have hmain := power_from_doubling_difference g hθ (show 0≤A*W^θ by positivity)
      (show 0≤(Real.log 4+5)*(2*W) by positivity) hbase hstep
    apply IsBigO.of_bound (((Real.log 4+5)*(2*W)+A*W^θ/(2^θ-1))/W^θ)
    filter_upwards [eventually_ge_atTop W] with x hx
    have hx0 := hWp.le.trans hx
    have hArg : 1≤x/W := (le_div_iff₀ hWp).mpr (by simpa using hx)
    have hh := hmain (x/W) hArg
    dsimp only [g] at hh
    have hEq : W*(x/W)=x := by field_simp
    rw [hEq,Real.div_rpow hx0 hWp.le] at hh
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx0 _),mul_div_assoc,
      div_mul_eq_mul_div] using hh
  · intro h
    obtain ⟨A,hA0,hA⟩ := h.exists_nonneg
    obtain ⟨Y,hY⟩ := eventually_atTop.1 hA.bound
    let W := max 1 Y
    apply IsBigO.of_bound (A*((2:ℝ)^θ+1))
    filter_upwards [eventually_ge_atTop W] with x hx
    have hx1 := (le_max_left (1:ℝ) Y).trans hx
    have hx0 : 0≤x := by linarith
    have hxY := (le_max_right (1:ℝ) Y).trans hx
    have h2x : Y≤2*x := by linarith
    have h1 := hY x hxY
    have h2 := hY (2*x) h2x
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.mul_rpow (by norm_num) hx0] at h2
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)] at h1 ⊢
    exact ((norm_sub_le _ _).trans (add_le_add h2 h1)).trans_eq (by ring)

theorem dyadic_chebyshev_cancellation_iff_RH :
    (∀ ε : ℝ, 0<ε → dyadicChebyshevError =O[atTop] (fun x : ℝ => x^(1/2+ε))) ↔
      RiemannHypothesis := by
  rw [←chebyshev_cancellation_iff_RH]
  unfold ChebyshevCancellation
  constructor
  · intro h ε hε
    exact (dyadic_chebyshev_power_iff (by linarith : (0:ℝ)<1/2+ε)).mp (h ε hε)
  · intro h ε hε
    exact (dyadic_chebyshev_power_iff (by linarith : (0:ℝ)<1/2+ε)).mpr (h ε hε)

end RHConnections.DyadicEndpoint
