import Verified
import RieszPrimeMellin

noncomputable section
open MeasureTheory Filter Asymptotics
namespace RHConnections.RieszPrimeMellin
open PoleCompensation PrimeErrorLaplace PositiveSummatory ChebyshevCriterion

theorem zero_free_of_one_sided_riesz_power {a σ C : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hσ : σ=1 ∨ σ= -1)
    (hC : ∀ x>1, 0≤σ*rieszError x*x^(-a)+C) :
    ∀ s : ℂ, a<s.re → riemannZeta s≠0 := by
  let G (s : ℂ) := (regularizedLogDerivative s-1)/(s+1)
  have hG (b : ℝ) (hb : 0<b) : AnalyticAt ℂ G (b:ℂ) := by
    have hn : (b:ℂ)+1≠0 := by
      intro h
      have hh := congrArg Complex.re h
      simp [Complex.add_re] at hh
      linarith
    exact ((regularizedLogDerivative_analytic (regularized_zeta_ne_zero_positive_real hb)).sub
      analyticAt_const).div (analyticAt_id.add analyticAt_const) hn
  obtain ⟨A,hA,hEq⟩ := signed_power_mellin_extension (G := G) rieszError_measurable hG
    (fun s hs => by
      obtain ⟨hi,h⟩ := riesz_error_mellin hs
      refine ⟨hi,?_⟩
      have hn : s≠1 := by intro h; simp [h] at hs
      rw [h,prime_error_euler_integral hs]
      dsimp [G]
      rw [regularizedLogDerivative_eq hn (riemannZeta_ne_zero_of_one_le_re hs.le)]
      ring) ha ha1 hσ hC
  let H (s : ℂ) := (s+1)*A s+1
  have hH : AnalyticOnNhd ℂ H {s : ℂ | a<s.re} := fun s hs =>
    ((analyticAt_id.add analyticAt_const).mul (hA s hs)).add analyticAt_const
  intro s hs
  apply zeta_zero_free_above_compensated_extension ha1 hH _ hs
  intro w hw
  have hn : w≠1 := by intro h; simp [h] at hw
  have hn' : w+1≠0 := by
    intro h
    have hh := congrArg Complex.re h
    simp [Complex.add_re] at hh
    linarith
  dsimp [H]
  rw [hEq w hw]
  dsimp [G]
  rw [regularizedLogDerivative_eq hn (riemannZeta_ne_zero_of_one_le_re hw.le)]
  rw [mul_div_cancel₀ _ hn',sub_add_cancel]

theorem RH_of_one_sided_riesz_bounds {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    (h : ∀ ε : ℝ, 0<ε → ∃ C : ℝ, ∀ x>1, 0≤σ*rieszError x*x^(-(1/2+ε))+C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_right_zero_free
  intro s hs
  let ε := min ((s.re-1/2)/2) (1/4)
  have hε : 0<ε := lt_min (by linarith) (by norm_num)
  have hb1 : (1/2:ℝ)+ε<1 := by linarith [min_le_right ((s.re-1/2)/2) (1/4:ℝ)]
  have hbs : (1/2:ℝ)+ε<s.re := by linarith [min_le_left ((s.re-1/2)/2) (1/4:ℝ)]
  obtain ⟨C,hC⟩ := h ε hε
  exact zero_free_of_one_sided_riesz_power (by linarith) hb1 hσ hC s hbs

private theorem norm_psi_error_eq (x : ℝ) : ‖psiError x‖=|realPrimeError x| := by
  have he : psi x=(Chebyshev.psi x:ℂ) := by
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
  rw [psiError,he,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,realPrimeError]

theorem riesz_power_bound_of_strip {a ε : ℝ}
    (hStrip : ∀ s : ℂ, a<s.re → riemannZeta s≠0)
    (ha : 1/2≤a) (ha1 : a<1) (hε : 0<ε) :
    ∃ D : ℝ, 0≤D ∧ ∀ x≥1, |rieszError x|≤D*x^(a+ε) := by
  obtain ⟨C,hC,h⟩ := (chebyshev_power_bound_of_strip hStrip ha ha1 hε).exists_nonneg
  obtain ⟨Y,hY⟩ := eventually_atTop.mp h.bound
  let D := C+(Real.log 4+5)*(max Y 1)
  have hL : 0≤Real.log 4+5 := by linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
  have hsmall : 0≤(Real.log 4+5)*(max Y 1) := by positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have hB (t : ℝ) (ht : 1≤t) : |realPrimeError t|≤D*t^(a+ε) := by
    have ht0 := zero_le_one.trans ht
    by_cases htY : Y≤t
    · have hh := hY t htY
      rw [norm_psi_error_eq,Real.norm_of_nonneg (Real.rpow_nonneg ht0 _)] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hsmall) (by positivity))
    · have htM : t≤max Y 1 := (le_of_not_ge htY).trans (le_max_left _ _)
      have hop : 1≤t^(a+ε) := Real.one_le_rpow ht (by linarith)
      exact (real_prime_error_linear ht0).trans ((mul_le_mul_of_nonneg_left htM hL).trans
        ((le_add_of_nonneg_left hC).trans (le_mul_of_one_le_right hD hop)))
  refine ⟨D,hD,?_⟩
  intro x hx
  have hxP := zero_lt_one.trans_le hx
  let A := D*x^(a+ε)
  have hA : 0≤A := by dsimp [A]; positivity
  have hQ (t : ℝ) (ht : t∈Set.Ioc (1:ℝ) x) : ‖realPrimeError t‖≤A := by
    rw [Real.norm_eq_abs]
    exact (hB t ht.1.le).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans ht.1.le) ht.2 (by linarith)) hD)
  have hI : IntegrableOn (fun _ : ℝ => A) (Set.Ioc (1:ℝ) x) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hE : IntegrableOn realPrimeError (Set.Ioc (1:ℝ) x) := by
    refine hI.mono' real_prime_error_measurable.aestronglyMeasurable ?_
    exact (ae_restrict_mem measurableSet_Ioc).mono hQ
  have hInt : ‖∫ t in Set.Ioc (1:ℝ) x, realPrimeError t‖≤A*(x-1) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hh := integral_mono_ae hE.norm hI
      ((ae_restrict_mem measurableSet_Ioc).mono hQ)
    simpa [integral_const,max_eq_left (sub_nonneg.mpr hx),mul_comm] using hh
  rw [rieszError,abs_mul,abs_of_nonneg (inv_nonneg.mpr hxP.le),←Real.norm_eq_abs]
  refine (mul_le_mul_of_nonneg_left hInt (inv_nonneg.mpr hxP.le)).trans ?_
  have hfrac : (x-1)/x≤1 := (div_le_one hxP).mpr (by linarith)
  calc
    _ = A*((x-1)/x) := by ring
    _ ≤ A*1 := mul_le_mul_of_nonneg_left hfrac hA
    _ = _ := by simp [A]

theorem rh_iff_one_sided_riesz_bounds {σ : ℝ} (hσ : σ=1 ∨ σ= -1) :
    RiemannHypothesis ↔
      (∀ ε : ℝ, 0<ε → ∃ C : ℝ, ∀ x>1, 0≤σ*rieszError x*x^(-(1/2+ε))+C) := by
  constructor
  · intro h ε hε
    obtain ⟨D,hD,hB⟩ := riesz_power_bound_of_strip (ZetaDiskLog.right_zero_free_of_RH h)
      le_rfl (by norm_num) hε
    refine ⟨D,?_⟩
    intro x hx
    have hx0 : 0<x := by linarith
    have hσ' : |σ|=1 := by rcases hσ with rfl|rfl <;> norm_num
    have hl := neg_abs_le (σ*rieszError x)
    rw [abs_mul,hσ',one_mul] at hl
    have hb := hB x hx.le
    have hp := Real.rpow_pos_of_pos hx0 (1/2+ε)
    have he : -D*x^(1/2+ε)≤σ*rieszError x := by linarith
    have hh := (le_div_iff₀ hp).mpr he
    rw [Real.rpow_neg hx0.le,←div_eq_mul_inv]
    linarith
  · exact RH_of_one_sided_riesz_bounds hσ

end RHConnections.RieszPrimeMellin
