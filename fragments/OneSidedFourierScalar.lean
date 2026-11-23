import Verified
import PositiveSummatoryPower
import FourierEulerFactor

noncomputable section
open MeasureTheory Filter Asymptotics
open scoped Topology
namespace RHConnections.ArithmeticFourierInversion
open RHConnections.PoleCompensation RHConnections.ZetaDiskLog
open RHConnections.PrimeErrorLaplace RHConnections.PositiveSummatory

def realFourierScalar (B : ℕ) (x : ℝ) : ℝ := S B ⌊x⌋₊

theorem real_fourier_scalar_measurable (B : ℕ) : Measurable (realFourierScalar B) := by
  have hfloor : Monotone (fun x : ℝ => ⌊x⌋₊) := fun _ _ h => Nat.floor_mono h
  exact (measurable_of_countable (S B)).comp hfloor.measurable

theorem real_fourier_scalar_linear (B : ℕ) :
    ∃ D : ℝ, 0≤D ∧ ∀ x≥1, |realFourierScalar B x|≤D*x := by
  have hM : NaturalPowerBound M 1 := by
    refine ⟨1,by norm_num,?_⟩
    intro n hn
    unfold M
    rw [Real.rpow_one,one_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _i∈Finset.Ioc 0 n,(1:ℝ) := Finset.sum_le_sum (fun i _ => by
        change |(ArithmeticFunction.moebius i:ℝ)|≤1
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := i)))
      _ = _ := by simp [Nat.card_Ioc]
  obtain ⟨D,hD,hS⟩ := (M_power_bound_iff_S B (by norm_num : (0:ℝ)<1)).mp hM
  refine ⟨D,hD,?_⟩
  intro x hx
  have hx0 := zero_le_one.trans hx
  have hf : 1≤⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  exact (hS _ hf).trans (by rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left (Nat.floor_le hx0) hD)

theorem real_fourier_scalar_weighted_integrable (B : ℕ) {s : ℂ} (hs : 1<s.re) :
    IntegrableOn (fun x => (realFourierScalar B x:ℂ)*(x:ℂ)^(-(s+1))) (Set.Ioi 1) := by
  obtain ⟨D,hD,hS⟩ := real_fourier_scalar_linear B
  refine (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re < -1) (by norm_num : (0:ℝ)<1)).const_mul
    D |>.mono' ?_ ?_
  · exact (Complex.continuous_ofReal.measurable.comp (real_fourier_scalar_measurable B)).aestronglyMeasurable.mul
      (integrableOn_Ioi_cpow_of_lt
        (show (-(s+1)).re < -1 by simp [Complex.add_re]; linarith) (by norm_num : (0:ℝ)<1)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have h1 : 1<x := hx
    have hx0 : 0<x := by linarith
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Complex.neg_re,Complex.add_re,Complex.one_re]
    have h := mul_le_mul_of_nonneg_right (hS x h1.le) (Real.rpow_nonneg hx0.le (-(s.re+1)))
    have he : x*x^(-(s.re+1)) = x^(-s.re) := by
      calc
        _ = x^(1:ℝ)*x^(-(s.re+1)) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hx0]; congr 1; ring
    rwa [mul_assoc,he] at h

theorem real_fourier_scalar_euler_integral (B : ℕ) {s : ℂ} (hs : 1<s.re) :
    (∫ x in Set.Ioi (1:ℝ),(realFourierScalar B x:ℂ)*(x:ℂ)^(-(s+1))) =
      (fourierEulerFactor B s*zetaReciprocal s)/s := by
  let f (n : ℕ) : ℂ := ((g B * muR) n:ℝ)
  have hsum (x : ℝ) : (∑ k∈Finset.Icc 1 ⌊x⌋₊,f k)=(realFourierScalar B x:ℂ) := by
    unfold realFourierScalar S
    rw [Complex.ofReal_sum]
    rw [show Finset.Icc 1 ⌊x⌋₊=Finset.Ioc 0 ⌊x⌋₊ from by ext k; simp; omega]
  obtain ⟨D,hD,hS⟩ := real_fourier_scalar_linear B
  have hcount : (fun n : ℕ => ∑ k∈Finset.Icc 1 n,f k) =O[atTop]
      (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
    apply IsBigO.of_bound D
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have h := hsum (n:ℝ)
    rw [Nat.floor_natCast] at h
    rw [h,Complex.norm_real,Real.norm_eq_abs,Real.rpow_one,Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hS n (by exact_mod_cast hn)
  have hE := LSeries_eq_mul_integral f (by norm_num : (0:ℝ)≤1) hs
    (scalar_LSeries_summable B hs) hcount
  simp only [hsum] at hE
  rw [scalar_LSeries_eq_factor B hs] at hE
  apply (eq_div_iff (show s≠0 by rintro rfl; norm_num at hs)).mpr
  rw [mul_comm,hE]

theorem global_fourier_signed_majorant (B : ℕ) {a σ C : ℝ}
    (ha : 0≤a) (hσ : |σ|=1) (hC : 0≤C)
    (hS : ∀ᶠ n : ℕ in atTop, -(C*(n:ℝ)^a)≤σ*S B n) :
    ∃ K : ℝ, ∀ x>1, 0≤σ*realFourierScalar B x*x^(-a)+K := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hS
  obtain ⟨D,hD,hL⟩ := real_fourier_scalar_linear B
  let Y := (N:ℝ)+1
  let K := C+D*Y
  have hY : 0≤Y := by dsimp [Y]; positivity
  have hCY : C≤K := le_add_of_nonneg_right (mul_nonneg hD hY)
  refine ⟨K,?_⟩
  intro x hx
  have hx0 : 0<x := by linarith
  have hpow : 1≤x^a := Real.one_le_rpow hx.le ha
  have hp : 0<x^a := Real.rpow_pos_of_pos hx0 _
  have h : -K*x^a≤σ*realFourierScalar B x := by
    by_cases hlarge : Y≤x
    · have hN' : N≤⌊x⌋₊ := (Nat.le_floor_iff hx0.le).mpr (by dsimp [Y] at hlarge; linarith)
      have hcap := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0.le) ha
      have hmul := mul_le_mul hCY (show ((⌊x⌋₊:ℕ):ℝ)^a≤x^a from hcap)
        (by positivity) (hC.trans hCY)
      have hn := hN _ hN'
      change -K*x^a ≤ σ*S B ⌊x⌋₊
      linarith only [hmul,hn]
    · have hb := (hL x hx.le).trans (mul_le_mul_of_nonneg_left (le_of_not_ge hlarge) hD)
      have hlow := neg_abs_le (σ*realFourierScalar B x)
      rw [abs_mul,hσ,one_mul] at hlow
      have hsize := le_mul_of_one_le_right (hC.trans hCY) hpow
      dsimp [K] at hsize ⊢
      linarith only [hb,hlow,hsize,hC]
  rw [Real.rpow_neg hx0.le,←div_eq_mul_inv]
  linarith [(le_div_iff₀ hp).mpr h]

theorem zero_free_of_one_sided_fourier_scalar (B : ℕ) {a σ C : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hσ : σ=1 ∨ σ= -1) (hC : 0≤C)
    (hS : ∀ᶠ n : ℕ in atTop, -(C*(n:ℝ)^a)≤σ*S B n) :
    ∀ s : ℂ, a<s.re → riemannZeta s≠0 := by
  have hσ' : |σ|=1 := by rcases hσ with rfl|rfl <;> norm_num
  obtain ⟨K,hK⟩ := global_fourier_signed_majorant B ha hσ' hC hS
  let G := fun s => fourierEulerFactor B s*zetaReciprocal s
  have hG (b : ℝ) (hb : 0<b) : AnalyticAt ℂ G (b:ℂ) := by
    have hh : 0<(b:ℂ).re := by simpa using hb
    exact (fourierEulerFactor_analytic B (b:ℂ) hh).mul
      ((analyticAt_id.sub analyticAt_const).div (regularizedZeta_analytic _)
        (regularized_zeta_ne_zero_positive_real hb))
  obtain ⟨A,hA,hEq⟩ := signed_power_mellin_extension (G := G)
    (real_fourier_scalar_measurable B) hG
    (fun s hs => ⟨real_fourier_scalar_weighted_integrable B hs,real_fourier_scalar_euler_integral B hs⟩)
    ha ha1 hσ hK
  let H : Set ℂ := {s | a<s.re}
  let P := fun s => regularizedZeta s*A s
  let R := fun s => (s-1)*fourierEulerFactor B s
  have hP : AnalyticOnNhd ℂ P H := fun s hs => (regularizedZeta_analytic _).mul (hA s hs)
  have hR : AnalyticOnNhd ℂ R H := fun s hs =>
    (analyticAt_id.sub analyticAt_const).mul (fourierEulerFactor_analytic B s (ha.trans_lt hs))
  have h2 : (2:ℂ)∈H := by change a<(2:ℂ).re; norm_num; linarith
  have hnear : P =ᶠ[𝓝 (2:ℂ)] R := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1<(2:ℂ).re by norm_num)] with s hs
    have hs1 : s≠1 := by intro he; change 1<s.re at hs; simp [he] at hs
    have hReg : regularizedZeta s≠0 := by
      rw [(regularizedZeta_germ hs1).eq_of_nhds]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_le_re hs.le)
    dsimp [P,R]
    rw [hEq s hs]
    dsimp [G,zetaReciprocal]
    field_simp [hReg]
  have hAll := hP.eqOn_of_preconnected_of_eventuallyEq hR
    (convex_halfSpace_re_gt a).isPreconnected h2 hnear
  intro s hs hz
  have hs1 : s≠1 := by
    intro he
    subst s
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hz
  have hh := hAll (show s∈H from hs)
  change regularizedZeta s*A s=(s-1)*fourierEulerFactor B s at hh
  rw [(regularizedZeta_germ hs1).eq_of_nhds,hz,mul_zero,zero_mul] at hh
  exact (mul_ne_zero (sub_ne_zero.mpr hs1) (fourierEulerFactor_ne_zero B (ha.trans_lt hs))) hh.symm

end RHConnections.ArithmeticFourierInversion
