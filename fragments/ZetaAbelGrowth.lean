import Verified
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
namespace RHConnections.ZetaAbelGrowth
open Filter Asymptotics MeasureTheory PoleCompensation
open scoped Topology

def frac (x : ℝ) : ℂ := ((x-(⌊x⌋₊:ℝ)):ℝ)
private def cut := (Set.Ioi (1:ℝ)).indicator frac
def remainder (s : ℂ) := mellin cut (-s)

private lemma frac_le {x : ℝ} (hx : 0 ≤ x) : ‖frac x‖ ≤ 1 := by
  rw [frac, Complex.norm_of_nonneg (sub_nonneg.mpr (Nat.floor_le hx))]
  linarith [Nat.lt_floor_add_one x]

private lemma frac_meas : Measurable frac := by unfold frac; fun_prop

private theorem cut_local : LocallyIntegrableOn cut (Set.Ioi 0) := by
  have hfloor : LocallyIntegrableOn (fun x : ℝ => (⌊x⌋₊:ℂ)) (Set.Ici 0) := by
    have hc (n : ℕ) : (∑ k ∈ Finset.Icc 1 n, (1:ℂ)) = n := by simp [Nat.card_Icc]
    simpa only [one_mul, hc] using
      (locallyIntegrableOn_mul_sum_Icc (m := 1) (fun _ : ℕ => (1:ℂ)) (a := (0:ℝ))
        le_rfl (locallyIntegrableOn_const (1:ℂ)))
  have hid : LocallyIntegrableOn (fun x : ℝ => (x:ℂ)) (Set.Ici (0:ℝ)) :=
    Complex.continuous_ofReal.continuousOn.locallyIntegrableOn measurableSet_Ici
  have hf : LocallyIntegrableOn frac (Set.Ici 0) := by
    have he : frac = (fun x : ℝ => (x:ℂ)) - (fun x : ℝ => (⌊x⌋₊:ℂ)) := by
      funext x
      simp only [frac, Pi.sub_apply, Complex.ofReal_sub, Complex.ofReal_natCast]
    rw [he]
    exact hid.sub hfloor
  intro x hx
  obtain ⟨U,hU,hI⟩ := hf.mono_set Set.Ioi_subset_Ici_self x hx
  exact ⟨U,hU,hI.indicator measurableSet_Ioi⟩

theorem remainder_analytic : AnalyticOnNhd ℂ remainder {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  have htop : cut =O[atTop] (fun x : ℝ => x^(-(0:ℝ))) := by
    refine isBigO_iff.mpr ⟨1,?_⟩
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    simpa [cut, hx] using frac_le (by linarith : 0≤x)
  have hbot : cut =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-(-s.re-1))) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with x hx
    simp [cut, not_lt.mpr hx.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow (s := -s) cut_local htop
    (by change -s.re < 0; change 0 < s.re at hs; linarith) hbot
    (by change -s.re-1 < -s.re; linarith)
  exact (hd.comp s differentiableAt_id.neg).differentiableWithinAt

theorem remainder_integral (s : ℂ) : remainder s =
    ∫ x in Set.Ioi (1:ℝ), frac x * (x:ℂ)^(-s-1) := by
  unfold remainder mellin
  have he (x : ℝ) : (x:ℂ)^(-s-1) • cut x =
      (Set.Ioi (1:ℝ)).indicator (fun t : ℝ => frac t * (t:ℂ)^(-s-1)) x := by
    by_cases hx : x ∈ Set.Ioi (1:ℝ)
    · simp only [cut,Set.indicator_of_mem hx,smul_eq_mul,mul_comm]
    · simp [cut,Set.indicator_of_notMem hx]
  simp_rw [he]
  rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num))]

private theorem remainder_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => frac x*(x:ℂ)^(-s-1)) (Set.Ioi 1) := by
  apply (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) (by norm_num : (0:ℝ)<1)).mono'
  · exact frac_meas.aestronglyMeasurable.mul (integrableOn_Ioi_cpow_of_lt
      (show (-s-1).re < -1 by simp [Complex.sub_re]; linarith) (by norm_num : (0:ℝ)<1)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (1:ℝ)))] with x hx
    have hpos : 0<x := by change 1<x at hx; linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re, Complex.neg_re, Complex.one_re]
    simpa using mul_le_mul_of_nonneg_right (frac_le hpos.le) (Real.rpow_nonneg hpos.le (-s.re-1))

theorem remainder_norm_le {s : ℂ} (hs : 0 < s.re) : ‖remainder s‖ ≤ 1/s.re := by
  rw [remainder_integral]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ x in Set.Ioi (1:ℝ), x^(-s.re-1) := by
      apply integral_mono_ae (remainder_integrable hs).norm
        (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) (by norm_num))
      filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (1:ℝ)))] with x hx
      have hpos : 0<x := by change 1<x at hx; linarith
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re, Complex.neg_re, Complex.one_re]
      simpa using mul_le_mul_of_nonneg_right (frac_le hpos.le) (Real.rpow_nonneg hpos.le (-s.re-1))
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) (by norm_num)]
      simp [show -s.re-1+1 = -s.re by ring]

private theorem zeta_abel_euler {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s/(s-1) - s*remainder s := by
  have hsum (n : ℕ) : (∑ k ∈ Finset.Icc 1 n, (1:ℂ)) = n := by simp [Nat.card_Icc]
  have ho : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1:ℂ)) =O[atTop] (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1,Filter.Eventually.of_forall fun n => ?_⟩
    simp [hsum]
  have hi := LSeries_eq_mul_integral (1 : ℕ → ℂ) (by norm_num : (0:ℝ)≤1) hs
    (LSeriesSummable_one_iff.mpr hs) ho
  rw [LSeries_one_eq_riemannZeta hs] at hi
  have hh (x : ℝ) (hx : 1<x) : (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1:ℂ))*(x:ℂ)^(-(s+1)) =
      (x:ℂ)^(-s) - frac x*(x:ℂ)^(-s-1) := by
    have hn : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hpow : (x:ℂ)^(-s-1)*(x:ℂ) = (x:ℂ)^(-s) := by
      calc
        _ = (x:ℂ)^(-s-1)*(x:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
        _ = (x:ℂ)^((-s-1)+1) := (Complex.cpow_add _ _ hn).symm
        _ = _ := by rw [show -s-1+1 = -s by ring]
    rw [hsum, show -(s+1) = -s-1 by ring, ← hpow]
    simp only [frac,Complex.ofReal_sub,Complex.ofReal_natCast]
    ring
  have hi' : riemannZeta s = s*∫ x in Set.Ioi (1:ℝ),
      ((x:ℂ)^(-s) - frac x*(x:ℂ)^(-s-1)) := by
    rw [hi]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi hh
  have hneg : (-s).re < -1 := by simp; linarith
  rw [hi', integral_sub (integrableOn_Ioi_cpow_of_lt hneg (by norm_num)) (remainder_integrable (by linarith)),
    integral_Ioi_cpow_of_lt hneg (by norm_num), Complex.ofReal_one, Complex.one_cpow, ← remainder_integral]
  have h1 : s ≠ 1 := fun h => by simpa [h] using hs
  field_simp [sub_ne_zero.mpr h1, show -s+1 ≠ 0 by intro h; apply h1; linear_combination -h] <;> ring

theorem zeta_abel_formula {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s/(s-1) - s * ∫ x in Set.Ioi (1:ℝ), frac x*(x:ℂ)^(-s-1) := by
  let H : Set ℂ := {z | 0 < z.re}
  have hA : AnalyticOnNhd ℂ regularizedZeta H := fun z _ => regularizedZeta_analytic z
  have hB : AnalyticOnNhd ℂ (fun z : ℂ => z - (z-1)*z*remainder z) H :=
    fun z hz => analyticAt_id.sub (((analyticAt_id.sub analyticAt_const).mul analyticAt_id).mul
      (remainder_analytic z hz))
  have hb : {z : ℂ | 1 < z.re} ∈ 𝓝 (2:ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have he : regularizedZeta =ᶠ[𝓝 (2:ℂ)] (fun z : ℂ => z-(z-1)*z*remainder z) := by
    filter_upwards [hb] with z hz
    have hn : z ≠ 1 := fun h => by change 1 < z.re at hz; simpa [h] using hz
    rw [(regularizedZeta_germ hn).eq_of_nhds,zeta_abel_euler hz]
    field_simp [sub_ne_zero.mpr hn] <;> ring
  have hall := hA.eqOn_of_preconnected_of_eventuallyEq hB (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ H by norm_num [H]) he
  have h := hall (show s ∈ H from hs)
  change regularizedZeta s = s-(s-1)*s*remainder s at h
  rw [(regularizedZeta_germ hs1).eq_of_nhds] at h
  rw [← remainder_integral]
  field_simp [sub_ne_zero.mpr hs1] <;> linear_combination h

theorem zeta_vertical_bound {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s/(s-1)‖ + ‖s‖/s.re := by
  rw [zeta_abel_formula hs hs1, ← remainder_integral]
  apply (norm_sub_le _ _).trans
  rw [norm_mul, div_eq_mul_inv ‖s‖]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (by simpa using remainder_norm_le hs) (norm_nonneg s))

end RHConnections.ZetaAbelGrowth
