import Verified
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.MellinTransform

noncomputable section
namespace RHConnections.ChebyshevCriterion
open MeasureTheory Filter Asymptotics PoleCompensation
open scoped Topology

private def powerCutChebyshev : ℝ → ℂ := (Set.Ioi (1:ℝ)).indicator psiError

def chebyshevPowerContinuation (s : ℂ) : ℂ := 1 + s * mellin powerCutChebyshev (-s)

private theorem power_cut_chebyshev_local : LocallyIntegrableOn powerCutChebyshev (Set.Ioi 0) := by
  have hp : LocallyIntegrableOn psi (Set.Ici 0) := by
    unfold psi
    simpa only [one_mul] using (locallyIntegrableOn_mul_sum_Icc (m := 1) mangoldtCoeff
      (a := (0:ℝ)) le_rfl (locallyIntegrableOn_const (1:ℂ)))
  have hid : LocallyIntegrableOn (fun x : ℝ => (x:ℂ)) (Set.Ici (0:ℝ)) :=
    Complex.continuous_ofReal.continuousOn.locallyIntegrableOn measurableSet_Ici
  have h : LocallyIntegrableOn psiError (Set.Ici 0) := hp.sub hid
  intro x hx
  obtain ⟨U,hU,hI⟩ := h.mono_set Set.Ioi_subset_Ici_self x hx
  exact ⟨U,hU,hI.indicator measurableSet_Ioi⟩

private theorem power_cut_growth {a : ℝ} (hM : psiError =O[atTop] (fun x : ℝ => x^a)) :
    powerCutChebyshev =O[atTop] (fun x : ℝ => x^a) := by
  obtain ⟨C,hC⟩ := isBigO_iff.mp hM
  refine isBigO_iff.mpr ⟨C,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),hC] with x hx hc
  simpa only [powerCutChebyshev, Set.indicator_of_mem (Set.mem_Ioi.mpr hx)] using hc

theorem chebyshevPowerContinuation_analytic {a : ℝ}
    (hm : psiError =O[atTop] (fun x : ℝ => x^a)) :
    AnalyticOnNhd ℂ chebyshevPowerContinuation {s : ℂ | a<s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  change a<s.re at hs
  let b := -s.re-1
  have htop : powerCutChebyshev =O[atTop] (fun x : ℝ => x^(-(-a))) := by
    simpa only [neg_neg] using power_cut_growth hm
  have hbot : powerCutChebyshev =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-b)) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    have hh : ∀ᶠ x in 𝓝[>] (0:ℝ), x < 1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hh] with x hx
    simp [powerCutChebyshev, not_lt.mpr hx.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow (s := -s) power_cut_chebyshev_local htop
    (by change -s.re < -a; linarith) hbot
    (by change -s.re-1 < -s.re; linarith)
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) s := by fun_prop
  have hM := hd.comp s hneg
  have hc : DifferentiableAt ℂ (fun _ : ℂ => (1:ℂ)) s := by fun_prop
  exact (hc.add (differentiableAt_id.mul hM)).differentiableWithinAt

private theorem mellin_power_cut_eq (s : ℂ) : mellin powerCutChebyshev (-s) =
    ∫ x in Set.Ioi (1:ℝ), psiError x * (x:ℂ)^(-(s+1)) := by
  unfold mellin
  have he (x : ℝ) : (x:ℂ)^(-s-1) • powerCutChebyshev x =
      (Set.Ioi (1:ℝ)).indicator (fun x : ℝ => psiError x * (x:ℂ)^(-(s+1))) x := by
    by_cases hx : x ∈ Set.Ioi (1:ℝ)
    · simp only [powerCutChebyshev, Set.indicator_of_mem hx, smul_eq_mul, show -s-1= -(s+1) by ring, mul_comm]
    · simp [powerCutChebyshev,Set.indicator_of_notMem hx]
  simp_rw [he]
  rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num))]

private theorem power_error_integrable
    (hm : psiError =O[atTop] (fun x : ℝ => x^(1:ℝ))) {s : ℂ} (hs : 1<s.re) :
    IntegrableOn (fun x : ℝ => psiError x * (x:ℂ)^(-(s+1))) (Set.Ioi 1) := by
  have ht : powerCutChebyshev =O[atTop] (fun x : ℝ => x^(-(-1:ℝ))) := by
    simpa only [neg_neg] using power_cut_growth hm
  have hb : powerCutChebyshev =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-(-s.re-1))) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with x hx
    simp [powerCutChebyshev,not_lt.mpr hx.le]
  have h := mellinConvergent_of_isBigO_rpow (s := -s) power_cut_chebyshev_local ht
    (by change -s.re < -1; linarith) hb (by change -s.re-1 < -s.re; linarith)
  unfold MellinConvergent at h
  apply (h.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))).congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [powerCutChebyshev,Set.indicator_of_mem hx,smul_eq_mul,show -s-1= -(s+1) by ring,mul_comm]

theorem chebyshevPowerContinuation_euler
    (hm : psiError =O[atTop] (fun x : ℝ => x^(1:ℝ))) {s : ℂ} (hs : 1<s.re) :
    chebyshevPowerContinuation s = compensatedLogDerivative s := by
  have ho := hm.comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  change (fun n : ℕ => psiError (n:ℝ)) =O[atTop] (fun n : ℕ => (n:ℝ)^(1:ℝ)) at ho
  have hi : (fun n : ℕ => (n:ℂ)) =O[atTop] (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1,Eventually.of_forall fun n => ?_⟩
    simp
  have hn : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, mangoldtCoeff k) =O[atTop]
      (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
    have he : (fun n : ℕ => psiError (n:ℝ)) + (fun n : ℕ => (n:ℂ)) =
        (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, mangoldtCoeff k) := by
      funext n
      simp only [Pi.add_apply, psiError, psi, Nat.floor_natCast, Complex.ofReal_natCast, sub_add_cancel]
    exact he ▸ ho.add hi
  have hL : LSeries mangoldtCoeff s = -deriv riemannZeta s / riemannZeta s :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have h := LSeries_eq_mul_integral mangoldtCoeff (by norm_num : (0:ℝ)≤1) hs
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs) hn
  have he (x : ℝ) (hx : x ∈ Set.Ioi (1:ℝ)) :
      psi x * (x:ℂ)^(-(s+1)) = psiError x * (x:ℂ)^(-(s+1)) + (x:ℂ)^(-s) := by
    have hpos : 0<x := by change 1<x at hx; linarith
    have hp : (x:ℂ)^(-(s+1))*(x:ℂ) = (x:ℂ)^(-s) := by
      calc
        _ = (x:ℂ)^(-(s+1))*(x:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
        _ = (x:ℂ)^((-(s+1))+1) := (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hpos.ne')).symm
        _ = _ := by rw [show -(s+1)+1 = -s by ring]
    rw [← hp, psiError]
    ring
  change LSeries mangoldtCoeff s = s * ∫ x in Set.Ioi (1:ℝ), psi x*(x:ℂ)^(-(s+1)) at h
  have hneg : (-s).re < -1 := by simp; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_add (power_error_integrable hm hs)
    (integrableOn_Ioi_cpow_of_lt hneg (by norm_num)),integral_Ioi_cpow_of_lt hneg (by norm_num),
    Complex.ofReal_one,Complex.one_cpow,← mellin_power_cut_eq] at h
  rw [chebyshevPowerContinuation,compensatedLogDerivative,← hL,h]
  have h1 : s ≠ 1 := fun he => by simpa [he] using hs
  field_simp [sub_ne_zero.mpr h1,show -s+1 ≠ 0 by intro he; apply h1; linear_combination -he] <;> ring

theorem zero_free_of_chebyshev_fixed_power {a : ℝ} (ha : a<1)
    (h : psiError =O[atTop] (fun x : ℝ => x^a)) :
    ∀ s : ℂ, a<s.re → riemannZeta s≠0 := by
  have hl : psiError =O[atTop] (fun x : ℝ => x^(1:ℝ)) := by
    obtain ⟨C,hC,hB⟩ := h.exists_nonneg
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1:ℝ),hB.bound] with x hx hBx
    refine hBx.trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _),
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)]
    exact Real.rpow_le_rpow_of_exponent_le hx ha.le
  intro s hs
  exact zeta_zero_free_above_compensated_extension ha (chebyshevPowerContinuation_analytic h)
    (fun _ ht => chebyshevPowerContinuation_euler hl ht) hs

end RHConnections.ChebyshevCriterion
