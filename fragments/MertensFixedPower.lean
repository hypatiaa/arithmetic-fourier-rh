import Verified
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.MellinTransform

noncomputable section
open MeasureTheory Filter Asymptotics
open scoped Topology

namespace RHConnections.MertensCriterion
open PoleCompensation ArithmeticFourierInversion

private def powerCutMertens : ℝ → ℂ := (Set.Ioi (1:ℝ)).indicator mertens

private theorem power_cut_mertens_local : LocallyIntegrableOn powerCutMertens (Set.Ioi 0) := by
  have h : LocallyIntegrableOn mertens (Set.Ici 0) := by
    unfold mertens
    simpa only [one_mul] using (locallyIntegrableOn_mul_sum_Icc (m := 1) moebiusCoeff
      (a := (0:ℝ)) le_rfl (locallyIntegrableOn_const (1:ℂ)))
  intro x hx
  obtain ⟨U,hU,hI⟩ := h.mono_set Set.Ioi_subset_Ici_self x hx
  exact ⟨U,hU,hI.indicator measurableSet_Ioi⟩

theorem zero_free_of_mertens_fixed_power {b : ℝ} (hb : b<1)
    (hM : mertens =O[atTop] (fun x : ℝ => x^b)) :
    ∀ s : ℂ, b<s.re → riemannZeta s≠0 := by
  let H : Set ℂ := {s | b<s.re}
  let F (s : ℂ) := s*mellin powerCutMertens (-s)
  have hF : AnalyticOnNhd ℂ F H := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
    intro s hs
    have htop : powerCutMertens =O[atTop] (fun x : ℝ => x^(-(-b))) := by
      obtain ⟨C,hC⟩ := isBigO_iff.mp hM
      refine isBigO_iff.mpr ⟨C,?_⟩
      filter_upwards [eventually_gt_atTop (1:ℝ),hC] with x hx hc
      simpa only [powerCutMertens,Set.indicator_of_mem (Set.mem_Ioi.mpr hx),neg_neg] using hc
    have hbot : powerCutMertens =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-(-s.re-1))) := by
      refine isBigO_iff.mpr ⟨0,?_⟩
      have hh : ∀ᶠ x in 𝓝[>] (0:ℝ), x<1 :=
        (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
      filter_upwards [hh] with x hx
      simp [powerCutMertens,not_lt.mpr hx.le]
    have hd := mellin_differentiableAt_of_isBigO_rpow (s := -s)
      power_cut_mertens_local htop (by change -s.re < -b; exact neg_lt_neg hs) hbot
      (by change -s.re-1 < -s.re; linarith)
    exact (differentiableAt_id.mul (hd.comp s differentiableAt_id.neg)).differentiableWithinAt
  have hEuler (s : ℂ) (hs : 1<s.re) : riemannZeta s * F s = 1 := by
    have hm1 : mertens =O[atTop] (fun x : ℝ => x^(1:ℝ)) := by
      obtain ⟨C,hC0,hC⟩ := hM.exists_nonneg
      apply IsBigO.of_bound C
      filter_upwards [eventually_ge_atTop (1:ℝ),hC.bound] with x hx hCx
      refine hCx.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
        abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      exact Real.rpow_le_rpow_of_exponent_le hx hb.le
    have ho := hm1.comp_tendsto (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
    have hn : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, moebiusCoeff k) =O[atTop]
        (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
      simpa only [mertens,Nat.floor_natCast,Function.comp_def] using ho
    have hconv : LSeriesSummable moebiusCoeff s := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
    have hi := LSeries_eq_mul_integral moebiusCoeff (by norm_num : (0:ℝ)≤1) hs hconv hn
    have hMellin : mellin powerCutMertens (-s) =
        ∫ x in Set.Ioi (1:ℝ), mertens x*(x:ℂ)^(-(s+1)) := by
      unfold mellin
      have he (x : ℝ) : (x:ℂ)^(-s-1) • powerCutMertens x =
          (Set.Ioi (1:ℝ)).indicator (fun x : ℝ => mertens x*(x:ℂ)^(-(s+1))) x := by
        by_cases hx : x ∈ Set.Ioi (1:ℝ)
        · simp only [powerCutMertens,Set.indicator_of_mem hx,smul_eq_mul,
            show -s-1=-(s+1) by ring,mul_comm]
        · simp [powerCutMertens,Set.indicator_of_notMem hx]
      simp_rw [he]
      rw [setIntegral_indicator measurableSet_Ioi,Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num))]
    change riemannZeta s*(s*mellin powerCutMertens (-s))=1
    rw [hMellin]
    unfold mertens
    rw [←hi,←LSeries_one_eq_riemannZeta hs]
    exact LSeries_one_mul_Lseries_moebius hs
  have hA : AnalyticOnNhd ℂ (regularizedZeta*F) H :=
    fun s hs => (regularizedZeta_analytic s).mul (hF s hs)
  have hB : AnalyticOnNhd ℂ (fun s : ℂ => s-1) H := fun _ _ => analyticAt_id.sub analyticAt_const
  have h2 : (2:ℂ)∈H := by change b<(2:ℂ).re; norm_num; linarith
  have hn : {s : ℂ | 1<s.re}∈𝓝 (2:ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have he : regularizedZeta*F =ᶠ[𝓝 (2:ℂ)] (fun s : ℂ => s-1) := by
    filter_upwards [hn] with s hs
    have hs1 : s≠1 := by intro he; change 1<s.re at hs; simpa [he] using hs
    change regularizedZeta s*F s=s-1
    rw [(regularizedZeta_germ hs1).eq_of_nhds,mul_assoc,hEuler s hs,mul_one]
  have hall := hA.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_halfSpace_re_gt b).isPreconnected h2 he
  intro s hs hz
  have hs1 : s≠1 := by
    intro he
    subst s
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hz
  have hr := hall (show s∈H from hs)
  change regularizedZeta s*F s=s-1 at hr
  rw [(regularizedZeta_germ hs1).eq_of_nhds,hz,mul_zero,zero_mul] at hr
  exact (sub_ne_zero.mpr hs1) hr.symm

theorem natural_mertens_excursions_of_zero {s : ℂ} (hz : riemannZeta s=0)
    {b : ℝ} (hb0 : 0≤b) (hb : b<s.re) (hb1 : b<1) :
    ∀ N : ℕ, ∃ t : ℕ, N≤t ∧ (t:ℝ)^b≤|M t| := by
  intro N
  by_contra! h
  have hM : mertens =O[atTop] (fun x : ℝ => x^b) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop ((N:ℝ)+1)] with x hx
    have hx0 : 0≤x := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hN : N≤⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by linarith)
    rw [mertens_eq_natural_M,Complex.norm_real,Real.norm_eq_abs,one_mul,
      Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx0 _)]
    exact (h ⌊x⌋₊ hN).le.trans
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0) hb0)
  exact zero_free_of_mertens_fixed_power hb1 hM s hb hz

end RHConnections.MertensCriterion
