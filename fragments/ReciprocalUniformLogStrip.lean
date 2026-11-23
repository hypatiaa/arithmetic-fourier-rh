import ReciprocalHighLogStrip
open Set Metric
noncomputable section
namespace RHConnections.ReciprocalLocalComparison
open ZetaZeroFreeRegion ZetaDiskLog PoleCompensation

theorem reciprocal_analytic_of_nonzero {s : ℂ} (hz : riemannZeta s ≠ 0) :
    AnalyticAt ℂ zetaReciprocal s := by
  have hn : regularizedZeta s ≠ 0 := by
    by_cases he : s=1
    · rw [he,regularizedZeta_one]; exact one_ne_zero
    · rw [(regularizedZeta_germ he).eq_of_nhds]
      exact mul_ne_zero (sub_ne_zero.mpr he) hz
  exact (analyticAt_id.sub analyticAt_const).div (regularizedZeta_analytic s) hn

theorem reciprocal_log_region_subpower {ε : ℝ} (hε : 0<ε) :
    ∃ c D : ℝ, 0<c ∧ 0≤D ∧
      AnalyticOnNhd ℂ zetaReciprocal {s : ℂ | 1-c/heightFactor s.im ≤ s.re} ∧
      ∀ s : ℂ, 1-c/heightFactor s.im ≤ s.re → s.re ≤ 2 →
        ‖zetaReciprocal s‖ ≤ D*(1+|s.im|)^ε := by
  obtain ⟨C,hC,hCa,hn⟩ := exists_nonzero_log_region
  let q := min 1 (ε/4)
  let a := C*q/64
  let K := 2+1/(a*q)
  have hq : 0<q := lt_min (by norm_num) (by linarith)
  have hq1 : q≤1 := min_le_left _ _
  have hqε : 4*q≤ε := by linarith [min_le_right (1:ℝ) (ε/4)]
  have ha : 0<a := by positivity
  have haC : a<C := by dsimp [a]; nlinarith [mul_le_mul_of_nonneg_left hq1 hC.le]
  have ha' : a≤1/2 := haC.le.trans hCa
  let S := {s : ℂ | 1-a/heightFactor s.im ≤ s.re}
  have hAnal : AnalyticOnNhd ℂ zetaReciprocal S := by
    intro s hs
    apply reciprocal_analytic_of_nonzero (hn s ?_)
    change 1-a/heightFactor s.im ≤ s.re at hs
    linarith [div_lt_div_of_pos_right haC (zero_lt_one.trans_le (heightFactor_one_le s.im))]
  have hf : Continuous (fun s : ℂ => heightFactor s.im) := by
    unfold heightFactor
    apply continuous_const.add
    apply Continuous.log (by fun_prop)
    intro x
    positivity
  have hclosed : IsClosed S := isClosed_le (continuous_const.sub
    (continuous_const.div hf (fun s => (zero_lt_one.trans_le (heightFactor_one_le s.im)).ne'))) Complex.continuous_re
  let L := closedBall (0:ℂ) 8 ∩ S
  have hL : IsCompact L := (isCompact_closedBall 0 _).inter_right hclosed
  have hcont : ContinuousOn (fun s => ‖zetaReciprocal s‖) L :=
    fun s hs => (hAnal s hs.2).continuousAt.norm.continuousWithinAt
  obtain ⟨B,hB⟩ := hL.bddAbove_image hcont
  let A := Real.exp (2*K+4*q*(1+Real.log 3))
  let D := max A B
  have hA : 0<A := Real.exp_pos _
  have hD : 0≤D := hA.le.trans (le_max_left _ _)
  refine ⟨a,D,ha,hD,hAnal,?_⟩
  intro s hs hs2
  have hb : 1 ≤ 1+|s.im| := by linarith [abs_nonneg s.im]
  have hpow : 1≤(1+|s.im|)^ε := Real.one_le_rpow hb hε.le
  by_cases ht : 5≤|s.im|
  · have hh := narrow_high hC hCa hq hq1 (show a=C*q/64 from rfl) hn ht hs
    have hb' : 0<1+|s.im| := by positivity
    have hH : heightFactor s.im ≤ 1+Real.log 3+Real.log (1+|s.im|) := by
      unfold heightFactor
      have hh := Real.log_le_log (show 0<3+2*|s.im| by positivity)
        (show 3+2*|s.im| ≤ 3*(1+|s.im|) by linarith [abs_nonneg s.im])
      rw [Real.log_mul (by norm_num) hb'.ne'] at hh
      linarith
    have hx : 2*K+4*q*heightFactor s.im ≤ (2*K+4*q*(1+Real.log 3))+
        Real.log (1+|s.im|)*ε := by
      nlinarith [mul_le_mul_of_nonneg_left hH (show 0≤4*q by positivity),
        mul_le_mul_of_nonneg_right hqε (Real.log_nonneg hb)]
    refine hh.trans ((Real.exp_le_exp.mpr hx).trans ?_)
    rw [Real.exp_add,← Real.rpow_def_of_pos hb']
    exact mul_le_mul_of_nonneg_right (le_max_left A B) (by positivity)
  · have hsL : s ∈ L := by
      refine ⟨?_,hs⟩
      rw [mem_closedBall,dist_zero_right]
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      have hu := (div_le_self ha.le (heightFactor_one_le s.im)).trans ha'
      rw [abs_of_nonneg (by linarith : 0 ≤ s.re)]
      linarith [lt_of_not_ge ht]
    exact (hB (Set.mem_image_of_mem _ hsL)).trans ((le_max_right A B).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hD))
end RHConnections.ReciprocalLocalComparison
