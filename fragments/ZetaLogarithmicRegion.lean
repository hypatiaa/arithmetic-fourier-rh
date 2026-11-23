import Verified

open Set Metric
noncomputable section
namespace RHConnections.ZetaZeroFreeRegion
open SpectralTail PoleCompensation

theorem bounded_height_exclusion (T : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ rho : NontrivialZetaZero, |rho.val.im| ≤ T → rho.val.re ≤ 1-d := by
  let K := closedBall (0:ℂ) (T+1) ∩ entireXi ⁻¹' {0}
  have hXi : Continuous entireXi :=
    continuous_iff_continuousAt.mpr fun s => (entireXi_analytic s).continuousAt
  have hK : IsCompact K := (isCompact_closedBall 0 _).inter_right
    (isClosed_singleton.preimage hXi)
  have hmem (rho : NontrivialZetaZero) (ht : |rho.val.im| ≤ T) : rho.val ∈ K := by
    have hre : 0 < rho.val.re := rho.property.1.1
    have hr1 : rho.val.re < 1 := rho.property.1.2
    refine ⟨?_,(entireXi_eq_zero_iff rho.val).mpr rho.property⟩
    rw [mem_closedBall,dist_zero_right]
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    rw [abs_of_pos hre]
    linarith
  by_cases hne : K.Nonempty
  · obtain ⟨s,hs,hm⟩ := hK.exists_isMaxOn hne Complex.continuous_re.continuousOn
    have hz : entireXi s = 0 := hs.2
    have hr := ((entireXi_eq_zero_iff s).mp hz).1.2
    refine ⟨1-s.re,by linarith,?_⟩
    intro rho ht
    have hb : rho.val.re ≤ s.re := hm (hmem rho ht)
    linarith
  · exact ⟨1,by norm_num,fun rho ht => (hne ⟨rho.val,hmem rho ht⟩).elim⟩

def heightFactor (t : ℝ) : ℝ := 1+Real.log (3+2*|t|)

theorem heightFactor_one_le (t : ℝ) : 1 ≤ heightFactor t := by
  unfold heightFactor
  have h : 0 ≤ Real.log (3+2*|t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  linarith

theorem all_height_logarithmic_exclusion :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/2 ∧ ∀ rho : NontrivialZetaZero,
      c/heightFactor rho.val.im ≤ rho.val.re ∧ rho.val.re ≤ 1-c/heightFactor rho.val.im := by
  obtain ⟨c,hc,hbig⟩ := nontrivial_zero_logarithmic_exclusion
  obtain ⟨d,hd,hsmall⟩ := bounded_height_exclusion 1
  let C : ℝ := min (1/2) (min c d)
  have hC : 0 < C := lt_min (by norm_num) (lt_min hc hd)
  have hCc : C ≤ c := (min_le_right _ _).trans (min_le_left _ _)
  have hCd : C ≤ d := (min_le_right _ _).trans (min_le_right _ _)
  have hr (rho : NontrivialZetaZero) : rho.val.re ≤ 1-C/heightFactor rho.val.im := by
    have hH : 0 < heightFactor rho.val.im := zero_lt_one.trans_le (heightFactor_one_le _)
    by_cases ht : 1 ≤ |rho.val.im|
    · exact (hbig rho ht).trans (sub_le_sub_left (div_le_div_of_nonneg_right hCc hH.le) _)
    · have h := div_le_self hC.le (heightFactor_one_le rho.val.im)
      exact (hsmall rho (lt_of_not_ge ht).le).trans (sub_le_sub_left (h.trans hCd) _)
  refine ⟨C,hC,min_le_left _ _,?_⟩
  intro rho
  let r : NontrivialZetaZero := ⟨1-rho.val,
    (entireXi_eq_zero_iff (1-rho.val)).mp ((entireXi_reflection rho.val).trans
      ((entireXi_eq_zero_iff rho.val).mpr rho.property))⟩
  have hl := hr r
  change (1-rho.val).re ≤ 1-C/heightFactor (1-rho.val).im at hl
  simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,zero_sub,heightFactor,abs_neg] at hl
  exact ⟨by unfold heightFactor; linarith,hr rho⟩

theorem compensated_trace_analytic_on_log_region :
    ∃ c : ℝ, 0 < c ∧
      AnalyticOnNhd ℂ regularizedLogDerivative {s : ℂ | 1-c/heightFactor s.im < s.re} ∧
      ∀ s : ℂ, 1 < s.re → regularizedLogDerivative s = compensatedLogDerivative s := by
  obtain ⟨c,hc,hc1,hBound⟩ := all_height_logarithmic_exclusion
  refine ⟨c,hc,?_,?_⟩
  · intro s hs
    by_cases h1 : s = 1
    · subst s
      exact regularizedLogDerivative_analytic_one
    · apply regularizedLogDerivative_analytic
      rw [(regularizedZeta_germ h1).eq_of_nhds]
      apply mul_ne_zero (sub_ne_zero.mpr h1)
      intro hz
      have hs1 : s.re < 1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hz)
      have hh : c/heightFactor s.im ≤ 1/2 :=
        (div_le_self hc.le (heightFactor_one_le _)).trans hc1
      change 1-c/heightFactor s.im < s.re at hs
      let rho : NontrivialZetaZero := ⟨s,⟨by linarith,hs1⟩,hz⟩
      exact (not_le_of_gt hs) (hBound rho).2
  · intro s hs
    have h1 : s ≠ 1 := fun he => by simp [he] at hs
    exact regularizedLogDerivative_eq h1 (riemannZeta_ne_zero_of_one_le_re hs.le)

end RHConnections.ZetaZeroFreeRegion
