import Verified
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set Metric
noncomputable section
namespace RHConnections.PrimeAtomObstruction

def center : ℝ := Real.log 2

def radius : ℝ := min (center/2) ((Real.log 3 - center)/2)

private theorem center_pos : 0 < center := Real.log_pos (by norm_num)

private theorem center_lt_log_three : center < Real.log 3 :=
  Real.log_lt_log (by norm_num) (by norm_num)

theorem radius_pos : 0 < radius := by
  unfold radius
  exact lt_min (by linarith [center_pos]) (by linarith [center_lt_log_three])

theorem closed_support_inside :
    Icc (center-radius) (center+radius) ⊆ Ioo 0 (Real.log 3) := by
  intro x hx
  have h₀ : radius ≤ center/2 := min_le_left _ _
  have h₁ : radius ≤ (Real.log 3-center)/2 := min_le_right _ _
  exact ⟨by linarith [hx.1,center_pos],by linarith [hx.2,center_lt_log_three]⟩

def bump (r : ℝ) (hr : 0 < r) : ContDiffBump center where
  rIn := r/2
  rOut := r
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

def test (r : ℝ) (hr : 0 < r) (x : ℝ) : ℂ := (bump r hr x : ℝ)

theorem test_smooth (r : ℝ) (hr : 0 < r) : ContDiff ℝ ∞ (test r hr) :=
  Complex.ofRealCLM.contDiff.comp (bump r hr).contDiff

theorem test_at_center (r : ℝ) (hr : 0 < r) : test r hr center = 1 := by
  have he := (bump r hr).one_of_mem_closedBall
    (mem_closedBall_self (show 0 ≤ r/2 by linarith))
  simp [test,he]

theorem test_norm_le_one (r : ℝ) (hr : 0 < r) (x : ℝ) : ‖test r hr x‖ ≤ 1 := by
  rw [test,Complex.norm_of_nonneg ((bump r hr).nonneg' x)]
  exact (bump r hr).le_one

theorem test_zero_off_interval (r : ℝ) (hr : 0 < r) {x : ℝ}
    (hx : x ∉ Ioo (center-r) (center+r)) : test r hr x = 0 := by
  have hd : r ≤ dist x center := by
    by_contra! hlt
    apply hx
    rw [Real.dist_eq,abs_lt] at hlt
    exact ⟨by linarith [hlt.1],by linarith [hlt.2]⟩
  simp [test,(bump r hr).zero_of_le_dist hd]

theorem support_interval_inside {r : ℝ} (hr : r ≤ radius) :
    Ioo (center-r) (center+r) ⊆ Icc (center-radius) (center+radius) := by
  exact fun x hx => ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem test_compact (r : ℝ) (hr : 0 < r) : HasCompactSupport (test r hr) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := center-r) (b := center+r)) ?_
  exact fun x hx => test_zero_off_interval r hr (fun h => hx ⟨h.1.le,h.2.le⟩)

private theorem integral_width_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r C : ℝ} (hr : 0 < r) {F : ℝ → E} (hC : ∀ x ∈ Ioo (center-r) (center+r), ‖F x‖ ≤ C)
    (hz : ∀ x ∉ Ioo (center-r) (center+r), F x = 0) :
    ‖∫ x : ℝ, F x‖ ≤ (2*r)*C := by
  let J := Ioo (center-r) (center+r)
  have he : J.indicator F = F := by
    funext x
    by_cases hx : x ∈ J
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,hz x hx]
  have h : ‖∫ x in J, F x‖ ≤ C * (volume : Measure ℝ).real J :=
    norm_setIntegral_le_of_norm_le_const (show (volume : Measure ℝ) J < ⊤ from measure_Ioo_lt_top) hC
  rw [← integral_indicator measurableSet_Ioo,he] at h
  have hμ : (volume : Measure ℝ).real J = 2*r := by
    change (volume (Ioo (center-r) (center+r))).toReal = 2*r
    rw [Real.volume_Ioo,ENNReal.toReal_ofReal (by linarith)]
    ring
  simpa only [hμ,mul_comm C] using h

def weightedMass (w : ℝ → ℝ) (f : ℝ → ℂ) : ℝ := ∫ x : ℝ, ‖f x‖^2*w x

theorem weightedMass_bound {w : ℝ → ℝ} (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ radius →
      0 ≤ weightedMass w (test r hr) ∧ weightedMass w (test r hr) ≤ (2*r)*C := by
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := center-radius) (b := center+radius)).bddAbove_image
    hw.continuousOn
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro r hr hr'
  have hn : 0 ≤ weightedMass w (test r hr) :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw0 x))
  refine ⟨hn,?_⟩
  rw [← Real.norm_of_nonneg hn]
  apply integral_width_bound hr
  · intro x hx
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hw0 x))]
    refine (mul_le_mul_of_nonneg_right
      (show ‖test r hr x‖^2 ≤ 1 by nlinarith [test_norm_le_one r hr x,norm_nonneg (test r hr x)])
      (hw0 x)).trans ?_
    rw [one_mul]
    exact (hB (mem_image_of_mem _ (support_interval_inside hr' hx))).trans (le_max_left _ _)
  · exact fun x hx => by simp [test_zero_off_interval r hr hx]

theorem density_integral_bound {G : ℝ → ℂ} (hG : ContinuousOn G (Ioi 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ radius →
      ‖∫ x in Ioi (0:ℝ), G x*test r hr x‖ ≤ (2*r)*C := by
  have hc : ContinuousOn (fun x => ‖G x‖) (Icc (center-radius) (center+radius)) :=
    hG.norm.mono (fun x hx => (closed_support_inside hx).1)
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := center-radius) (b := center+radius)).bddAbove_image hc
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro r hr hr'
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_width_bound hr
  · intro x hx
    have hx' : x ∈ Ioi (0:ℝ) := (closed_support_inside (support_interval_inside hr' hx)).1
    rw [indicator_of_mem hx', norm_mul]
    exact ((mul_le_mul_of_nonneg_left (test_norm_le_one r hr x) (norm_nonneg _)).trans_eq
      (mul_one _)).trans ((hB (mem_image_of_mem _ (support_interval_inside hr' hx))).trans (le_max_left _ _))
  · intro x hx
    by_cases hx' : x ∈ Ioi (0:ℝ)
    · rw [indicator_of_mem hx',test_zero_off_interval r hr hx,mul_zero]
    · exact indicator_of_notMem hx' _

def stripWeight (a b s : ℝ) (x : ℝ) : ℝ :=
  max (Real.exp (2*a*x)) (Real.exp (2*b*x)) * (1+|x|^2)^(s/2)

theorem stripWeight_continuous (a b s : ℝ) : Continuous (stripWeight a b s) := by
  unfold stripWeight
  apply Continuous.mul
  · fun_prop
  · apply continuous_iff_continuousAt.mpr
    intro x
    let F := fun y : ℝ => 1+|y|^2
    have hF : ContinuousAt F x := by unfold F; fun_prop
    have hn : F x ≠ 0 := by dsimp [F]; positivity
    exact (Real.continuousAt_rpow_const (F x) (s/2) (Or.inl hn)).comp hF

theorem stripWeight_nonneg (a b s x : ℝ) : 0 ≤ stripWeight a b s x := by
  unfold stripWeight
  exact mul_nonneg ((Real.exp_pos _).le.trans (le_max_left _ _))
    (Real.rpow_nonneg (by positivity) _)

end RHConnections.PrimeAtomObstruction
