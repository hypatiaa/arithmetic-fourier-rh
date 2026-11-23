import Verified
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Metric Set Filter
open scoped Topology
noncomputable section
namespace RHConnections.ZetaDiskLog
open PoleCompensation

def zetaReciprocal (s : ℂ) : ℂ := (s-1)/regularizedZeta s

theorem right_zero_free_of_RH (hRH : RiemannHypothesis) :
    ∀ s : ℂ, 1/2 < s.re → riemannZeta s ≠ 0 := by
  intro s hs hz
  have hs1 : s ≠ 1 := fun h => by
    subst s
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hz
  have hnt : ¬∃ n : ℕ, s = -2*(n+1) := by
    rintro ⟨n,rfl⟩
    norm_num [Complex.mul_re,Complex.add_re] at hs
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact (ne_of_gt hs) (hRH s hz hnt hs1)

theorem zetaReciprocal_analytic_of_RH (hRH : RiemannHypothesis) :
    AnalyticOnNhd ℂ zetaReciprocal {s : ℂ | 1/2 < s.re} := by
  intro s hs
  have hn : regularizedZeta s ≠ 0 := by
    by_cases he : s = 1
    · rw [he,regularizedZeta_one]
      exact one_ne_zero
    · rw [(regularizedZeta_germ he).eq_of_nhds]
      exact mul_ne_zero (sub_ne_zero.mpr he) (right_zero_free_of_RH hRH s hs)
  exact (analyticAt_id.sub analyticAt_const).div (regularizedZeta_analytic s) hn

theorem zetaReciprocal_eq_inv_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    zetaReciprocal s = (riemannZeta s)⁻¹ := by
  rw [zetaReciprocal,(regularizedZeta_germ hs).eq_of_nhds,
    div_eq_mul_inv, _root_.mul_inv_rev]
  calc
    _ = ((s-1)*(s-1)⁻¹)*(riemannZeta s)⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

private theorem sublinear_log_bound_eventually {C θ η : ℝ}
    (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hθ' : θ < 1) (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, C*(1+Real.log (t+10))^θ ≤ η*Real.log (t+10) := by
  have hLog : Tendsto (fun t : ℝ => Real.log (t+10)) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro d
    filter_upwards [eventually_ge_atTop (Real.exp d)] with t ht
    rw [← Real.log_exp d]
    exact Real.log_le_log (Real.exp_pos _) (ht.trans (by linarith))
  have hdecay : Tendsto (fun t : ℝ => (C*2^θ)*(Real.log (t+10))^(θ-1)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (show 0 < 1-θ by linarith)).comp hLog).const_mul (C*2^θ)
    simpa only [mul_zero,Function.comp_apply, neg_sub] using h
  filter_upwards [(tendsto_order.mp hdecay).2 η hη,
    (Filter.tendsto_atTop.mp hLog) 1] with t ht ht₁
  let y := Real.log (t+10)
  have hp : 0 < y := zero_lt_one.trans_le ht₁
  change C*(1+y)^θ ≤ η*y
  have hmul : y^(θ-1)*y = y^θ := by
    calc
      _ = y^(θ-1)*y^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hp, show θ-1+1=θ by ring]
  calc
    _ ≤ C*(2*y)^θ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hθ) hC
    _ = (C*2^θ)*y^θ := by rw [Real.mul_rpow (by norm_num) hp.le]; ring
    _ = (C*2^θ)*(y^(θ-1)*y) := by rw [hmul]
    _ = ((C*2^θ)*y^(θ-1))*y := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ht.le hp.le

theorem zetaReciprocal_subpower_of_RH (hRH : RiemannHypothesis)
    {b η : ℝ} (hb : 1/2 < b) (hb' : b < 1) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, b ≤ s.re → s.re ≤ 3 →
      ‖zetaReciprocal s‖ ≤ C*(|s.im|+10)^η := by
  obtain ⟨C,θ,hC,hθ,hθ',hEst⟩ := reciprocal_zeta_outer_bound (right_zero_free_of_RH hRH) hb hb'
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp (sublinear_log_bound_eventually hC hθ hθ' hη)
  let T' := max T 5
  let K := closedBall (0:ℂ) (T'+3) ∩ {s : ℂ | b ≤ s.re}
  have hK : IsCompact K := (isCompact_closedBall 0 _).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hc : ContinuousOn (fun s => ‖zetaReciprocal s‖) K := by
    apply ContinuousOn.norm
    intro s hs
    exact ((zetaReciprocal_analytic_of_RH hRH) s (hb.trans_le hs.2)).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩ := hK.bddAbove_image hc
  let A := max B 1
  have hA : 1 ≤ A := le_max_right _ _
  refine ⟨A,zero_le_one.trans hA,?_⟩
  intro s hsb hs3
  have hsbase : 1 ≤ |s.im|+10 := by linarith [abs_nonneg s.im]
  have hpow : 1 ≤ (|s.im|+10)^η := Real.one_le_rpow hsbase hη.le
  by_cases ht : T' ≤ |s.im|
  · have ht1 : 5 ≤ |s.im| := (le_max_right _ _).trans ht
    have hsame : s ≠ 1 := by
      intro he
      norm_num [he] at ht1
    have hlog := hT |s.im| ((le_max_left _ _).trans ht)
    rw [zetaReciprocal_eq_inv_of_ne_one hsame]
    calc
      _ ≤ Real.exp (C*(1+Real.log (|s.im|+10))^θ) := hEst s hsb hs3 ht1
      _ ≤ Real.exp (η*Real.log (|s.im|+10)) := Real.exp_le_exp.mpr hlog
      _ = (|s.im|+10)^η := by rw [Real.rpow_def_of_pos (by linarith), mul_comm]
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hA (by positivity)
  · have hsK : s ∈ K := by
      refine ⟨?_, hsb⟩
      rw [mem_closedBall, dist_zero_right]
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      have hsr : 0 ≤ s.re := by linarith
      rw [abs_of_nonneg hsr]
      linarith [lt_of_not_ge ht]
    calc
      _ ≤ B := hB (Set.mem_image_of_mem _ hsK)
      _ ≤ A := le_max_left _ _
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hA)

end RHConnections.ZetaDiskLog
