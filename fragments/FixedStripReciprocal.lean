import Verified

open Metric Set Filter
noncomputable section
namespace RHConnections.ZetaDiskLog
open ZetaEulerNearOne DiskNormInterpolation

private theorem strip_borel_on_centered_sphere {G : ℂ → ℂ} {c : ℂ} {R r M : ℝ}
    (hR : 0 < R) (hr : r < R) (hM : 0 < M)
    (hG : AnalyticOnNhd ℂ G (ball c R))
    (hRe : ∀ z ∈ ball c R, (G z).re ≤ M)
    {z : ℂ} (hz : z ∈ sphere c r) :
    ‖G z‖ ≤ 2*M*r/(R-r) + ‖G c‖*(R+r)/(R-r) := by
  let H := fun w => G (w+c)
  have hw (w : ℂ) (hw : w ∈ ball (0:ℂ) R) : w+c ∈ ball c R := by
    simpa [mem_ball, dist_eq_norm] using hw
  have hDiff : DifferentiableOn ℂ H (ball 0 R) := by
    intro w hw'
    have hD := (hG (w+c) (hw w hw')).differentiableAt
    exact (hD.comp w (differentiableAt_id.add_const c)).differentiableWithinAt
  have hmap : MapsTo H (ball 0 R) {x : ℂ | x.re ≤ M} := fun w hw' =>
    hRe _ (hw w hw')
  have hnr : ‖z-c‖ = r := by simpa [mem_sphere, dist_eq_norm] using hz
  have ht : z-c ∈ ball (0:ℂ) R := by simpa [mem_ball,dist_eq_norm,hnr] using hr
  have h := Complex.borelCaratheodory hM hDiff hmap hR ht
  simpa [H,hnr] using h

theorem reciprocal_zeta_outer_bound_of_strip
    {a : ℝ} (hno : ∀ s : ℂ, a < s.re → riemannZeta s ≠ 0)
    {b : ℝ} (ha : 1/2 ≤ a) (hb : a < b) (hb' : b < 1) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 ≤ θ ∧ θ < 1 ∧
      ∀ s : ℂ, b ≤ s.re → s.re ≤ 3 → 5 ≤ |s.im| →
        ‖(riemannZeta s)⁻¹‖ ≤ Real.exp (C*(1+Real.log (|s.im|+10))^θ) := by
  let e := b-a
  let R := 4-a-e/4
  let r₂ := 4-a-e/2
  let rmax := 4-b
  let r₁ : ℝ := 1/2
  let D := 1+Real.pi
  let θ := (Real.log rmax-Real.log r₁)/(Real.log r₂-Real.log r₁)
  let A := (4*r₂+D*(R+r₂))/(R-r₂)+D+1
  have he : 0 < e := by dsimp [e]; linarith
  have hR : 0 < R := by dsimp [R,e]; linarith
  have h1R : 1 < R := by dsimp [R,e]; linarith
  have hR' : R ≤ 7/2 := by dsimp [R]; linarith
  have hr₁ : 0 < r₁ := by norm_num [r₁]
  have hrmax : r₁ < rmax := by dsimp [r₁,rmax]; linarith
  have hr₂ : rmax < r₂ := by dsimp [rmax,r₂,e]; linarith
  have hr₂p : 0 < r₂ := hr₁.trans (hrmax.trans hr₂)
  have hr₂R : r₂ < R := by dsimp [r₂,R]; linarith
  have hlog₂ : 0 < Real.log r₂ - Real.log r₁ :=
    sub_pos.mpr (Real.log_lt_log hr₁ (hrmax.trans hr₂))
  have hθ₀ : 0 ≤ θ :=
    div_nonneg (sub_nonneg.mpr (Real.log_le_log hr₁ hrmax.le)) hlog₂.le
  have hθ₁ : θ < 1 :=
    (div_lt_one hlog₂).mpr (by linarith [Real.log_lt_log (hr₁.trans hrmax) hr₂])
  have hD : 1 ≤ D := by dsimp [D]; linarith [Real.pi_pos]
  have hA : 1 ≤ A := by
    dsimp [A]
    have h : 0 ≤ (4*r₂+D*(R+r₂))/(R-r₂) := by positivity
    linarith
  refine ⟨D*A^θ,θ,by positivity,hθ₀,hθ₁,?_⟩
  intro s hs h3 ht
  let t := s.im
  let c := verticalCenter t
  let L := |t|+10
  let r := 4-s.re
  let α := (Real.log r-Real.log r₁)/(Real.log r₂-Real.log r₁)
  have hL : 1 < L := by dsimp [L]; linarith [abs_nonneg t]
  have hLlog : 0 < Real.log L := Real.log_pos hL
  have hshift (w : ℂ) (hw : w ∈ ball c R) : a < w.re := by
    have h := (ball_verticalCenter_re_bounds hw).1
    dsimp [R] at h
    linarith
  have hnz (w : ℂ) (hw : w ∈ ball c R) : w ≠ 1 := by
    have h := (ball_verticalCenter_norm_bounds (by linarith : R ≤ 4) hw).2
    intro he
    rw [he,sub_self,norm_zero] at h
    change 5 ≤ |t| at ht
    linarith
  have hzeta : AnalyticOnNhd ℂ riemannZeta (ball c R) :=
    fun w hw => analyticOn_riemannZeta w (hnz w hw)
  obtain ⟨G,hG,hGc,hGe⟩ := analytic_log_on_ball hR hzeta (fun w hw => hno w (hshift w hw))
  have hSmall : ball c 1 ⊆ ball c R := Metric.ball_subset_ball h1R.le
  have hright (w : ℂ) (hw : w ∈ ball c (1:ℝ)) : 3 ≤ w.re := by
    have h := (ball_verticalCenter_re_bounds hw).1
    linarith
  have hprincipal := log_branch_eq_principal_on_positive_ball (show 0 < (1:ℝ) by norm_num)
    (hzeta.mono hSmall) (hG.mono hSmall) hGc
    (fun w hw => (by
      have h := (zeta_right_bounds (hright w hw)).2.2
      linarith : 0 < (riemannZeta w).re))
    (fun w hw => hGe w (hSmall hw))
  have hCenter : ‖G c‖ ≤ D := by
    rw [hGc]
    exact principal_log_norm_of_zeta_right (by norm_num [c,verticalCenter_re])
  have hinner (w : ℂ) (hw : w ∈ sphere c r₁) : ‖G w‖ ≤ D := by
    have hw' : w ∈ ball c 1 := by
      have h := Metric.mem_sphere.mp hw
      exact Metric.mem_ball.mpr (h.trans_lt (by norm_num [r₁]))
    rw [hprincipal hw']
    exact principal_log_norm_of_zeta_right (hright w hw')
  have hRe (w : ℂ) (hw : w ∈ ball c R) : (G w).re ≤ 2*Real.log L := by
    have hζ := zeta_norm_on_vertical_ball ht hR' hw
    have hζp := norm_pos_iff.mpr (hno w (hshift w hw))
    have h := Real.log_le_log hζp hζ
    rw [← hGe w hw, Complex.norm_exp, Real.log_exp] at h
    have hl3 : Real.log 3 ≤ Real.log L := Real.log_le_log (by norm_num)
      (by dsimp [L]; linarith [abs_nonneg t])
    have hL0 : 0 < L := by linarith
    rw [show (3:ℝ)*(|t|+10) = 3*L from rfl,
      Real.log_mul (by norm_num) hL0.ne'] at h
    linarith
  have houter (w : ℂ) (hw : w ∈ sphere c r₂) : ‖G w‖ ≤ A*(1+Real.log L) := by
    have h := strip_borel_on_centered_sphere hR hr₂R
      (by positivity : 0 < 2*Real.log L) hG hRe hw
    have hq : 0 ≤ (R+r₂)/(R-r₂) := by positivity
    have hv : ‖G w‖ ≤ (4*r₂*Real.log L+D*(R+r₂))/(R-r₂) := by
      calc
        _ ≤ 2*(2*Real.log L)*r₂/(R-r₂) + ‖G c‖*(R+r₂)/(R-r₂) := h
        _ = 2*(2*Real.log L)*r₂/(R-r₂) + ‖G c‖*((R+r₂)/(R-r₂)) := by ring
        _ ≤ 2*(2*Real.log L)*r₂/(R-r₂) + D*((R+r₂)/(R-r₂)) := by gcongr
        _ = _ := by ring
    have hN : 0 ≤ (4*r₂+D*(R+r₂))/(R-r₂) := by positivity
    apply hv.trans
    calc
      _ ≤ ((4*r₂+D*(R+r₂))*(1+Real.log L))/(R-r₂) := by
        apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hr₂R.le)
        nlinarith [mul_nonneg (by positivity : 0 ≤ D*(R+r₂)) hLlog.le]
      _ = ((4*r₂+D*(R+r₂))/(R-r₂))*(1+Real.log L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (by positivity)
  have hsr : r₁ < r := by dsimp [r,r₁]; linarith
  have hrR : r ≤ rmax := by dsimp [r,rmax]; linarith
  have hdist : ‖s-c‖ = r := by
    have he : s-c = ((s.re-4:ℝ):ℂ) := by
      apply Complex.ext
      · simp [c, verticalCenter_re, Complex.sub_re]
      · simp [c, t, verticalCenter_im, Complex.sub_im]
    rw [he,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (by linarith : s.re-4 ≤ 0)]
    dsimp [r]
    ring
  have hlower : 0 ≤ α :=
    div_nonneg (sub_nonneg.mpr (Real.log_le_log hr₁ hsr.le)) hlog₂.le
  have hupper : α ≤ θ :=
    div_le_div_of_nonneg_right (sub_le_sub_right (Real.log_le_log (hr₁.trans hsr) hrR) _) hlog₂.le
  have hCr : c+(s-c) = s := by ring
  have hcircle (w : ℂ) (a : ℝ) (hw : ‖w‖ = a) : c+w ∈ sphere c a := by
    simpa [mem_sphere,dist_eq_norm] using hw
  have hInterp := norm_le_three_circle G hr₁ hsr (hrR.trans_lt hr₂) hr₂R hG.differentiableOn
    (fun w hw => hinner (c+w) (hcircle w r₁ hw))
    (fun w hw => houter (c+w) (hcircle w r₂ hw)) hdist
  have hGnorm : ‖G s‖ ≤ D*A^θ*(1+Real.log L)^θ := by
    rw [hCr] at hInterp
    change ‖G s‖ ≤ D^(1-α)*(A*(1+Real.log L))^α at hInterp
    have h₁ : D^(1-α) ≤ D := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hD
        (show 1-α ≤ 1 by linarith)
    have h₂ : 1 ≤ A*(1+Real.log L) := one_le_mul_of_one_le_of_one_le hA (by linarith)
    calc
      _ ≤ D^(1-α)*(A*(1+Real.log L))^α := hInterp
      _ ≤ D*(A*(1+Real.log L))^θ := mul_le_mul h₁
        (Real.rpow_le_rpow_of_exponent_le h₂ hupper) (by positivity) (by positivity)
      _ = _ := by rw [Real.mul_rpow (by linarith) (by positivity)]; ring
  have hsB : s ∈ ball c R := by
    rw [mem_ball, dist_eq_norm, hdist]
    exact hrR.trans_lt (hr₂.trans hr₂R)
  rw [← hGe s hsB, norm_inv, Complex.norm_exp, ← Real.exp_neg]
  have hneg : -(G s).re ≤ ‖G s‖ := by
    simpa [Complex.neg_re,norm_neg] using Complex.re_le_norm (-G s)
  exact Real.exp_le_exp.mpr (hneg.trans hGnorm)

open scoped Topology
open PoleCompensation

theorem zetaReciprocal_analytic_of_strip {a : ℝ} (hno : ∀ s : ℂ, a < s.re → riemannZeta s ≠ 0) :
    AnalyticOnNhd ℂ zetaReciprocal {s : ℂ | a < s.re} := by
  intro s hs
  have hn : regularizedZeta s ≠ 0 := by
    by_cases he : s = 1
    · rw [he,regularizedZeta_one]
      exact one_ne_zero
    · rw [(regularizedZeta_germ he).eq_of_nhds]
      exact mul_ne_zero (sub_ne_zero.mpr he) (hno s hs)
  exact (analyticAt_id.sub analyticAt_const).div (regularizedZeta_analytic s) hn

private theorem strip_sublinear_log_bound_eventually {C θ η : ℝ}
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

theorem zetaReciprocal_subpower_of_strip {a : ℝ} (hno : ∀ s : ℂ, a < s.re → riemannZeta s ≠ 0)
    {b η : ℝ} (ha : 1/2 ≤ a) (hb : a < b) (hb' : b < 1) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, b ≤ s.re → s.re ≤ 3 →
      ‖zetaReciprocal s‖ ≤ C*(|s.im|+10)^η := by
  obtain ⟨C,θ,hC,hθ,hθ',hEst⟩ := reciprocal_zeta_outer_bound_of_strip hno ha hb hb'
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp (strip_sublinear_log_bound_eventually hC hθ hθ' hη)
  let T' := max T 5
  let K := closedBall (0:ℂ) (T'+3) ∩ {s : ℂ | b ≤ s.re}
  have hK : IsCompact K := (isCompact_closedBall 0 _).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hc : ContinuousOn (fun s => ‖zetaReciprocal s‖) K := by
    apply ContinuousOn.norm
    intro s hs
    exact ((zetaReciprocal_analytic_of_strip hno) s (hb.trans_le hs.2)).continuousAt.continuousWithinAt
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
