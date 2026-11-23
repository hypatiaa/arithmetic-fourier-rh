import Verified
import Mathlib.Analysis.Complex.Liouville

noncomputable section
open Metric Set Filter
open scoped Topology
namespace RHConnections.ZetaDiskLog
open PoleCompensation ZetaEulerNearOne

private theorem logDeriv_strip_borel_on_centered_sphere {G : ℂ → ℂ} {c : ℂ} {R r M : ℝ}
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

theorem regularizedLogDerivative_outer_log_of_strip {a : ℝ} (hno : ∀ s : ℂ, a < s.re → riemannZeta s ≠ 0)
    {b : ℝ} (ha : 1/2 ≤ a) (hb : a < b) (hb' : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, b ≤ s.re → s.re ≤ 2 → 5 ≤ |s.im| →
      ‖regularizedLogDerivative s‖ ≤ C*(1+Real.log (|s.im|+10)) := by

  let e := b-a
  let R := 4-a-e/4
  let r₂ := 4-a-e/2
  let rmax := 4-b
  let d := (r₂-rmax)/2
  let D := 1+Real.pi
  let A := (4*r₂+D*(R+r₂))/(R-r₂)+D+1
  have he : 0 < e := by dsimp [e]; linarith
  have hR : 0 < R := by dsimp [R,e]; linarith
  have h1R : 1 < R := by dsimp [R,e]; linarith
  have hR' : R ≤ 7/2 := by dsimp [R]; linarith
  have hr₂p : 0 < r₂ := by dsimp [r₂,e]; linarith
  have hd : 0 < d := by dsimp [d,r₂,rmax,e]; linarith
  have hr₂R : r₂ < R := by dsimp [r₂,R]; linarith
  have hD : 1 ≤ D := by dsimp [D]; linarith [Real.pi_pos]
  have hA : 1 ≤ A := by
    dsimp [A]
    have h : 0 ≤ (4*r₂+D*(R+r₂))/(R-r₂) := by positivity
    linarith
  refine ⟨A/d+1,by positivity,?_⟩
  intro s hs h3 ht
  let t := s.im
  let c := verticalCenter t
  let L := |t|+10
  let r := 4-s.re
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
  have hCenter : ‖G c‖ ≤ D := by
    rw [hGc]
    exact principal_log_norm_of_zeta_right (by norm_num [c,verticalCenter_re])
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
    have h := logDeriv_strip_borel_on_centered_sphere hR hr₂R
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
  have hdist : ‖s-c‖ = r := by
    have he : s-c = ((s.re-4:ℝ):ℂ) := by
      apply Complex.ext
      · simp [c, verticalCenter_re, Complex.sub_re]
      · simp [c, t, verticalCenter_im, Complex.sub_im]
    rw [he,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (by linarith : s.re-4 ≤ 0)]
    dsimp [r]
    ring
  have hsc : dist s c ≤ rmax := by
    rw [dist_eq_norm,hdist]
    dsimp [r,rmax]
    linarith
  have hinner : closedBall s d ⊆ closedBall c r₂ := by
    intro w hw
    apply Metric.mem_closedBall.mpr
    have h := dist_triangle w s c
    have hw' := Metric.mem_closedBall.mp hw
    dsimp [d] at hw'
    dsimp [d] at hd
    linarith
  have hsub : closedBall c r₂ ⊆ ball c R := closedBall_subset_ball hr₂R
  have hGd := hG.differentiableOn.diffContOnCl_ball (hinner.trans hsub)
  have hbound (w : ℂ) (hw : w ∈ sphere s d) : ‖G w‖ ≤ A*(1+Real.log L) := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hG.differentiableOn.diffContOnCl_ball hsub)
      (fun z hz => houter z (frontier_ball_subset_sphere hz))
    rw [closure_ball _ hr₂p.ne']
    exact hinner (Metric.sphere_subset_closedBall hw)
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hd hGd hbound
  have hsB := hsub (hinner (mem_closedBall_self hd.le))
  have hgerm : (Complex.exp ∘ G) =ᶠ[𝓝 s] riemannZeta := by
    filter_upwards [isOpen_ball.mem_nhds hsB] with w hw
    exact hGe w hw
  have hprime := hgerm.deriv_eq
  rw [((Complex.hasDerivAt_exp (G s)).comp s (hG s hsB).differentiableAt.hasDerivAt).deriv,
    hGe s hsB] at hprime
  have hn := hno s (hb.trans_le hs)
  have h1 := hnz s hsB
  have hquot : -deriv riemannZeta s / riemannZeta s = -deriv G s := by
    rw [← hprime]
    field_simp [hn]
  have hdist1 : 1 ≤ ‖s-1‖ := by
    have hi := Complex.abs_im_le_norm (s-1)
    simp only [Complex.sub_im,Complex.one_im,sub_zero] at hi
    linarith
  have hpole : ‖1/(s-1)‖ ≤ 1 := by
    rw [norm_div,norm_one]
    exact (div_le_one (by linarith)).mpr hdist1
  rw [regularizedLogDerivative_eq h1 hn,compensatedLogDerivative,hquot]
  calc
    _ ≤ ‖-deriv G s‖+‖1/(s-1)‖ := norm_sub_le _ _
    _ ≤ A*(1+Real.log L)/d+1 := add_le_add (by simpa using hder) hpole
    _ ≤ (A/d+1)*(1+Real.log L) := by
      rw [show A*(1+Real.log L)/d = A/d*(1+Real.log L) by ring]
      nlinarith

theorem regularizedLogDerivative_subpower_of_strip {a : ℝ} (hno : ∀ s : ℂ, a < s.re → riemannZeta s ≠ 0)
    {b η : ℝ} (ha : 1/2 ≤ a) (hb : a < b) (hb' : b < 1) (hη : 0 < η) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, b ≤ s.re → s.re ≤ 2 →
      ‖regularizedLogDerivative s‖ ≤ D*(1+|s.im|)^η := by
  obtain ⟨C,hC,hout⟩ := regularizedLogDerivative_outer_log_of_strip hno ha hb hb'
  let K := closedBall (0:ℂ) 7 ∩ {s : ℂ | b ≤ s.re}
  have hK : IsCompact K := (isCompact_closedBall 0 _).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hc : ContinuousOn (fun s => ‖regularizedLogDerivative s‖) K := by
    intro s hs
    exact ((regularizedLogDerivative_on_halfplane hno s
      (hb.trans_le hs.2)).continuousAt.norm).continuousWithinAt
  obtain ⟨B,hB⟩ := hK.bddAbove_image hc
  let D := max (max B 0) (C*(1+10^η/η))
  have hD : 0 ≤ D := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨D,hD,?_⟩
  intro s hs h2
  let X := 1+|s.im|
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg s.im]
  have hp : 1 ≤ X^η := Real.one_le_rpow hX hη.le
  by_cases ht : 5 ≤ |s.im|
  · have hpow : (|s.im|+10)^η ≤ 10^η * X^η := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤10) (by linarith : 0≤X)]
      apply Real.rpow_le_rpow (by positivity) _ hη.le
      dsimp [X]
      linarith [abs_nonneg s.im]
    have hl := Real.log_le_rpow_div (by positivity : 0≤|s.im|+10) hη
    have hq := div_le_div_of_nonneg_right hpow hη.le
    calc
      _ ≤ C*(1+Real.log (|s.im|+10)) := hout s hs h2 ht
      _ ≤ C*(X^η+(10^η*X^η)/η) := by gcongr; linarith
      _ = (C*(1+10^η/η))*X^η := by ring
      _ ≤ D*X^η := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hsK : s ∈ K := by
      refine ⟨?_,hs⟩
      rw [mem_closedBall,dist_zero_right]
      apply (Complex.norm_le_abs_re_add_abs_im s).trans
      rw [abs_of_nonneg (by linarith : 0≤s.re)]
      linarith [lt_of_not_ge ht]
    calc
      _ ≤ B := hB (Set.mem_image_of_mem _ hsK)
      _ ≤ D := (le_max_left _ _).trans (le_max_left _ _)
      _ ≤ D*X^η := by simpa using mul_le_mul_of_nonneg_left hp hD

end RHConnections.ZetaDiskLog
