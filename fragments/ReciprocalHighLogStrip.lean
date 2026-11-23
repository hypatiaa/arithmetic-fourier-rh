import ReciprocalMovingDisk
open Set Metric
noncomputable section
namespace RHConnections.ReciprocalLocalComparison
open ZetaZeroFreeRegion ZetaDiskLog PoleCompensation

private theorem euler_envelope {a q H : ℝ} (ha : 0<a) (hq : 0<q) (hH : 0<H) :
    2+H/a ≤ Real.exp ((2+1/(a*q))+q*H) := by
  let K := 2+1/(a*q)
  have hk : 2 ≤ K := by dsimp [K]; linarith [show 0 < 1/(a*q) by positivity]
  have he : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have he' := Real.add_one_le_exp (q*H)
  have hm := mul_le_mul he he' (by positivity : 0≤q*H+1) (Real.exp_nonneg K)
  rw [Real.exp_add]
  refine le_trans ?_ hm
  have hc : (1/(a*q))*(q*H) = H/a := by field_simp
  dsimp [K] at *
  nlinarith [mul_pos hq hH]

theorem narrow_high {C q a : ℝ} (hC : 0<C) (hCa : C≤1/2)
    (hq : 0<q) (hq1 : q≤1) (haeq : a=C*q/64)
    (hn : ∀ s : ℂ, 1-C/heightFactor s.im < s.re → riemannZeta s ≠ 0)
    {s : ℂ} (ht : 5≤|s.im|) (hs : 1-a/heightFactor s.im ≤ s.re) :
    ‖zetaReciprocal s‖ ≤ Real.exp (2*(2+1/(a*q))+4*q*heightFactor s.im) := by
  let H := heightFactor s.im
  let c : ℂ := ⟨1+a/H,s.im⟩
  let R := C/(4*H)
  let K := 2+1/(a*q)
  have hH1 : 1≤H := heightFactor_one_le _
  have hH : 0<H := by linarith
  have ha : 0<a := by rw [haeq]; positivity
  have haC : a≤C := by nlinarith [mul_le_mul_of_nonneg_left hq1 hC.le]
  have haH : 0<a/H := by positivity
  have hK : 0<K := by positivity
  have hR : 0<R := by positivity
  have henv := euler_envelope ha hq hH
  have heuler {w : ℂ} (hw : 1+a/H ≤ w.re) :
      ‖zetaReciprocal w‖ ≤ Real.exp (K+q*H) := by
    have h := euler_reciprocal_bound (by linarith : 1<w.re)
    have hdiv := one_div_le_one_div_of_le haH (show a/H ≤ w.re-1 by linarith)
    rw [show 1/(a/H) = H/a by field_simp] at hdiv
    exact (h.trans (by linarith : 2+1/(w.re-1)≤2+H/a)).trans henv
  by_cases hright : 1+a/H ≤ s.re
  · exact (heuler hright).trans (Real.exp_le_exp.mpr (by change K+q*H≤2*K+4*q*H; nlinarith [mul_pos hq hH]))
  let r := 1+a/H-s.re
  have hr0 : 0<r := sub_pos.mpr (lt_of_not_ge hright)
  have hrad : r≤2*a/H := by
    change 1-a/H ≤ s.re at hs
    dsimp [r]
    linarith [show 2*a/H=2*(a/H) by ring]
  have hratio : 2*r ≤ q*(R-r) := by
    have h1 : 2*a/H = (q*R)/8 := by dsimp [R]; rw [haeq]; ring
    have h2 := mul_le_mul_of_nonneg_right hq1 hr0.le
    rw [h1] at hrad
    nlinarith
  have hrr : r<R := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hq.le (sub_nonpos.mpr h)]
  have hd := disk_data hC hCa ha haC hn ht
  have hfn : ∀ w ∈ ball c R, riemannZeta w ≠ 0 := fun w hw => (hd w hw).1
  have hfa : AnalyticOnNhd ℂ riemannZeta (ball c R) := fun w hw =>
    analyticOn_riemannZeta w (hd w hw).2.1
  have hsphere : s ∈ sphere c r := by
    rw [mem_sphere,dist_eq_norm]
    have he : s-c = ((s.re-(1+a/H):ℝ):ℂ) := by apply Complex.ext <;> simp [c]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_neg (sub_neg.mpr (lt_of_not_ge hright))]
    dsimp [r]; ring
  have hcv := heuler (w:=c) (le_refl _)
  rw [zetaReciprocal_eq_inv_of_ne_one ((hd c (mem_ball_self hR)).2.1)] at hcv
  have hbc := reciprocal_le_exp_disk hR hrr hsphere hfa hfn
    (fun w hw => (hd w hw).2.2) hcv (show 0<2*H+(K+q*H) by positivity)
  have hsin : s ∈ ball c R := mem_ball.mpr ((mem_sphere.mp hsphere).trans_lt hrr)
  rw [zetaReciprocal_eq_inv_of_ne_one ((hd s hsin).2.1)]
  apply hbc.trans (Real.exp_le_exp.mpr ?_)
  have hm := mul_le_mul_of_nonneg_left hratio (show 0≤2*H+(K+q*H) by positivity)
  have hb : 2*(2*H+(K+q*H))*r/(R-r) ≤ q*(2*H+(K+q*H)) := by
    apply (div_le_iff₀ (sub_pos.mpr hrr)).mpr
    nlinarith only [hm]
  change K+q*H+_ ≤ 2*K+4*q*H
  nlinarith [mul_le_mul_of_nonneg_right hq1 hK.le,mul_le_mul_of_nonneg_right hq1 (mul_pos hq hH).le]
end RHConnections.ReciprocalLocalComparison
