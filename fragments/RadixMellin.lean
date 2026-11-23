import Verified

noncomputable section
namespace RHConnections.RadixMellin
open Filter Asymptotics MeasureTheory
open scoped Topology

def floorValue (u : ℝ) : ℂ := (⌊u⌋₊ : ℂ)
def residue (r : ℕ) (u : ℝ) : ℂ := floorValue u - (r : ℂ) * floorValue (u / r)
def weight (r : ℕ) (x : ℝ) : ℂ := residue r x⁻¹

theorem residue_mod (r : ℕ) (u : ℝ) : residue r u = (⌊u⌋₊ % r : ℕ) := by
  unfold residue floorValue
  rw [Nat.floor_div_natCast]
  have e := congrArg (fun n : ℕ => (n : ℂ)) (Nat.mod_add_div ⌊u⌋₊ r)
  push_cast at e
  linear_combination -e

private theorem floor_local : LocallyIntegrableOn floorValue (Set.Ioi 0) := by
  have hc (n : ℕ) : (∑ k ∈ Finset.Icc 1 n, (1:ℂ)) = n := by simp [Nat.card_Icc]
  have h := locallyIntegrableOn_mul_sum_Icc (m := 1) (fun _ : ℕ => (1:ℂ)) (a := (0:ℝ))
    le_rfl (locallyIntegrableOn_const (1:ℂ))
  simp only [one_mul, hc] at h
  exact h.mono_set Set.Ioi_subset_Ici_self

private theorem floor_converges {s : ℂ} (hs : 1 < s.re) : MellinConvergent floorValue (-s) := by
  apply mellinConvergent_of_isBigO_rpow (a := -1) (b := -s.re-1) floor_local
  · refine isBigO_iff.mpr ⟨1,?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simpa [floorValue,abs_of_pos hx] using Nat.floor_le hx.le
  · simp; linarith
  · refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with x hx
    simp [floorValue,Nat.floor_eq_zero.mpr hx]
  · simp

private theorem floor_transform {s : ℂ} (hs : 1 < s.re) :
    s * mellin floorValue (-s) = riemannZeta s := by
  have hc (n : ℕ) : (∑ k ∈ Finset.Icc 1 n, (1:ℂ)) = n := by simp [Nat.card_Icc]
  have ho : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1:ℂ)) =O[atTop] (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1,Filter.Eventually.of_forall fun n => ?_⟩
    simp [hc]
  have hi := LSeries_eq_mul_integral (1 : ℕ → ℂ) (by norm_num : (0:ℝ)≤1) hs
    (LSeriesSummable_one_iff.mpr hs) ho
  rw [LSeries_one_eq_riemannZeta hs] at hi
  rw [hi]
  congr 1
  unfold mellin
  let f := fun x : ℝ => (x:ℂ)^(-s-1) • floorValue x
  have he : f = (Set.Ici (1:ℝ)).indicator f := by
    funext x
    by_cases hx : 1 ≤ x
    · simp [hx]
    · simp [f,floorValue,hx,Nat.floor_eq_zero.mpr (lt_of_not_ge hx)]
  change (∫ x in Set.Ioi (0:ℝ), f x) = _
  rw [he, setIntegral_indicator measurableSet_Ici, Set.inter_eq_right.mpr
    (show Set.Ici (1:ℝ) ⊆ Set.Ioi 0 by intro x hx; exact lt_of_lt_of_le (zero_lt_one : (0:ℝ)<1) (Set.mem_Ici.mp hx)),
    integral_Ici_eq_integral_Ioi]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => by
    change 1 < x at hx
    simp [f,floorValue,hc,smul_eq_mul,show -(s+1) = -s-1 by ring,mul_comm]

theorem euler {r : ℕ} (hr : 0 < r) {s : ℂ} (hs : 1 < s.re) :
    mellin (weight r) s = (1-(r:ℂ)^(1-s))*riemannZeta s/s := by
  have hR : 0 < (r:ℝ) := by exact_mod_cast hr
  have hC : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs0 : s ≠ 0 := by intro e; norm_num [e] at hs
  have harg : (r:ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast,Complex.arg_ofReal_of_nonneg hR.le]
    exact Real.pi_pos.ne
  have hf := floor_converges hs
  have hg := (MellinConvergent.comp_mul_left (f := floorValue) (inv_pos.mpr hR)).2 hf
  have h := (hasMellin_sub hf (hg.const_smul (r:ℂ))).2
  have he : residue r = fun t : ℝ => floorValue t - (r:ℂ) • floorValue ((r:ℝ)⁻¹*t) := by
    funext t; simp [residue,div_eq_inv_mul]
  change mellin (fun t : ℝ => residue r t⁻¹) s = _
  rw [mellin_comp_inv, he, h, mellin_const_smul, mellin_comp_mul_left _ _ (inv_pos.mpr hR)]
  simp only [neg_neg,Complex.ofReal_inv,Complex.ofReal_natCast,Complex.inv_cpow _ _ harg,smul_eq_mul]
  rw [sub_eq_add_neg (1:ℂ) s,Complex.cpow_add _ _ hC,Complex.cpow_one,Complex.cpow_neg]
  apply (eq_div_iff hs0).2
  rw [← floor_transform hs]
  ring

private theorem residue_bound {r : ℕ} (hr : 0 < r) (u : ℝ) : ‖residue r u‖ ≤ r := by
  rw [residue_mod,Complex.norm_natCast]
  exact_mod_cast (Nat.mod_lt ⌊u⌋₊ hr).le

private theorem residue_local {r : ℕ} (hr : 0 < r) :
    LocallyIntegrableOn (residue r) (Set.Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k _ hk
  have hm : Measurable (residue r) := by unfold residue floorValue; fun_prop
  exact (integrableOn_const (C := (r:ℝ)) hk.measure_lt_top.ne).mono'
    hm.aestronglyMeasurable (Filter.Eventually.of_forall (residue_bound hr))

theorem transform_analytic {r : ℕ} (hr : 0 < r) :
    AnalyticOnNhd ℂ (mellin (weight r)) {z : ℂ | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  have ht : residue r =O[atTop] (fun x : ℝ => x^(-(0:ℝ))) := by
    refine isBigO_iff.mpr ⟨r,Filter.Eventually.of_forall fun x => ?_⟩
    simpa using residue_bound hr x
  have hb : residue r =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-(-s.re-1))) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with x hx
    simp [residue_mod,Nat.floor_eq_zero.mpr hx]
  have hd := mellin_differentiableAt_of_isBigO_rpow (s := -s) (residue_local hr) ht
    (by change -s.re < 0; change 0 < s.re at hs; linarith) hb
    (by change -s.re-1 < -s.re; linarith)
  have he : mellin (weight r) = fun z : ℂ => mellin (residue r) (-z) := by
    funext z; exact mellin_comp_inv (residue r) z
  rw [he]
  exact (hd.comp s differentiableAt_id.neg).differentiableWithinAt

open PoleCompensation

theorem regularized {r : ℕ} (hr : 0 < r) {s : ℂ} (hs : 0 < s.re) :
    (s-1)*s*mellin (weight r) s = (1-(r:ℂ)^(1-s))*regularizedZeta s := by
  let H : Set ℂ := {z | 0 < z.re}
  have hC : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hA : AnalyticOnNhd ℂ (fun z : ℂ => (z-1)*z*mellin (weight r) z) H :=
    fun z hz => ((analyticAt_id.sub analyticAt_const).mul analyticAt_id).mul (transform_analytic hr z hz)
  have hB : AnalyticOnNhd ℂ (fun z : ℂ => (1-(r:ℂ)^(1-z))*regularizedZeta z) H := by
    intro z _
    apply AnalyticAt.mul _ (regularizedZeta_analytic z)
    apply analyticAt_const.sub
    simp_rw [Complex.cpow_def_of_ne_zero hC]
    exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).cexp'
  have hb : {z : ℂ | 1 < z.re} ∈ 𝓝 (2:ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  apply hA.eqOn_of_preconnected_of_eventuallyEq hB (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ H by norm_num [H]) _ (show s ∈ H from hs)
  filter_upwards [hb] with z hz
  change 1 < z.re at hz
  have hz1 : z ≠ 1 := fun e => by norm_num [e] at hz
  have hz0 : z ≠ 0 := fun e => by norm_num [e] at hz
  rw [euler hr hz,(regularizedZeta_germ hz1).eq_of_nhds]
  field_simp

theorem transform {r : ℕ} (hr : 0 < r) {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    mellin (weight r) s = (1-(r:ℂ)^(1-s))*riemannZeta s/s := by
  have h := regularized hr hs
  rw [(regularizedZeta_germ h1).eq_of_nhds] at h
  have hs0 : s ≠ 0 := fun e => by norm_num [e] at hs
  apply (eq_div_iff hs0).2
  apply mul_left_cancel₀ (sub_ne_zero.mpr h1)
  linear_combination h

theorem transform_one {r : ℕ} (hr : 0 < r) :
    mellin (weight r) 1 = (Real.log (r : ℝ) : ℂ) := by
  have hC : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hD := (transform_analytic hr 1 (by norm_num)).differentiableAt.hasDerivAt
  have hL := (((hasDerivAt_id (1:ℂ)).sub_const 1).mul (hasDerivAt_id (1:ℂ))).mul hD
  have hE := ((hasDerivAt_id (1:ℂ)).const_sub 1).const_cpow (c := (r:ℂ)) (Or.inl hC)
  have hR := (hE.const_sub 1).mul (regularizedZeta_analytic 1).differentiableAt.hasDerivAt
  have he : (fun z : ℂ => (z-1)*z*mellin (weight r) z) =ᶠ[𝓝 (1:ℂ)]
      (fun z : ℂ => (1-(r:ℂ)^(1-z))*regularizedZeta z) := by
    have hb : {z : ℂ | 0 < z.re} ∈ 𝓝 (1:ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hb] with z hz using regularized hr hz
  have h := (hL.congr_of_eventuallyEq he.symm).unique hR
  have hl : Complex.log (r:ℂ) = (Real.log (r:ℝ):ℂ) := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_log (Nat.cast_nonneg r)]
  simp only [Pi.mul_apply,id_eq,sub_self,zero_mul,one_mul,mul_one,Complex.cpow_zero,
    regularizedZeta_one, mul_neg, neg_neg, add_zero, hl] at h
  exact h

theorem transform_limit_one {r : ℕ} (hr : 0 < r) :
    Tendsto (mellin (weight r)) (𝓝 (1:ℂ)) (𝓝 (Real.log (r : ℝ) : ℂ)) := by
  rw [← transform_one hr]
  exact (transform_analytic hr 1 (by norm_num)).continuousAt

end RHConnections.RadixMellin
