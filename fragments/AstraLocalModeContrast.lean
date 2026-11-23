import Verified
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open Filter Set MeasureTheory
open scoped Topology
noncomputable section

namespace RHConnections.LocalModeContrast

def segment (a b s : ℝ) : ℝ := (1-s)*a+s*b

def normalizedMean (g : ℝ → ℂ) (a b : ℝ) : ℂ :=
  ∫ s in (0:ℝ)..1, g (segment a b s)

private theorem segment_mem {a b l u s : ℝ} (ha : a ∈ Ioo l u) (hb : b ∈ Ioo l u)
    (hs : s ∈ Icc (0:ℝ) 1) : segment a b s ∈ Ioo l u := by
  exact (convex_Ioo l u) ha hb (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel _ _)

private theorem segment_cont (a b : ℝ) : Continuous (segment a b) := by
  unfold segment
  fun_prop

theorem local_mean_contrast {g v : ℝ → ℂ} (hd : ∀ᶠ y in 𝓝 (1:ℝ), HasDerivAt g (v y) y)
    (hv : ContinuousAt v 1) (hne : v 1 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ {a b c e d : ℝ},
      a ∈ Ioo (1-r) (1+r) → b ∈ Ioo (1-r) (1+r) →
      c ∈ Ioo (1-r) (1+r) → e ∈ Ioo (1-r) (1+r) →
      0 < d → d ≤ c-a → d ≤ e-b →
      d/2 ≤ ((normalizedMean g c e - normalizedMean g a b)/(v 1)).re := by
  let F (y : ℝ) := (g y / v 1).re
  let V (y : ℝ) := (v y / v 1).re
  have hV : ContinuousAt V 1 := Complex.continuous_re.continuousAt.comp (hv.div_const _)
  have hV1 : V 1 = 1 := by simp [V,hne]
  have hhalf : ∀ᶠ y in 𝓝 (1:ℝ), 1/2 < V y :=
    hV.eventually (lt_mem_nhds (by rw [hV1]; norm_num))
  obtain ⟨r,hr,hrange⟩ := Metric.eventually_nhds_iff.mp (hd.and hhalf)
  refine ⟨r,hr,?_⟩
  let I := Ioo (1-r) (1+r)
  have hloc {y : ℝ} (hy : y ∈ I) : HasDerivAt g (v y) y ∧ 1/2 < V y := by
    apply hrange
    rw [Real.dist_eq,abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hDF {y : ℝ} (hy : y ∈ I) : HasDerivAt F (V y) y :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt y ((hloc hy).1.div_const (v 1))
  have hcont : ContinuousOn g I := fun y hy => (hloc hy).1.continuousAt.continuousWithinAt
  have hFcont : ContinuousOn F I := fun y hy => (hDF hy).continuousAt.continuousWithinAt
  intro a b c e d ha hb hc he hdpos hca heb
  have hint {p q : ℝ} (hp : p ∈ I) (hq : q ∈ I) :
      IntegrableOn (fun s => g (segment p q s)) (Ioc (0:ℝ) 1) := by
    exact (hcont.comp (segment_cont p q).continuousOn (fun _ hs => segment_mem hp hq hs)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiA := hint ha hb
  have hiC := hint hc he
  let D (s : ℝ) := (g (segment c e s) - g (segment a b s))/v 1
  have hiD : IntegrableOn D (Ioc (0:ℝ) 1) := (hiC.sub hiA).div_const _
  have hproj : IntegrableOn (fun s => (D s).re) (Ioc (0:ℝ) 1) :=
    Complex.reCLM.integrable_comp hiD
  have hmean : ((normalizedMean g c e-normalizedMean g a b)/v 1).re =
      ∫ s in Ioc (0:ℝ) 1, (D s).re := by
    rw [show (∫ s in Ioc (0:ℝ) 1, (D s).re) = (∫ s in Ioc (0:ℝ) 1, D s).re from integral_re hiD]
    simp only [D, normalizedMean,intervalIntegral.integral_of_le zero_le_one,integral_div,integral_sub hiC hiA]
  rw [hmean]
  calc
    _ = ∫ _s in Ioc (0:ℝ) 1, d/2 := by simp
    _ ≤ _ := by
      apply setIntegral_mono_on (integrableOn_const measure_Ioc_lt_top.ne) hproj measurableSet_Ioc
      intro s hs
      have hss : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2⟩
      let x := segment a b s
      let y := segment c e s
      have hx : x ∈ I := segment_mem ha hb hss
      have hy : y ∈ I := segment_mem hc he hss
      have hgap : d ≤ y-x := by
        dsimp [x,y,segment]
        nlinarith [mul_le_mul_of_nonneg_left hca (sub_nonneg.mpr hs.2),
          mul_le_mul_of_nonneg_left heb hs.1.le]
      have hxy : x < y := by linarith
      have hsub {t : ℝ} (ht : t ∈ Icc x y) : t ∈ I := ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
      obtain ⟨t,ht,htv⟩ := exists_hasDerivAt_eq_slope F V hxy (hFcont.mono (fun _ => hsub))
        (fun _ ht => hDF (hsub ⟨ht.1.le,ht.2.le⟩))
      have hslope := (hloc (hsub ⟨ht.1.le,ht.2.le⟩)).2
      have hm := (eq_div_iff (sub_ne_zero.mpr hxy.ne')).mp htv
      have hmul := mul_le_mul_of_nonneg_right hslope.le (sub_nonneg.mpr hxy.le)
      change d/2 ≤ ((g y-g x)/v 1).re
      rw [sub_div,Complex.sub_re]
      change d/2 ≤ F y-F x
      linarith

def logMode (rho : ℂ) (y : ℝ) : ℂ := Complex.exp ((rho-1)*(Real.log y : ℂ))

theorem logMode_mean_contrast (rho : ℂ) (hρ : rho ≠ 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ {a b c e d : ℝ},
      a ∈ Ioo (1-r) (1+r) → b ∈ Ioo (1-r) (1+r) →
      c ∈ Ioo (1-r) (1+r) → e ∈ Ioo (1-r) (1+r) →
      0 < d → d ≤ c-a → d ≤ e-b →
      d/2 ≤ ((normalizedMean (logMode rho) c e - normalizedMean (logMode rho) a b)/(rho-1)).re := by
  let v (y : ℝ) := logMode rho y * ((rho-1)*(y⁻¹:ℝ))
  have h1 : v 1 = rho-1 := by simp [v,logMode]
  have hd : ∀ᶠ y in 𝓝 (1:ℝ), HasDerivAt (logMode rho) (v y) y := by
    filter_upwards [lt_mem_nhds (by norm_num : (0:ℝ)<1)] with y hy
    exact (((Real.hasDerivAt_log hy.ne').ofReal_comp).const_mul (rho-1)).cexp
  have hv : ContinuousAt v 1 := by
    dsimp [v,logMode]
    fun_prop (disch := norm_num)
  simpa only [h1] using local_mean_contrast hd hv (h1 ▸ sub_ne_zero.mpr hρ)

#print axioms local_mean_contrast
#print axioms logMode_mean_contrast
end RHConnections.LocalModeContrast
