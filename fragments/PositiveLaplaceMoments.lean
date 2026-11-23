import Verified

open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace RHConnections.PositiveLaplace

variable {α : Type*} [MeasurableSpace α] {measure : Measure α}

private def momentTerm (f Y : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  f x * (Y x)^n / (n.factorial:ℝ)

private def moment (f Y : α → ℝ) (n : ℕ) : ℝ := ∫ x, momentTerm f Y n x ∂measure

private theorem momentTerm_measurable {f Y : α → ℝ}
    (hf : Measurable f) (hY : Measurable Y) (n : ℕ) :
    Measurable (momentTerm f Y n) := by
  unfold momentTerm
  fun_prop

omit [MeasurableSpace α] in
private theorem momentTerm_nonneg {f Y : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hY : ∀ x, 0 ≤ Y x) (n : ℕ) (x : α) :
    0 ≤ momentTerm f Y n x := by
  exact div_nonneg (mul_nonneg (hf x) (pow_nonneg (hY x) _)) (Nat.cast_nonneg _)

omit [MeasurableSpace α] in
private theorem pointwise_expansion (f Y : α → ℝ) (t : ℝ) (x : α) :
    HasSum (fun n => momentTerm f Y n x * t^n) (f x*Real.exp (t*Y x)) := by
  rw [Real.exp_eq_exp_ℝ]
  convert (NormedSpace.expSeries_div_hasSum_exp (t*Y x)).mul_left (f x) using 1
  ext n
  simp [momentTerm,mul_pow]
  ring

private theorem momentTerm_integrable {f Y : α → ℝ} {r : ℝ} (hr : 0<r)
    (hf : Measurable f) (hY : Measurable Y) (hf0 : ∀ x, 0 ≤ f x) (hY0 : ∀ x, 0 ≤ Y x)
    (hi : Integrable (fun x => f x*Real.exp (r*Y x)) measure) (n : ℕ) :
    Integrable (momentTerm f Y n) measure := by
  have h := hi.div_const (r^n)
  refine h.mono' (momentTerm_measurable hf hY n).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (momentTerm_nonneg hf0 hY0 n x)]
  apply (le_div_iff₀ (pow_pos hr n)).mpr
  rw [← (pointwise_expansion f Y r x).tsum_eq]
  exact Summable.le_tsum (pointwise_expansion f Y r x).summable n
    (fun k _ => mul_nonneg (momentTerm_nonneg hf0 hY0 k x) (pow_nonneg hr.le k))

private theorem moment_hasSum_of_integrable {f Y : α → ℝ} {r t : ℝ}
    (hf : Measurable f) (hY : Measurable Y) (hf0 : ∀ x, 0 ≤ f x) (hY0 : ∀ x, 0 ≤ Y x)
    (hi : Integrable (fun x => f x*Real.exp (r*Y x)) measure) (ht : |t| ≤ r) :
    HasSum (fun n => moment (measure := measure) f Y n * t^n) (∫ x, f x*Real.exp (t*Y x) ∂measure) := by
  simp only [moment,← integral_mul_const]
  apply hasSum_integral_of_dominated_convergence (fun n x => momentTerm f Y n x * r^n)
  · exact fun n => ((momentTerm_measurable hf hY n).mul_const _).aestronglyMeasurable
  · intro n
    filter_upwards with x
    simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg (momentTerm_nonneg hf0 hY0 n x)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ht _) (momentTerm_nonneg hf0 hY0 n x)
  · exact ae_of_all _ (fun x => (pointwise_expansion f Y r x).summable)
  · simpa only [(show (fun x => ∑' n, momentTerm f Y n x * r^n) =
        (fun x => f x*Real.exp (r*Y x)) from funext fun x => (pointwise_expansion f Y r x).tsum_eq)]
      using hi
  · exact ae_of_all _ (pointwise_expansion f Y t)

theorem integrable_exp_of_summable_moments {f Y : α → ℝ} {r t : ℝ} (hr : 0<r) (ht : 0≤t)
    (hf : Measurable f) (hY : Measurable Y) (hf0 : ∀ x, 0 ≤ f x) (hY0 : ∀ x, 0 ≤ Y x)
    (hi : Integrable (fun x => f x*Real.exp (r*Y x)) measure)
    (hs : Summable (fun n => moment (measure := measure) f Y n * t^n)) :
    Integrable (fun x => f x*Real.exp (t*Y x)) measure := by
  have nonneg (n : ℕ) (x : α) : 0 ≤ momentTerm f Y n x * t^n :=
    mul_nonneg (momentTerm_nonneg hf0 hY0 n x) (pow_nonneg ht _)
  have hm (n : ℕ) : Integrable (fun x => momentTerm f Y n x*t^n) measure :=
    (momentTerm_integrable hr hf hY hf0 hY0 hi n).mul_const _
  refine ⟨(hf.mul (Real.continuous_exp.measurable.comp (hY.const_mul _))).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le))).mpr ?_⟩
  calc
    _ = ∫⁻ x, ∑' n, ENNReal.ofReal (momentTerm f Y n x*t^n) ∂measure := by
      apply lintegral_congr
      intro x
      rw [← (pointwise_expansion f Y t x).tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg (fun n => nonneg n x)
        (pointwise_expansion f Y t x).summable
    _ = ∑' n, ENNReal.ofReal (moment (measure := measure) f Y n * t^n) := by
      rw [lintegral_tsum]
      · congr 1
        ext n
        rw [← ofReal_integral_eq_lintegral_ofReal (hm n) (ae_of_all _ (nonneg n)),
          integral_mul_const,moment]
      · exact fun n => (((momentTerm_measurable hf hY n).mul_const _).ennreal_ofReal).aemeasurable
    _ = ENNReal.ofReal (∑' n, moment (measure := measure) f Y n * t^n) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n =>
        mul_nonneg (integral_nonneg (momentTerm_nonneg hf0 hY0 n)) (pow_nonneg ht _)) hs).symm
    _ < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top

def laplace (f Y : α → ℝ) (measure : Measure α) (s : ℝ) : ℝ :=
  ∫ x, f x * Real.exp (-s * Y x) ∂measure

private def tilted (f Y : α → ℝ) (b : ℝ) (x : α) : ℝ :=
  f x * Real.exp (-b * Y x)

private theorem tilted_measurable {f Y : α → ℝ} (hf : Measurable f) (hY : Measurable Y)
    (b : ℝ) : Measurable (tilted f Y b) := by
  unfold tilted
  fun_prop

omit [MeasurableSpace α] in
private theorem tilted_nonneg {f Y : α → ℝ} (hf : ∀ x, 0 ≤ f x) (b : ℝ) (x : α) :
    0 ≤ tilted f Y b x := mul_nonneg (hf x) (Real.exp_pos _).le

omit [MeasurableSpace α] in
private theorem tilted_exp (f Y : α → ℝ) (b t : ℝ) (x : α) :
    tilted f Y b x * Real.exp (t*Y x) = tilted f Y (b-t) x := by
  simp only [tilted,mul_assoc,← Real.exp_add]
  congr 2
  ring

private theorem laplace_series_on_ball {f Y : α → ℝ} {b : ℝ} {r : ℝ≥0} (hr : 0<r)
    (hf : Measurable f) (hY : Measurable Y) (hf0 : ∀ x, 0 ≤ f x) (hY0 : ∀ x, 0 ≤ Y x)
    (hi : Integrable (tilted f Y (b-r)) measure) :
    HasFPowerSeriesOnBall (laplace f Y measure)
      (.ofScalars ℝ (fun n => moment (measure := measure) (tilted f Y b) Y n * (-1)^n)) b r := by
  let g := tilted f Y b
  have hg := tilted_measurable hf hY b
  have hg0 := tilted_nonneg hf0 (Y := Y) b
  have hgI : Integrable (fun x => g x*Real.exp ((r:ℝ)*Y x)) measure := by
    simpa only [g,tilted_exp] using hi
  have hmom (y : ℝ) (hy : |y|≤r) :
      HasSum (fun n => moment (measure := measure) g Y n * (-y)^n) (laplace f Y measure (b+y)) := by
    have ht : |-y| ≤ (r:ℝ) := by simpa only [abs_neg] using hy
    have hh := moment_hasSum_of_integrable hg hY hg0 hY0 hgI ht
    change HasSum _ (∫ x, tilted f Y (b+y) x ∂measure)
    simpa only [g,tilted_exp,sub_neg_eq_add] using hh
  refine ⟨?_,ENNReal.coe_pos.mpr hr,?_⟩
  · apply FormalMultilinearSeries.le_radius_of_summable
    simp only [FormalMultilinearSeries.ofScalars_norm,Real.norm_eq_abs,abs_mul,abs_pow,abs_neg,abs_one,one_pow,mul_one]
    have hnonneg (n : ℕ) : 0 ≤ moment (measure := measure) g Y n :=
      integral_nonneg (momentTerm_nonneg hg0 hY0 n)
    simp only [g,abs_of_nonneg (hnonneg _)]
    exact (moment_hasSum_of_integrable hg hY hg0 hY0 hgI
      (le_of_eq (abs_of_nonneg (NNReal.coe_nonneg r)))).summable
  · intro y hy
    have hyr : |y| ≤ (r:ℝ) := by
      rw [Metric.mem_eball,edist_zero_right] at hy
      change (↑‖y‖₊:ℝ≥0∞) < ↑r at hy
      have hnn := ENNReal.coe_lt_coe.mp hy
      exact le_of_lt (by simpa only [coe_nnnorm,Real.norm_eq_abs] using (NNReal.coe_lt_coe.mpr hnn))
    convert hmom y hyr using 1
    ext n
    simp only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,g]
    rw [show -y = (-1:ℝ)*y by ring,mul_pow,mul_assoc]

private theorem integrable_tilted_mono {f Y : α → ℝ} {a b : ℝ}
    (hf : Measurable f) (hY : Measurable Y) (hf0 : ∀ x, 0 ≤ f x) (hY0 : ∀ x, 0 ≤ Y x)
    (ha : Integrable (tilted f Y a) measure) (hab : a ≤ b) :
    Integrable (tilted f Y b) measure := by
  refine ha.mono' (tilted_measurable hf hY b).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (tilted_nonneg hf0 b x)]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hab) (hY0 x))) (hf0 x)

private theorem hasFPowerSeries_laplace_at {f Y : α → ℝ} (b : ℝ) {r : ℝ≥0} (hr : 0<r)
    (hf : Measurable f) (hY : Measurable Y) (hf0 : ∀ x, 0 ≤ f x) (hY0 : ∀ x, 0 ≤ Y x)
    (hi : Integrable (tilted f Y (b-r)) measure) :
    AnalyticAt ℝ (laplace f Y measure) b :=
  (laplace_series_on_ball hr hf hY hf0 hY0 hi).analyticAt

private theorem small_radius {R : ℝ≥0∞} (hR : 0<R) {a : ℝ} (ha : 0<a) :
    ∃ d : ℝ, 0<d ∧ d<a ∧ ENNReal.ofReal (3*d)<R := by
  by_cases ht : R = ⊤
  · exact ⟨a/2,by linarith,by linarith, ht ▸ ENNReal.ofReal_lt_top⟩
  have htr : 0 < R.toReal := ENNReal.toReal_pos hR.ne' ht
  let d := min (a/2) (R.toReal/4)
  have hd : 0<d := lt_min (by linarith) (by linarith)
  refine ⟨d,hd,(min_le_left _ _).trans_lt (by linarith),?_⟩
  rw [← ENNReal.ofReal_toReal ht]
  exact ENNReal.ofReal_lt_ofReal_iff htr |>.mpr (by
    have hle : d ≤ R.toReal/4 := min_le_right _ _
    linarith only [hle,htr])

theorem laplace_integrable_of_positive_real_extension {f Y : α → ℝ}
    (hf : Measurable f) (hY : Measurable Y) (hf0 : ∀ x, 0 ≤ f x) (hY0 : ∀ x, 0 ≤ Y x)
    {F : ℝ → ℝ} (hF : AnalyticOnNhd ℝ F (Set.Ioi 0)) (u : ℝ)
    (hu : Integrable (fun x => f x * Real.exp (-u * Y x)) measure)
    (he : ∀ b > u, F b = laplace f Y measure b) (s : ℝ) (hs : 0<s) :
    Integrable (fun x => f x * Real.exp (-s * Y x)) measure := by
  by_contra hn
  let D : Set ℝ := {b | Integrable (tilted f Y b) measure}
  have hne : D.Nonempty := ⟨u,hu⟩
  have hlb (b : ℝ) (hb : b∈D) : s ≤ b := by
    by_contra! h
    exact hn (integrable_tilted_mono hf hY hf0 hY0 hb h.le)
  have hbd : BddBelow D := ⟨s,hlb⟩
  let a := sInf D
  have ha : 0<a := hs.trans_le (le_csInf hne hlb)
  have hlarge (b : ℝ) (hb : a<b) : Integrable (tilted f Y b) measure := by
    obtain ⟨v,hv,hvb⟩ := exists_lt_of_csInf_lt hne hb
    exact integrable_tilted_mono hf hY hf0 hY0 hv hvb.le
  have hA : AnalyticOnNhd ℝ (laplace f Y measure) (Set.Ioi a) := by
    intro b hb
    change a<b at hb
    let r : ℝ≥0 := ⟨(b-a)/2,by linarith⟩
    have hr : 0<r := NNReal.coe_pos.mp (by show 0<(b-a)/2; linarith)
    exact hasFPowerSeries_laplace_at b hr hf hY hf0 hY0
      (hlarge _ (by change a < b-(b-a)/2; linarith))
  have hu2 : max a u < max a u+1 := by linarith
  let z := max a u+1
  have hz : z ∈ Set.Ioi a := (le_max_left a u).trans_lt hu2
  have hstate : F =ᶠ[𝓝 z] laplace f Y measure := by
    filter_upwards [isOpen_Ioi.mem_nhds ((le_max_right a u).trans_lt hu2)] with b hb
    exact he b hb
  have hdent := (hF.mono (Set.Ioi_subset_Ioi ha.le)).eqOn_of_preconnected_of_eventuallyEq
    hA (convex_Ioi a).isPreconnected hz hstate
  obtain ⟨P,R,hP⟩ := hF a ha
  obtain ⟨d,hd,hda,h3d⟩ := small_radius hP.r_pos ha
  let b := a+d
  have hbr : b ∈ Set.Ioi a := by show a<a+d; linarith
  have hr₁ : ‖d‖ₑ < R := by
    rw [Real.enorm_eq_ofReal_abs,abs_of_nonneg hd.le]
    exact (ENNReal.ofReal_le_ofReal (by linarith only [hd])).trans_lt h3d
  have hr₂ : ‖(-2*d : ℝ)‖ₑ < R-‖d‖ₑ := by
    have hlt : ‖(-2*d : ℝ)‖ₑ + ‖d‖ₑ < R := by
      rw [Real.enorm_eq_ofReal_abs,Real.enorm_eq_ofReal_abs,abs_of_nonneg hd.le,
        abs_of_nonpos (show (-2*d:ℝ)≤0 by linarith),← ENNReal.ofReal_add (by linarith) hd.le]
      convert h3d using 1
      ring
    by_contra! hc
    exact (not_le_of_gt hlt) (by
      simpa only [tsub_add_cancel_of_le hr₁.le] using add_le_add_left hc ‖d‖ₑ)
  have hshift := hP.changeOrigin hr₁
  have hnearb : F =ᶠ[𝓝 b] laplace f Y measure := by
    filter_upwards [isOpen_Ioi.mem_nhds hbr] with x hx
    exact hdent hx
  let r : ℝ≥0 := ⟨d/2,by linarith⟩
  have hposr : 0<r := NNReal.coe_pos.mp (by show 0<d/2; linarith)
  have hrI : Integrable (tilted f Y (b-r)) measure := hlarge _ (by show a < (a+d)-(d/2); linarith)
  have hLocal := laplace_series_on_ball hposr hf hY hf0 hY0 hrI
  have hEq := (hshift.hasFPowerSeriesAt.congr hnearb).eq_formalMultilinearSeries hLocal.hasFPowerSeriesAt
  have hsum := hshift.hasSum (y := -2*d) ((Metric.mem_eball.mpr (by rwa [edist_zero_right])))
  rw [hEq] at hsum
  have heq (n : ℕ) : ((FormalMultilinearSeries.ofScalars ℝ
      (fun k => moment (measure := measure) (tilted f Y b) Y k * (-1)^k) n) (fun _ => -2*d)) =
      moment (measure := measure) (tilted f Y b) Y n * (2*d)^n := by
    rw [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,mul_assoc,← mul_pow]
    congr 2
    ring
  simp only [heq] at hsum
  have hi : Integrable (fun x => tilted f Y b x * Real.exp ((r:ℝ)*Y x)) measure := by
    simpa only [tilted_exp] using hrI
  have had := integrable_exp_of_summable_moments (NNReal.coe_pos.mpr hposr)
    (by linarith : 0 ≤ 2*d) (tilted_measurable hf hY b) hY (tilted_nonneg hf0 b) hY0 hi hsum.summable
  simp only [tilted_exp] at had
  have hcontra := csInf_le hbd (show b-2*d ∈ D from had)
  dsimp [b] at hcontra
  linarith only [hcontra,hd]

end RHConnections.PositiveLaplace
