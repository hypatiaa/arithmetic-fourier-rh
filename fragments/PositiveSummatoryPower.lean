import Verified

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace RHConnections.PositiveSummatory
open PositiveLaplace

variable {E : ℝ → ℝ} {G : ℂ → ℂ}

private def powerDensity (E : ℝ → ℝ) (a σ C : ℝ) (x : ℝ) : ℝ :=
  max 0 ((σ*E x*(max 1 x)^(-a)+C)/max 1 x)

private def logScale (x : ℝ) : ℝ := max 0 (Real.log x)

private def positiveTailMeasure : Measure ℝ := volume.restrict (Set.Ioi 1)

private theorem power_density_measurable (hm : Measurable E) (a σ C : ℝ) : Measurable (powerDensity E a σ C) := by
  unfold powerDensity
  have hp : Measurable (fun x : ℝ => (max 1 x)^(-a)) := by fun_prop
  exact measurable_const.max ((((hm.const_mul _).mul
    hp).add_const _).div
    (measurable_const.max measurable_id))

private theorem logScale_measurable : Measurable logScale :=
  measurable_const.max Real.measurable_log

private theorem power_density_euler_data
    (hEuler : ∀ s : ℂ, 1<s.re →
      IntegrableOn (fun x => (E x:ℂ)*(x:ℂ)^(-(s+1))) (Set.Ioi 1) ∧
      (∫ x in Set.Ioi (1:ℝ), (E x:ℂ)*(x:ℂ)^(-(s+1)))=G s/s)
    (a σ C : ℝ) (hC : ∀ x>1, 0≤σ*E x*x^(-a)+C)
    {s : ℂ} (hs : 0<s.re) (hsa : 1<(s+(a:ℂ)).re) :
    Integrable (fun x => (powerDensity E a σ C x:ℂ)*Complex.exp (-s*(logScale x:ℂ))) positiveTailMeasure ∧
    complexLaplace (powerDensity E a σ C) logScale positiveTailMeasure s =
      (σ:ℂ)*(G (s+(a:ℂ)))/(s+(a:ℂ))+(C:ℂ)/s := by
  have hpow : IntegrableOn (fun x : ℝ => (x:ℂ)^(-(s+1))) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp [Complex.add_re]; linarith) (by norm_num)
  obtain ⟨hErr,hInt⟩ := hEuler _ hsa
  have he (x : ℝ) (hx : x∈Set.Ioi (1:ℝ)) :
      (powerDensity E a σ C x:ℂ)*Complex.exp (-s*(logScale x:ℂ)) =
      (σ:ℂ)*((E x:ℂ)*(x:ℂ)^(-(s+(a:ℂ)+1)))+(C:ℂ)*(x:ℂ)^(-(s+1)) := by
    have hx1 : 1<x := hx
    have hx0 : 0<x := by linarith
    have hxC : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    have hlog : Complex.exp (-s*(logScale x:ℂ))=(x:ℂ)^(-s) := by
      rw [logScale,max_eq_right (Real.log_nonneg hx1.le),Complex.ofReal_log hx0.le,
        Complex.cpow_def_of_ne_zero hxC,mul_comm]
    have hdiv : (x:ℂ)^(-s)/(x:ℂ)=(x:ℂ)^(-(s+1)) := by
      rw [div_eq_mul_inv,← Complex.cpow_neg_one,← Complex.cpow_add _ _ hxC]
      congr 1
      ring
    rw [hlog,powerDensity,max_eq_right hx1.le,max_eq_right (div_nonneg (hC x hx1) hx0.le)]
    push_cast
    rw [div_mul_eq_mul_div,mul_div_assoc,hdiv]
    have hpow_eq : ((x^(-a):ℝ):ℂ)*(x:ℂ)^(-(s+1))=(x:ℂ)^(-(s+(a:ℂ)+1)) := by
      rw [Complex.ofReal_cpow hx0.le,Complex.ofReal_neg,←Complex.cpow_add _ _ hxC]
      congr 1
      ring
    simp only [add_mul,mul_assoc,hpow_eq]
  have hnear : (fun x => (powerDensity E a σ C x:ℂ)*Complex.exp (-s*(logScale x:ℂ))) =ᵐ[positiveTailMeasure]
      (fun x => (σ:ℂ)*((E x:ℂ)*(x:ℂ)^(-(s+(a:ℂ)+1)))+(C:ℂ)*(x:ℂ)^(-(s+1))) :=
    (ae_restrict_mem measurableSet_Ioi).mono he
  have hi : IntegrableOn
      (fun x => (σ:ℂ)*((E x:ℂ)*(x:ℂ)^(-(s+(a:ℂ)+1)))+(C:ℂ)*(x:ℂ)^(-(s+1))) (Set.Ioi 1) :=
    (hErr.const_mul _).add (hpow.const_mul _)
  refine ⟨hi.congr hnear.symm,?_⟩
  unfold complexLaplace
  rw [integral_congr_ae hnear]
  unfold positiveTailMeasure
  rw [integral_add (hErr.const_mul _) (hpow.const_mul _),
    integral_const_mul,integral_const_mul,hInt,
    integral_Ioi_cpow_of_lt (by simp [Complex.add_re]; linarith : (-(s+1)).re < -1) (by norm_num)]
  simp only [Complex.ofReal_one,Complex.one_cpow,
    show -(s+1)+1= -s by ring,div_neg,neg_div,neg_neg]
  ring

private theorem power_real_euler_start
    (hEuler : ∀ s : ℂ, 1<s.re →
      IntegrableOn (fun x => (E x:ℂ)*(x:ℂ)^(-(s+1))) (Set.Ioi 1) ∧
      (∫ x in Set.Ioi (1:ℝ), (E x:ℂ)*(x:ℂ)^(-(s+1)))=G s/s)
    (a σ C : ℝ)
    (hC : ∀ x>1, 0≤σ*E x*x^(-a)+C) (ha : 0≤a) :
    Integrable (fun x => powerDensity E a σ C x * Real.exp (-(2:ℝ)*logScale x)) positiveTailMeasure := by
  have h := (power_density_euler_data hEuler a σ C hC (s := 2) (by norm_num) (by simp only [Complex.add_re,Complex.ofReal_re]; norm_num; linarith)).1.norm
  apply h.congr (ae_of_all _ (fun x => ?_))
  have hp : 0≤powerDensity E a σ C x := le_max_left _ _
  simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hp,
    Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  norm_num

private theorem power_real_laplace_eq_re (E : ℝ → ℝ) (a σ C b : ℝ) :
    (complexLaplace (powerDensity E a σ C) logScale positiveTailMeasure (b:ℂ)).re =
      laplace (powerDensity E a σ C) logScale positiveTailMeasure b := by
  unfold complexLaplace laplace
  simp only [← Complex.ofReal_neg,← Complex.ofReal_mul,← Complex.ofReal_exp,
    integral_complex_ofReal,Complex.ofReal_re]

theorem signed_power_mellin_extension (hm : Measurable E)
    (hG : ∀ b : ℝ, 0<b → AnalyticAt ℂ G (b:ℂ))
    (hEuler : ∀ s : ℂ, 1<s.re →
      IntegrableOn (fun x => (E x:ℂ)*(x:ℂ)^(-(s+1))) (Set.Ioi 1) ∧
      (∫ x in Set.Ioi (1:ℝ), (E x:ℂ)*(x:ℂ)^(-(s+1)))=G s/s)
    {a σ C : ℝ} (ha : 0≤a) (ha1 : a<1) (hσ : σ=1 ∨ σ= -1)
    (hC : ∀ x>1, 0≤σ*E x*x^(-a)+C) :
    ∃ A : ℂ → ℂ, AnalyticOnNhd ℂ A {s : ℂ | a<s.re} ∧
      ∀ s : ℂ, 1<s.re → A s=G s := by
  let H := fun s : ℂ =>
    (σ:ℂ)*G (s+(a:ℂ))/(s+(a:ℂ))+(C:ℂ)/s
  let F := fun b : ℝ => (H (b:ℂ)).re
  have hH (b : ℝ) (hb : 0<b) : AnalyticAt ℂ H (b:ℂ) := by
    have hb' : 0<b+a := by linarith
    have hn : (b:ℂ)+(a:ℂ)≠0 := by exact_mod_cast hb'.ne'
    have hbz := hG (b+a) hb'
    rw [Complex.ofReal_add] at hbz
    have hc : AnalyticAt ℂ (fun z : ℂ => z+(a:ℂ)) (b:ℂ) := analyticAt_id.add analyticAt_const
    have hc' : AnalyticAt ℂ (fun z : ℂ => G (z+(a:ℂ))) (b:ℂ) :=
      hbz.comp (f := fun z : ℂ => z+(a:ℂ)) hc
    unfold H
    exact ((analyticAt_const.mul hc').div (analyticAt_id.add analyticAt_const) hn).add
      (analyticAt_const.div analyticAt_id (Complex.ofReal_ne_zero.mpr hb.ne'))
  have hF : AnalyticOnNhd ℝ F (Set.Ioi 0) := by
    intro b hb
    exact (Complex.reCLM.analyticAt _).comp
      (((hH b hb).restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt b))
  have he (b : ℝ) (hb : 2<b) :
      F b=laplace (powerDensity E a σ C) logScale positiveTailMeasure b := by
    have hb' : 1<(b:ℂ).re := by rw [Complex.ofReal_re]; linarith
    have hbs : 1<((b:ℂ)+(a:ℂ)).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
    have hE := (power_density_euler_data hEuler a σ C hC (zero_lt_one.trans hb') hbs).2
    rw [←power_real_laplace_eq_re E]
    unfold F H
    rw [hE]
  have hconv (b : ℝ) (hb : 0<b) :
      Integrable (fun x => powerDensity E a σ C x*Real.exp (-b*logScale x)) positiveTailMeasure :=
    laplace_integrable_of_positive_real_extension (power_density_measurable hm a σ C) logScale_measurable
      (fun _ => le_max_left _ _) (fun _ => le_max_left _ _) hF 2 (power_real_euler_start hEuler a σ C hC ha) he b hb
  let L := complexLaplace (powerDensity E a σ C) logScale positiveTailMeasure
  have hL : AnalyticOnNhd ℂ L {s : ℂ | 0<s.re} :=
    complex_laplace_analytic (power_density_measurable hm a σ C) logScale_measurable
      (fun _ => le_max_left _ _) (fun _ => le_max_left _ _) hconv
  let A := fun s : ℂ => (σ:ℂ)*s*(L (s-(a:ℂ))-(C:ℂ)/(s-(a:ℂ)))
  have hA : AnalyticOnNhd ℂ A {s : ℂ | a<s.re} := by
    intro s hs
    have hpos : 0<(s-(a:ℂ)).re := by rw [Complex.sub_re,Complex.ofReal_re]; exact sub_pos.mpr hs
    have hn : s-(a:ℂ)≠0 := by intro he; rw [he,Complex.zero_re] at hpos; exact (lt_irrefl _ hpos)
    have hSub : AnalyticAt ℂ (fun s : ℂ => s-(a:ℂ)) s := analyticAt_id.sub analyticAt_const
    have hComp : AnalyticAt ℂ (fun z : ℂ => L (z-(a:ℂ))) s := (hL _ hpos).comp (f := fun z : ℂ => z-(a:ℂ)) hSub
    have hDiv : AnalyticAt ℂ (fun z : ℂ => (C:ℂ)/(z-(a:ℂ))) s :=
      analyticAt_const.div hSub hn
    exact (analyticAt_const.mul analyticAt_id).mul (hComp.sub hDiv)
  have hEq (s : ℂ) (hs : 1<s.re) : A s=G s := by
    have hsA : 0<(s-(a:ℂ)).re := by simp only [Complex.sub_re,Complex.ofReal_re]; linarith
    have hs0 : s≠0 := by rintro rfl; norm_num at hs
    have hz := (power_density_euler_data hEuler a σ C hC (s := s-(a:ℂ)) hsA (by simpa using hs)).2
    unfold A L
    rw [hz,sub_add_cancel,add_sub_cancel_right]
    have hsq : (σ:ℂ)^2=1 := by rcases hσ with rfl|rfl <;> norm_num
    field_simp [hs0]
    linear_combination (G s)*hsq
  exact ⟨A,hA,hEq⟩

end RHConnections.PositiveSummatory
