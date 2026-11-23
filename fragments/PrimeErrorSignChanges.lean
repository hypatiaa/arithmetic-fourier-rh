import Verified

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace RHConnections.PrimeErrorLaplace
open PoleCompensation PositiveLaplace ArithmeticFourierShortBlocks SpectralTail

private def density (σ C : ℝ) (x : ℝ) : ℝ :=
  max 0 ((σ*realPrimeError x+C)/max 1 x)

private def logScale (x : ℝ) : ℝ := max 0 (Real.log x)

private def positiveTailMeasure : Measure ℝ := volume.restrict (Set.Ioi 1)

private theorem density_measurable (σ C : ℝ) : Measurable (density σ C) := by
  unfold density
  exact measurable_const.max (((real_prime_error_measurable.const_mul _).add_const _).div
    (measurable_const.max measurable_id))

private theorem logScale_measurable : Measurable logScale :=
  measurable_const.max Real.measurable_log

private theorem signed_error_bounded_below (σ : ℝ) (hσ : |σ|=1) (N : ℕ)
    (hN : ∀ n≥N, 0≤σ*primeRemainder n) :
    ∃ C : ℝ, 0≤C ∧ ∀ x>1, 0≤σ*realPrimeError x+C := by
  let D := Real.log 4+5
  let C := D*((N:ℝ)+1)+1
  have hD : 0≤D := by
    have h := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
    dsimp [D]
    linarith
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro x hx
  have hx0 : 0<x := by linarith
  by_cases hb : N≤⌊x⌋₊
  · have he := hN ⌊x⌋₊ hb
    have hl := sub_nonneg.mpr (Nat.floor_le hx0.le)
    have hu : x-(⌊x⌋₊:ℝ)≤1 := by linarith only [Nat.lt_floor_add_one x]
    have hσ_le : σ≤1 := (le_abs_self σ).trans_eq hσ
    have hh := (mul_le_mul_of_nonneg_right hσ_le hl).trans (by simpa using hu)
    rw [real_prime_error_fold x,real_prime_error_at_nat,mul_sub]
    have hC : 1≤C := by dsimp [C]; linarith [mul_nonneg hD (by positivity : 0≤(N:ℝ)+1)]
    linarith only [he,hh,hC]
  · have hf := Nat.lt_floor_add_one x
    have hfloor : (⌊x⌋₊:ℝ)≤(N:ℝ) := by exact_mod_cast (lt_of_not_ge hb).le
    have hbound := (real_prime_error_linear hx0.le).trans
      (mul_le_mul_of_nonneg_left (show x≤(N:ℝ)+1 by linarith only [hf,hfloor]) hD)
    have hneg : -(D*((N:ℝ)+1))≤σ*realPrimeError x := by
      have h := neg_abs_le (σ*realPrimeError x)
      rw [abs_mul,hσ,one_mul] at h
      linarith only [h,hbound]
    dsimp [C]
    linarith only [hneg]

private theorem density_euler_data (σ C : ℝ) (hC : ∀ x>1, 0≤σ*realPrimeError x+C)
    {s : ℂ} (hs : 1<s.re) :
    Integrable (fun x => (density σ C x:ℂ)*Complex.exp (-s*(logScale x:ℂ))) positiveTailMeasure ∧
    complexLaplace (density σ C) logScale positiveTailMeasure s =
      ((σ:ℂ)*(compensatedLogDerivative s-1)+(C:ℂ))/s := by
  have hpow : IntegrableOn (fun x : ℝ => (x:ℂ)^(-(s+1))) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp [Complex.add_re]; linarith) (by norm_num)
  have hErr := prime_error_weighted_integrable hs
  have he (x : ℝ) (hx : x∈Set.Ioi (1:ℝ)) :
      (density σ C x:ℂ)*Complex.exp (-s*(logScale x:ℂ)) =
      (σ:ℂ)*((realPrimeError x:ℂ)*(x:ℂ)^(-(s+1)))+(C:ℂ)*(x:ℂ)^(-(s+1)) := by
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
    rw [hlog,density,max_eq_right hx1.le,max_eq_right (div_nonneg (hC x hx1) hx0.le)]
    push_cast
    rw [div_mul_eq_mul_div,mul_div_assoc,hdiv]
    ring
  have hnear : (fun x => (density σ C x:ℂ)*Complex.exp (-s*(logScale x:ℂ))) =ᵐ[positiveTailMeasure]
      (fun x => (σ:ℂ)*((realPrimeError x:ℂ)*(x:ℂ)^(-(s+1)))+(C:ℂ)*(x:ℂ)^(-(s+1))) :=
    (ae_restrict_mem measurableSet_Ioi).mono he
  have hi : IntegrableOn
      (fun x => (σ:ℂ)*((realPrimeError x:ℂ)*(x:ℂ)^(-(s+1)))+(C:ℂ)*(x:ℂ)^(-(s+1))) (Set.Ioi 1) :=
    (hErr.const_mul _).add (hpow.const_mul _)
  refine ⟨hi.congr hnear.symm,?_⟩
  unfold complexLaplace
  rw [integral_congr_ae hnear]
  unfold positiveTailMeasure
  rw [integral_add (hErr.const_mul _) (hpow.const_mul _),
    integral_const_mul,integral_const_mul,prime_error_euler_integral hs,
    integral_Ioi_cpow_of_lt (by simp [Complex.add_re]; linarith : (-(s+1)).re < -1) (by norm_num)]
  simp only [Complex.ofReal_one,Complex.one_cpow,
    show -(s+1)+1= -s by ring,div_neg,neg_div,neg_neg]
  rw [add_div]
  ring

private theorem real_euler_start (σ C : ℝ) (hC : ∀ x>1, 0≤σ*realPrimeError x+C) :
    Integrable (fun x => density σ C x * Real.exp (-(2:ℝ)*logScale x)) positiveTailMeasure := by
  have h := (density_euler_data σ C hC (s := 2) (by norm_num)).1.norm
  apply h.congr (ae_of_all _ (fun x => ?_))
  have hp : 0≤density σ C x := le_max_left _ _
  simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hp,
    Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  norm_num

private theorem real_laplace_eq_re (σ C b : ℝ) :
    (complexLaplace (density σ C) logScale positiveTailMeasure (b:ℂ)).re =
      laplace (density σ C) logScale positiveTailMeasure b := by
  unfold complexLaplace laplace
  simp only [← Complex.ofReal_neg,← Complex.ofReal_mul,← Complex.ofReal_exp,
    integral_complex_ofReal,Complex.ofReal_re]

theorem no_eventual_signed_prime_error (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (N : ℕ) :
    ¬ ∀ n≥N, 0≤σ*primeRemainder n := by
  intro hN
  have hsabs : |σ|=1 := by rcases hσ with rfl|rfl <;> norm_num
  obtain ⟨C,_,hC⟩ := signed_error_bounded_below σ hsabs N hN
  let H := fun s : ℂ => ((σ:ℂ)*(regularizedLogDerivative s-1)+(C:ℂ))/s
  let F := fun b : ℝ => (H (b:ℂ)).re
  have hH (b : ℝ) (hb : 0<b) : AnalyticAt ℂ H (b:ℂ) := by
    unfold H
    exact (((analyticAt_const.mul ((regularizedLogDerivative_analytic
      (regularized_zeta_ne_zero_positive_real hb)).sub analyticAt_const)).add analyticAt_const).div
        analyticAt_id (Complex.ofReal_ne_zero.mpr hb.ne'))
  have hF : AnalyticOnNhd ℝ F (Set.Ioi 0) := by
    intro b hb
    exact (Complex.reCLM.analyticAt _).comp
      (((hH b hb).restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt b))
  have he (b : ℝ) (hb : 2<b) : F b=laplace (density σ C) logScale positiveTailMeasure b := by
    have hb' : 1<(b:ℂ).re := by rw [Complex.ofReal_re]; linarith
    have hb1 : (b:ℂ)≠1 := by intro hd; rw [hd,Complex.one_re] at hb'; linarith
    have hE := (density_euler_data σ C hC hb').2
    rw [← real_laplace_eq_re]
    unfold F H
    rw [hE,regularizedLogDerivative_eq hb1 (riemannZeta_ne_zero_of_one_le_re hb'.le)]
  have hconv (b : ℝ) (hb : 0<b) :
      Integrable (fun x => density σ C x * Real.exp (-b*logScale x)) positiveTailMeasure :=
    laplace_integrable_of_positive_real_extension (density_measurable σ C) logScale_measurable
      (fun _ => le_max_left _ _) (fun _ => le_max_left _ _) hF 2 (real_euler_start σ C hC) he b hb
  let L := complexLaplace (density σ C) logScale positiveTailMeasure
  have hL : AnalyticOnNhd ℂ L {s : ℂ | 0<s.re} :=
    complex_laplace_analytic (density_measurable σ C) logScale_measurable
      (fun _ => le_max_left _ _) (fun _ => le_max_left _ _) hconv
  let A := fun s : ℂ => 1+(σ:ℂ)*(s*L s-(C:ℂ))
  have hA : AnalyticOnNhd ℂ A {s : ℂ | 0<s.re} := by
    intro s hs
    exact analyticAt_const.add (analyticAt_const.mul ((analyticAt_id.mul (hL s hs)).sub analyticAt_const))
  have hEuler (s : ℂ) (hs : 1<s.re) : A s=compensatedLogDerivative s := by
    have h := (density_euler_data σ C hC hs).2
    have hs0 : s≠0 := by rintro rfl; norm_num at hs
    unfold A L
    rw [h]
    have hsq : (σ:ℂ)^2=1 := by rcases hσ with rfl|rfl <;> norm_num
    field_simp [hs0]
    linear_combination (compensatedLogDerivative s-1)*hsq
  obtain ⟨r⟩ := nontrivial_zeta_zero_nonempty
  exact zeta_zero_free_above_compensated_extension (by norm_num : (0:ℝ)<1) hA hEuler
    r.property.1.1 r.property.2

theorem chebyshev_late_signs : LatePrimeErrorSigns := by
  constructor
  · intro N
    by_contra! hn
    apply no_eventual_signed_prime_error 1 (Or.inl rfl) N
    simpa only [one_mul] using hn
  · intro N
    by_contra! hn
    apply no_eventual_signed_prime_error (-1) (Or.inr rfl) N
    simpa only [neg_one_mul,neg_nonneg] using hn

theorem unconditional_balanced_chebyshev_blocks (N : ℕ) :
    ∃ Q≥N, |blockDiscrepancy Q Q.sqrt| ≤ 3*Real.log (2+2*(Q:ℝ))+1 :=
  balanced_blocks_of_late_prime_error_signs chebyshev_late_signs N

theorem unconditional_fourth_power_block_comparisons (B N : ℕ) :
    ∃ Q ≥ N, 0<Q ∧
      |blockDiscrepancy Q Q.sqrt| ≤ 3*Real.log (2+2*(Q:ℝ))+1 ∧
      (let I := Finset.Ioc Q (Q+Q.sqrt)
       let term := fun q => (shortWeight B q-1)*ArithmeticFourierInversion.S B (Q^4/q)
       |∑ q ∈ I,term q| ≤
         (4*Real.log (2+2*(Q:ℝ))+20)*(Q:ℝ)^3+19*Real.sqrt (Q:ℝ) ∧
       (∑ q ∈ I, |term q|) ≤ 19*Real.sqrt (Q:ℝ)*(Q:ℝ)^3) := by
  obtain ⟨Q,hQ,hgood⟩ := unconditional_balanced_chebyshev_blocks (max 1 N)
  have hp : 0<Q := by omega
  exact ⟨Q,by omega,hp,hgood,fourth_power_block_comparison B Q hp hgood⟩

end RHConnections.PrimeErrorLaplace
