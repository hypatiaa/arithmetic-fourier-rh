import Verified
import Mathlib.NumberTheory.Chebyshev

open MeasureTheory Set Filter
noncomputable section
namespace RHConnections.SmoothedPrimeLimit
open ChebyshevCriterion

theorem translate_compact {E : Type*} [Zero E] [TopologicalSpace E] {f : ℝ → E}
    (hf : HasCompactSupport f) (T : ℝ) : HasCompactSupport (fun x => f (x-T)) := by
  let S := (fun x : ℝ => x+T) '' tsupport f
  have hcont : Continuous (fun x : ℝ => x+T) := by fun_prop
  have hS : IsCompact S := hf.isCompact.image hcont
  refine HasCompactSupport.intro hS ?_
  intro x hx
  by_contra h
  exact hx ⟨x-T,subset_tsupport f h,by ring⟩

theorem smoothed_prime_limit_whole {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Tendsto (fun T : ℝ => Complex.exp (-(T:ℂ)) * ∑' n : ℕ, mangoldtCoeff n*f (Real.log n-T))
      atTop (nhds (∫ x : ℝ, Complex.exp (x:ℂ)*f x)) := by
  obtain ⟨b,hb⟩ := hc.isCompact.bddBelow
  let a := 1-b
  let g := fun x => f (x-a)
  have hg : ContDiff ℝ ∞ g := hf.comp (by fun_prop)
  have hc' : HasCompactSupport g := translate_compact hc _
  have hz (x : ℝ) (hx : x ≤ 0) : g x = 0 := by
    by_contra hn
    have hh := hb (subset_tsupport f hn)
    change b ≤ x-a at hh
    dsimp [a] at hh
    linarith
  have hshift : Tendsto (fun T : ℝ => T-a) atTop atTop := by
    refine tendsto_atTop.mpr fun d => ?_
    filter_upwards [eventually_ge_atTop (d+a)] with x hx
    linarith
  have h := ((smoothed_prime_limit hg hc' hz).comp hshift).const_mul (Complex.exp (-(a:ℂ)))
  have hl : (Complex.exp (-(a:ℂ)))*(∫ x in Ioi (0:ℝ), Complex.exp (x:ℂ)*g x) =
      ∫ x : ℝ, Complex.exp (x:ℂ)*f x := by
    have he : (Ioi (0:ℝ)).indicator (fun x : ℝ => Complex.exp (x:ℂ)*g x) =
        fun x : ℝ => Complex.exp (x:ℂ)*g x := by
      funext x
      by_cases hx : x ∈ Ioi (0:ℝ)
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx,hz x (le_of_not_gt hx),mul_zero]
    rw [← integral_indicator measurableSet_Ioi,he,← integral_const_mul]
    simp only [g,← mul_assoc,← Complex.exp_add]
    have he' (x : ℝ) : -(a:ℂ)+(x:ℂ) = ((x-a:ℝ):ℂ) := by push_cast; ring
    simp_rw [he']
    exact integral_sub_right_eq_self (fun x : ℝ => Complex.exp (x:ℂ)*f x) a
  rw [hl] at h
  refine h.congr' (Eventually.of_forall fun T => ?_)
  change Complex.exp (-(a:ℂ)) *
      (Complex.exp (-((T-a:ℝ):ℂ)) * ∑' n : ℕ, mangoldtCoeff n*g (Real.log n-(T-a))) = _
  rw [← mul_assoc,← Complex.exp_add]
  have he : -(a:ℂ) + (-((T-a:ℝ):ℂ)) = -(T:ℂ) := by push_cast; ring
  rw [he]
  congr 1
  apply tsum_congr
  intro n
  unfold g
  rw [show Real.log (n:ℝ)-(T-a)-a = Real.log n-T by ring]

def realPrimeTest (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  Real.exp (-T) * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n*f (Real.log n-T)

theorem real_prime_test_limit {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Tendsto (realPrimeTest f) atTop (nhds (∫ x : ℝ, Real.exp x*f x)) := by
  let g := fun x : ℝ => (f x:ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hf
  have hcg : HasCompactSupport g := by
    apply HasCompactSupport.intro hc.isCompact
    intro x hx
    have h0 : f x = 0 := by
      by_contra hne
      exact hx (subset_tsupport f hne)
    simp [g,h0]
  have h := Complex.continuous_re.continuousAt.tendsto.comp (smoothed_prime_limit_whole hg hcg)
  have he (T : ℝ) : (Complex.exp (-(T:ℂ)) *
      ∑' n : ℕ, mangoldtCoeff n*g (Real.log n-T)).re = realPrimeTest f T := by
    rw [realPrimeTest,← Complex.ofReal_neg,← Complex.ofReal_exp]
    simp only [mangoldtCoeff,g,← Complex.ofReal_mul,← Complex.ofReal_tsum,Complex.ofReal_re]
  have hi : (∫ x : ℝ, Complex.exp (x:ℂ)*g x).re = ∫ x : ℝ, Real.exp x*f x := by
    simp only [g,← Complex.ofReal_exp,← Complex.ofReal_mul,integral_complex_ofReal,Complex.ofReal_re]
  rwa [hi,show (Complex.re ∘ fun T : ℝ =>
    Complex.exp (-(T:ℂ))* ∑' n : ℕ, mangoldtCoeff n*g (Real.log n-T)) = realPrimeTest f from funext he] at h

end RHConnections.SmoothedPrimeLimit
