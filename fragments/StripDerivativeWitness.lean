import Verified
import Mathlib.Analysis.Complex.Liouville

open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHConnections.StripEvaluationWitness

def derivativeMass (k n : ℕ) (lam : ℂ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, ‖iteratedDeriv k (witness n lam) (⟨x,y⟩:ℂ)‖^2

theorem derivativeMass_bound {a : ℝ} {lam : ℂ} (hgap : a < lam.re) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (x : ℝ), |x| ≤ a →
      Integrable (fun y : ℝ => ‖iteratedDeriv k (witness n lam) (⟨x,y⟩:ℂ)‖^2) ∧
      derivativeMass k n lam x ≤ K * Real.exp (-(lam.re-a)*(n:ℝ)) := by
  let r := (lam.re-a)/2
  let b := a+r+|lam.re|
  let C := (k.factorial:ℝ)/r^k * Real.exp (b^2+r^2)
  let g (y : ℝ) := Real.exp (-(y-lam.im)^2)
  have hr : 0 < r := by dsimp [r]; linarith
  have hg : Integrable g := by
    simpa only [g,sub_eq_add_neg,neg_one_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : 0 < (1:ℝ))).comp_add_right (-lam.im)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C^2 * ∫ y : ℝ, g y, mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => (Real.exp_pos _).le),?_⟩
  intro n x hx
  let d := Real.exp (-(lam.re-a)*(n:ℝ))
  have hd : 0 ≤ d := (Real.exp_pos _).le
  have hpoint (y : ℝ) :
      ‖iteratedDeriv k (witness n lam) (⟨x,y⟩:ℂ)‖^2 ≤ (C^2*d)*g y := by
    let M := Real.exp (-(n:ℝ)*r + (b^2+r^2) - (y-lam.im)^2/2)
    have hcircle (z : ℂ) (hz : z ∈ Metric.sphere (⟨x,y⟩:ℂ) r) : ‖witness n lam z‖ ≤ M := by
      have ht : ‖z-(⟨x,y⟩:ℂ)‖ = r := by simpa only [Metric.mem_sphere,dist_eq_norm] using hz
      have hu : |z.re-x| ≤ r := by
        simpa only [Complex.sub_re,ht] using Complex.abs_re_le_norm (z-(⟨x,y⟩:ℂ))
      have hv : |z.im-y| ≤ r := by
        simpa only [Complex.sub_im,ht] using Complex.abs_im_le_norm (z-(⟨x,y⟩:ℂ))
      have hxr : z.re-lam.re ≤ -r := by
        dsimp only [r] at hu ⊢
        linarith [(le_abs_self (z.re-x)).trans hu,(le_abs_self x).trans hx]
      have hdx : |z.re-lam.re| ≤ b := by
        change |z.re-lam.re| ≤ a+r+|lam.re|
        rw [abs_le] at hu hx ⊢
        constructor <;> linarith [le_abs_self lam.re,neg_le_abs lam.re]
      have hsx := pow_le_pow_left₀ (abs_nonneg _) hdx 2
      have hsy := pow_le_pow_left₀ (abs_nonneg _) hv 2
      simp only [sq_abs] at hsx hsy
      have hny := sq_nonneg ((y-lam.im)+2*(z.im-y))
      have hn := mul_le_mul_of_nonneg_left hxr (Nat.cast_nonneg (α := ℝ) n)
      rw [witness, Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [M,Complex.add_re,pow_two,Complex.mul_re,Complex.sub_re,Complex.sub_im,
        Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at *
      nlinarith
    have hk := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
      (witness_entire n lam).diffContOnCl hcircle
    apply (pow_le_pow_left₀ (norm_nonneg _) hk 2).trans_eq
    change ((k.factorial:ℝ)*M/r^k)^2 = (C^2*d)*g y
    have he : M^2 = (Real.exp (b^2+r^2))^2*d*g y := by
      simp only [M,d,g,pow_two,← Real.exp_add]
      congr 1
      dsimp only [r]
      ring
    calc
      _ = ((k.factorial:ℝ)/r^k)^2*M^2 := by ring
      _ = _ := by rw [he]; dsimp only [C]; ring
  have hmeas : Continuous (fun y : ℝ => ‖iteratedDeriv k (witness n lam) (⟨x,y⟩:ℂ)‖^2) := by
    have hc : ContDiff ℂ k (witness n lam) := by unfold witness; fun_prop
    have hl (y : ℝ) : (⟨x,y⟩:ℂ) = (x:ℂ)+(y:ℂ)*Complex.I := by
      apply Complex.ext <;> simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
    have hline : Continuous (fun y : ℝ => (⟨x,y⟩:ℂ)) := by
      simp_rw [hl]
      fun_prop
    exact ((hc.continuous_iteratedDeriv' k).comp hline).norm.pow _
  have hmajor := hg.const_mul (C^2*d)
  have hi : Integrable (fun y : ℝ => ‖iteratedDeriv k (witness n lam) (⟨x,y⟩:ℂ)‖^2) := by
    apply hmajor.mono' hmeas.aestronglyMeasurable
    exact ae_of_all _ fun y => by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hpoint y
  refine ⟨hi,(integral_mono hi hmajor hpoint).trans_eq ?_⟩
  rw [integral_const_mul]
  dsimp only [d]
  ring

theorem derivativeMass_uniformly_small {a : ℝ} {lam : ℂ} (hgap : a < lam.re) (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, |x| ≤ a →
      derivativeMass k n lam x < ε := by
  obtain ⟨K,_,hK⟩ := derivativeMass_bound hgap k
  have ht : Tendsto (fun n : ℕ => -(lam.re-a)*(n:ℝ)) atTop atBot :=
    tendsto_const_nhds.neg_mul_atTop (by linarith : -(lam.re-a) < 0) tendsto_natCast_atTop_atTop
  have he := (Real.tendsto_exp_atBot.comp ht).const_mul K
  rw [mul_zero] at he
  intro ε hε
  filter_upwards [he.eventually_lt_const hε] with n hn
  exact fun x hx => ((hK n x hx).2).trans_lt hn

theorem finite_derivativeMass_uniformly_small {a : ℝ} {lam : ℂ} (hgap : a < lam.re)
    (orders : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k ∈ orders, ∀ x : ℝ, |x| ≤ a → derivativeMass k n lam x < ε :=
  (eventually_all_finset orders).mpr fun k _ => derivativeMass_uniformly_small hgap k ε hε

#print axioms derivativeMass_bound
#print axioms finite_derivativeMass_uniformly_small
end RHConnections.StripEvaluationWitness
