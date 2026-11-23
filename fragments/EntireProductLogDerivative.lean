import Verified
import Mathlib.Analysis.Calculus.LogDeriv

open Filter
noncomputable section
namespace RHConnections.EntireCanonicalProduct.Data
open SpectralTail RelativeResolvent CanonicalFactor
variable (D : Data)

theorem factor_logDerivative (r : D.RepeatedZero) (s : ℂ) (hs : s ≠ r.1.val) :
    logDeriv (D.factor r) s = (s-r.1.val)⁻¹ + (r.1.val)⁻¹ := by
  obtain ⟨δ, hδ, hd⟩ := D.zero_norm_lower
  have hr : r.1.val ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hd r.1))
  let g := fun t : ℂ => 1-t/r.1.val
  let h := fun t : ℂ => Complex.exp (t/r.1.val)
  have hg : HasDerivAt g (-1/r.1.val) s := by
    simpa only [g, id_eq, neg_div] using ((hasDerivAt_id s).div_const r.1.val).const_sub 1
  have hh : HasDerivAt h (Complex.exp (s/r.1.val)*(1/r.1.val)) s := by
    simpa only [h, id_eq, mul_comm] using ((hasDerivAt_id s).div_const r.1.val).cexp
  have hg0 : g s ≠ 0 := by
    intro he
    have he' : s/r.1.val = 1 := (sub_eq_zero.mp he).symm
    exact hs (by simpa using (div_eq_iff hr).mp he')
  have hEq : D.factor r = g*h := rfl
  rw [hEq, logDeriv_mul (f := g) (g := h) s hg0 (Complex.exp_ne_zero _) hg.differentiableAt hh.differentiableAt,
    logDeriv_apply, logDeriv_apply, hg.deriv, hh.deriv]
  dsimp [g,h] at *
  field_simp [hr, hs, sub_ne_zero.mpr hs, Complex.exp_ne_zero]
  <;> ring

theorem product_logDerivative_limit {s : ℂ}
    (hs : ∀ r : D.Zero, s ≠ r.val) :
    Tendsto (fun S : Finset D.RepeatedZero =>
      ∑ r ∈ S, ((s-r.1.val)⁻¹ + (r.1.val)⁻¹)) atTop
      (nhds (logDeriv D.product s)) := by
  have h := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    D.product_locally_uniform
  let F := fun S : Finset D.RepeatedZero => fun w : ℂ => ∏ r ∈ S, D.factor r w
  have hF : ∀ᶠ S in (atTop : Filter (Finset D.RepeatedZero)),
      DifferentiableOn ℂ (F S) Set.univ := .of_forall fun S => by
    simpa only [F, Finset.prod_fn] using (DifferentiableOn.finsetProd (u := S) (f := D.factor) (s := Set.univ)
      (fun r _ => (D.factor_differentiable r).differentiableOn (s := Set.univ)))
  have hl : TendstoLocallyUniformlyOn F D.product atTop Set.univ := h
  have hvalue := hl.tendsto_at (Set.mem_univ s)
  have hderiv := (hl.deriv hF isOpen_univ).tendsto_at (Set.mem_univ s)
  have hld := hderiv.div hvalue (D.product_ne_zero hs)
  apply hld.congr'
  filter_upwards with S
  have hfin := logDeriv_fun_prod (s := S) (f := D.factor)
    (fun r _ h => hs r.1 ((D.factor_eq_zero_iff r s).mp h))
    (fun r _ => D.factor_differentiable r s)
  change logDeriv (F S) s = _
  rw [hfin]
  exact Finset.sum_congr rfl (fun r _ => D.factor_logDerivative r s (hs r.1))

theorem product_relative_logDerivative {s s₀ : ℂ}
    (hs : ∀ r : D.Zero, s ≠ r.val)
    (hs₀ : ∀ r : D.Zero, s₀ ≠ r.val) :
    HasSum (fun r : D.RepeatedZero => relative s s₀ r.1.val)
      (logDeriv D.product s - logDeriv D.product s₀) := by
  have h := (D.product_logDerivative_limit hs).sub
    (D.product_logDerivative_limit hs₀)
  apply h.congr'
  filter_upwards with S
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ => by unfold relative; ring

def HadamardFactorization : Prop :=
  ∃ B : ℂ, ∀ s : ℂ, D.F s = Complex.exp (B*s) * D.product s

theorem logDerivative_of_hadamard {B : ℂ}
    (hB : ∀ s : ℂ, D.F s = Complex.exp (B*s) * D.product s)
    {s : ℂ} (hs : ∀ r : D.Zero, s ≠ r.val) :
    logDeriv D.F s = B + logDeriv D.product s := by
  have he : D.F = fun t : ℂ => Complex.exp (B*t)*D.product t :=
    funext hB
  have hd : HasDerivAt (fun t : ℂ => Complex.exp (B*t))
      (Complex.exp (B*s)*B) s := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul B).cexp
  rw [he, logDeriv_fun_mul (f := fun t : ℂ => Complex.exp (B*t)) (g := D.product)
    s (Complex.exp_ne_zero _) (D.product_ne_zero hs)
    hd.differentiableAt (D.product_entire s (Set.mem_univ s)).differentiableAt,
    logDeriv_apply (fun t : ℂ => Complex.exp (B*t)), hd.deriv]
  rw [mul_comm (Complex.exp (B*s)) B, mul_div_cancel_right₀ _ (Complex.exp_ne_zero _)]

theorem relative_logDerivative (h : D.HadamardFactorization)
    {s s₀ : ℂ} (hs : ∀ r : D.Zero, s ≠ r.val)
    (hs₀ : ∀ r : D.Zero, s₀ ≠ r.val) :
    HasSum (fun r : D.RepeatedZero => relative s s₀ r.1.val)
      (logDeriv D.F s - logDeriv D.F s₀) := by
  obtain ⟨B,hB⟩ := h
  rw [D.logDerivative_of_hadamard hB hs, D.logDerivative_of_hadamard hB hs₀]
  simpa using D.product_relative_logDerivative hs hs₀

end RHConnections.EntireCanonicalProduct.Data
