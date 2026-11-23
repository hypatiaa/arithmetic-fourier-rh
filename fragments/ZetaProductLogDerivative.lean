import Verified
import Mathlib.Analysis.Calculus.LogDeriv

open Filter
noncomputable section
namespace RHConnections.CanonicalFactor
open SpectralTail RelativeResolvent

theorem zetaFactor_logDerivative (r : RepeatedZetaZero) (s : ℂ) (hs : s ≠ r.1.val) :
    logDeriv (zetaFactor r) s = (s-r.1.val)⁻¹ + (r.1.val)⁻¹ := by
  obtain ⟨δ, hδ, hd⟩ := zeta_zero_norm_lower
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
  have hEq : zetaFactor r = g*h := rfl
  rw [hEq, logDeriv_mul (f := g) (g := h) s hg0 (Complex.exp_ne_zero _) hg.differentiableAt hh.differentiableAt,
    logDeriv_apply, logDeriv_apply, hg.deriv, hh.deriv]
  dsimp [g,h] at *
  field_simp [hr, hs, sub_ne_zero.mpr hs, Complex.exp_ne_zero]
  <;> ring

theorem zetaCanonicalProduct_logDerivative_limit {s : ℂ}
    (hs : ∀ r : NontrivialZetaZero, s ≠ r.val) :
    Tendsto (fun S : Finset RepeatedZetaZero =>
      ∑ r ∈ S, ((s-r.1.val)⁻¹ + (r.1.val)⁻¹)) atTop
      (nhds (logDeriv zetaCanonicalProduct s)) := by
  have h := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    zetaCanonicalProduct_locally_uniform
  let F := fun S : Finset RepeatedZetaZero => fun w : ℂ => ∏ r ∈ S, zetaFactor r w
  have hF : ∀ᶠ S in (atTop : Filter (Finset RepeatedZetaZero)),
      DifferentiableOn ℂ (F S) Set.univ := .of_forall fun S => by
    simpa only [F, Finset.prod_fn] using (DifferentiableOn.finsetProd (u := S) (f := zetaFactor) (s := Set.univ)
      (fun r _ => (zetaFactor_differentiable r).differentiableOn (s := Set.univ)))
  have hl : TendstoLocallyUniformlyOn F zetaCanonicalProduct atTop Set.univ := h
  have hvalue := hl.tendsto_at (Set.mem_univ s)
  have hderiv := (hl.deriv hF isOpen_univ).tendsto_at (Set.mem_univ s)
  have hld := hderiv.div hvalue (zetaCanonicalProduct_ne_zero hs)
  apply hld.congr'
  filter_upwards with S
  have hfin := logDeriv_fun_prod (s := S) (f := zetaFactor)
    (fun r _ h => hs r.1 ((zetaFactor_eq_zero_iff r s).mp h))
    (fun r _ => zetaFactor_differentiable r s)
  change logDeriv (F S) s = _
  rw [hfin]
  exact Finset.sum_congr rfl (fun r _ => zetaFactor_logDerivative r s (hs r.1))

theorem zetaCanonicalProduct_relative_logDerivative {s s₀ : ℂ}
    (hs : ∀ r : NontrivialZetaZero, s ≠ r.val)
    (hs₀ : ∀ r : NontrivialZetaZero, s₀ ≠ r.val) :
    HasSum (fun r : RepeatedZetaZero => relative s s₀ r.1.val)
      (logDeriv zetaCanonicalProduct s - logDeriv zetaCanonicalProduct s₀) := by
  have h := (zetaCanonicalProduct_logDerivative_limit hs).sub
    (zetaCanonicalProduct_logDerivative_limit hs₀)
  apply h.congr'
  filter_upwards with S
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ => by unfold relative; ring

end RHConnections.CanonicalFactor
