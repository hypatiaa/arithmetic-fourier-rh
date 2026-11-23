import Verified
import Mathlib.Analysis.Analytic.Order

namespace RHConnections.PoleCompensation

theorem no_finite_zero_of_logDerivative {f g : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (horder : analyticOrderAt f x ≠ ⊤)
    (heq : deriv f =ᶠ[nhds x] (fun s => g s * f s)) : f x ≠ 0 := by
  intro hz
  have he : analyticOrderAt (deriv f) x =
      analyticOrderAt g x + analyticOrderAt f x :=
    (analyticOrderAt_congr heq).trans (analyticOrderAt_mul hg hf)
  have hge : analyticOrderAt f x ≤ analyticOrderAt (deriv f) x := by
    rw [he]
    exact le_add_of_nonneg_left (by positivity)
  let n := analyticOrderNatAt f x
  have hn : (n : ℕ∞) = analyticOrderAt f x := Nat.cast_analyticOrderNatAt horder
  have hh : (n : ℕ∞) ≤ analyticOrderAt (deriv f) x := hn.trans_le hge
  have ht := (analyticOrderAt_deriv_ge_iff hf hz).mp hh
  rw [← hn, ← Nat.cast_add_one] at ht
  exact (Nat.not_succ_le_self n) (by exact_mod_cast ht)

theorem no_zero_of_logDerivative_extension {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hbase : f s₀ ≠ 0)
    (hagree : deriv f =ᶠ[nhds s₀] (fun s => g s * f s)) :
    ∀ x ∈ U, f x ≠ 0 := by
  have hEq : Set.EqOn (deriv f) (fun s => g s * f s) U :=
    hf.deriv.eqOn_of_preconnected_of_eventuallyEq (hg.mul hf) hconn hs₀ hagree
  have ho : analyticOrderAt f s₀ ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hbase)]
    exact WithTop.zero_ne_top
  intro x hx
  exact no_finite_zero_of_logDerivative (hf x hx) (hg x hx)
    (hf.analyticOrderAt_ne_top_of_isPreconnected hconn hs₀ hx ho)
    (Filter.Eventually.mono (hU.mem_nhds hx) (fun s hs => hEq hs))

end RHConnections.PoleCompensation
