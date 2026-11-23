import Verified
import QuantitativeMertens
import ReciprocalUniformLogStrip

noncomputable section
namespace RHConnections.FinitePerron

open MertensCriterion ArithmeticFourierInversion ReciprocalLocalComparison

theorem quantitative_mertens :
    ∃ α C : ℝ, 0<α ∧ 0≤C ∧ ∀ X : ℝ, Real.exp 1≤X →
       ‖mertens X‖ ≤ C*X*Real.exp (-α*Real.sqrt (Real.log X)) := by
  obtain ⟨d,D,hd,hD,_,hb⟩ := reciprocal_log_region_subpower (by norm_num : (0:ℝ) < 1/4)
  exact quantitative_mertens_of_log_reciprocal d D hd hD hb

theorem quantitative_natural_mertens :
    ∃ α C : ℝ, 0<α ∧ 0≤C ∧ ∀ n : ℕ, Real.exp 1≤(n:ℝ) →
       |M n| ≤ C*(n:ℝ)*Real.exp (-α*Real.sqrt (Real.log (n:ℝ))) := by
  obtain ⟨α,C,hα,hC,h⟩ := quantitative_mertens
  exact ⟨α,C,hα,hC,fun n hn => by
    simpa [mertens_eq_natural_M,Complex.norm_real,Real.norm_eq_abs] using h (n:ℝ) hn⟩

end RHConnections.FinitePerron
