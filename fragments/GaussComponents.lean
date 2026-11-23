import Mathlib.NumberTheory.GaussSum

noncomputable section
namespace RHConnections.GaussComponents
variable {F : Type*} [Field F] [Fintype F]

theorem nontrivial_character_product (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : AddChar.IsPrimitive ψ) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card F : ℂ) := by
  exact gaussSum_mul_gaussSum_eq_card hχ hψ

theorem trivial_character_value (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    gaussSum (1 : MulChar F ℂ) ψ = -1 := by
  exact gaussSum_one_left hψ

#print axioms nontrivial_character_product
#print axioms trivial_character_value
end RHConnections.GaussComponents
