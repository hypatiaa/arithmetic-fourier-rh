import AstraSharpRightEndpoint

noncomputable section
namespace RHConnections.SharpRightEndpoint

theorem sharp_dyadic_X :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, Real.exp 2 ≤ X →
      |(Chebyshev.psi (2*X)-Chebyshev.psi X)-X| ≤ (X/Real.exp 1)*retained (Real.log X-1)
        + C*X^(5/6:ℝ)*(1+Real.log X)^2 := by
  obtain ⟨C,hC,h⟩ := sharp_dyadic_log
  refine ⟨C,hC,?_⟩
  intro X hX
  have hx := (Real.exp_pos 2).trans_le hX
  let T := Real.log X-1
  have hT : 1 ≤ T := by
    have e := Real.log_le_log (Real.exp_pos 2) hX
    rw [Real.log_exp] at e
    dsimp [T]; linarith
  have he : Real.exp (T+1)=X := by dsimp [T]; rw [sub_add_cancel,Real.exp_log hx]
  have heT : Real.exp T = X/Real.exp 1 := by simp only [T,Real.exp_sub,Real.exp_log hx]
  have hp : Real.exp T*Real.exp (-(T/6)) ≤ X^(5/6:ℝ) := by
    rw [← Real.exp_add,Real.rpow_def_of_pos hx]
    apply Real.exp_le_exp.mpr
    dsimp only [T]; linarith
  have hlog : T+2 = 1+Real.log X := by dsimp [T]; ring
  have hs := h T hT
  rw [he,mul_add,hlog] at hs
  apply hs.trans
  rw [← heT]
  apply add_le_add (le_refl _)
  calc
    _ = C*(Real.exp T*Real.exp (-(T/6)))*(1+Real.log X)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (sq_nonneg _)

#print axioms sharp_dyadic_X
end RHConnections.SharpRightEndpoint
