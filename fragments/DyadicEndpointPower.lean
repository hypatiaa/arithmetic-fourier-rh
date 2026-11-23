import Verified

noncomputable section
open Filter Asymptotics
namespace RHConnections.DyadicEndpoint

theorem power_from_doubling_difference (f : ℝ → ℂ) {θ A B : ℝ}
    (hθ : 0<θ) (hA : 0≤A) (hB : 0≤B)
    (hbase : ∀ x : ℝ, 1≤x → x<2 → ‖f x‖≤B)
    (hstep : ∀ x : ℝ, 1≤x → ‖f (2*x)-f x‖≤A*x^θ) :
    ∀ x : ℝ, 1≤x → ‖f x‖≤(B+A/(2^θ-1))*x^θ := by
  let C := B+A/(2^θ-1)
  have h2 : 1<(2:ℝ)^θ := by
    exact Real.one_lt_rpow (by norm_num) hθ
  have hC : 0≤C := by dsimp [C]; positivity
  have hCbase : B≤C := by dsimp [C]; linarith [div_nonneg hA (sub_nonneg.mpr h2.le)]
  have hscale : A+C≤C*(2:ℝ)^θ := by
    have h := mul_nonneg hB (sub_nonneg.mpr h2.le)
    dsimp [C] at *
    have he : (A/(2^θ-1))*(2^θ-1)=A := div_mul_cancel₀ _ (sub_ne_zero.mpr h2.ne')
    nlinarith only [h,he]
  have hInd (n : ℕ) : ∀ x : ℝ, 1≤x → ⌊x⌋₊=n → ‖f x‖≤C*x^θ := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hn
      by_cases hx2 : x<2
      · exact (hbase x hx hx2).trans (hCbase.trans (le_mul_of_one_le_right hC (Real.one_le_rpow hx hθ.le)))
      · let y := x/2
        have hy1 : 1≤y := by dsimp [y]; linarith
        have hyp : 0≤y := by linarith
        have hy : y<x := by dsimp [y]; linarith
        have hfloor : ⌊y⌋₊<n := by
          have hnx : x<(n:ℝ)+1 := by
            have hh := Nat.lt_floor_add_one x
            rwa [hn] at hh
          have hny : y<(n:ℝ) := by
            have hn1 : 1≤n := by rw [←hn]; exact (Nat.le_floor_iff (by linarith)).mpr (by simpa using hx)
            have hn1' : (1:ℝ)≤n := by exact_mod_cast hn1
            dsimp [y]
            linarith
          exact (Nat.floor_lt hyp).2 hny
        have hfy := ih ⌊y⌋₊ hfloor y hy1 rfl
        have hxy : x=2*y := by dsimp [y]; ring
        have hdiff : ‖f x-f y‖≤A*y^θ := by simpa only [←hxy] using hstep y hy1
        calc
          ‖f x‖ = ‖(f x-f y)+f y‖ := by rw [sub_add_cancel]
          _ ≤ ‖f x-f y‖+‖f y‖ := norm_add_le _ _
          _ ≤ (A+C)*y^θ := (add_le_add hdiff hfy).trans_eq (by ring)
          _ ≤ (C*(2:ℝ)^θ)*y^θ := mul_le_mul_of_nonneg_right hscale (by positivity)
          _ = C*x^θ := by rw [mul_assoc,←Real.mul_rpow (by norm_num) hyp,←hxy]
  exact fun x hx => hInd ⌊x⌋₊ x hx rfl

end RHConnections.DyadicEndpoint
