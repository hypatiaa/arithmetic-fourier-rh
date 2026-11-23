import Verified

noncomputable section
open Filter
namespace RHConnections.ParametricSignedSharp
open PrimeErrorPower
open ParametricSharpRightEndpoint (parametric_dyadic_remainder_order)

theorem zero_free_of_fixed_signed_mode {a b σ K : ℝ} (ha : 1/2≤a) (hab : a≤b) (hb1 : b<1)
    (hσ : σ=1 ∨ σ= -1) (hK : 0≤K)
    (h : ∀ᶠ T : ℝ in atTop, signedMode a σ T≤K*Real.exp ((b-1)*T)) :
    ∀ s : ℂ, b<s.re → riemannZeta s≠0 := by
  intro s hs
  let d := min ((s.re-b)/2) ((1-b)/2)
  have hd : 0<d := lt_min (by linarith) (by linarith)
  have hbd1 : b+d<1 := by linarith [min_le_right ((s.re-b)/2) ((1-b)/2)]
  have hbs : b+d<s.re := by linarith [min_le_left ((s.re-b)/2) ((1-b)/2)]
  have hβ : 0<b+d := by linarith
  obtain ⟨C,hC,hR⟩ := signed_mode_bounds_prime_error ha (hab.trans_lt hb1) hσ
  obtain ⟨Y,hY⟩ := eventually_atTop.mp h
  have hGap : 0<b+d-a := by linarith
  have hRem := parametric_dyadic_remainder_order a hGap
  have hExpSum : a+(b+d-a)=b+d := by ring
  have hStep : ∀ᶠ X : ℝ in atTop, -((K+4*C)*X^(b+d))≤σ*realDyadicPrimeError X := by
    filter_upwards [eventually_ge_atTop (max (Real.exp 2) (Real.exp (Y+1))),hRem] with X hX hE
    have hX2 := (le_max_left (Real.exp 2) _).trans hX
    have hx := (Real.exp_pos 2).trans_le hX2
    let T := Real.log X-1
    have hT : 1≤T := by
      have hh := Real.log_le_log (Real.exp_pos 2) hX2
      rw [Real.log_exp] at hh
      dsimp [T]
      linarith
    have hTY : Y≤T := by
      have hh := Real.log_le_log (Real.exp_pos (Y+1)) ((le_max_right (Real.exp 2) _).trans hX)
      rw [Real.log_exp] at hh
      dsimp [T]
      linarith
    have hTime : (X/Real.exp 1)*Real.exp ((b-1)*T)≤X^(b+d) := by
      have hTexp : X/Real.exp 1=Real.exp T := by simp only [T,Real.exp_sub,Real.exp_log hx]
      rw [hTexp,←Real.exp_add,Real.rpow_def_of_pos hx]
      apply Real.exp_le_exp.mpr
      have hlog : 0≤Real.log X := by dsimp [T] at hT; linarith
      dsimp [T]
      nlinarith only [ha,hab,mul_nonneg hd.le hlog]
    have hMode : (X/Real.exp 1)*signedMode a σ T≤K*X^(b+d) := by
      refine (mul_le_mul_of_nonneg_left (hY T hTY) (by positivity)).trans ?_
      calc
        _ = K*((X/Real.exp 1)*Real.exp ((b-1)*T)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hTime hK
    rw [hExpSum] at hE
    have hC' := mul_le_mul_of_nonneg_left hE hC
    have hh := hR X hX2
    nlinarith only [hMode,hC',hh]
  exact zero_free_of_signed_dyadic_power hβ hbd1 hσ (by positivity) hStep s hbs

theorem signed_mode_excursions_of_zero {s : ℂ} (hz : riemannZeta s=0)
    {a b σ K : ℝ} (ha : 1/2≤a) (hab : a≤b) (hb1 : b<1) (hs : b<s.re)
    (hσ : σ=1 ∨ σ= -1) (hK : 0≤K) (Y : ℝ) :
    ∃ T≥Y, K*Real.exp ((b-1)*T)<signedMode a σ T := by
  by_contra! h
  have hEv : ∀ᶠ T : ℝ in atTop, signedMode a σ T≤K*Real.exp ((b-1)*T) := by
    filter_upwards [eventually_ge_atTop Y] with T hT using h T hT
  exact zero_free_of_fixed_signed_mode ha hab hb1 hσ hK hEv s hs hz

end RHConnections.ParametricSignedSharp
