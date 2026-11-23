import Verified
import FixedStripChebyshev
import SharpRetainedStripBound

noncomputable section
open Filter Asymptotics
namespace RHConnections.SharpRightEndpoint
open RHConnections.ChebyshevCriterion RHConnections.DyadicEndpoint RHConnections.RankContrast

def retainedDyadicAmplitude (X : ℝ) : ℝ :=
  (X/Real.exp 1)*retained (Real.log X-1)

private theorem psi_eq_coe_chebyshev (x : ℝ) : psi x = (Chebyshev.psi x:ℂ) := by
  rw [Chebyshev.psi_eq_sum_Icc,Complex.ofReal_sum]
  unfold psi mangoldtCoeff
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Icc.mp hn).2⟩
  · intro n hn hx
    have hz : n=0 := by
      by_contra hd
      exact hx (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd,(Finset.mem_Icc.mp hn).2⟩)
    simp [hz]

theorem norm_dyadic_chebyshev_error (x : ℝ) : ‖dyadicChebyshevError x‖ =
    |(Chebyshev.psi (2*x)-Chebyshev.psi x)-x| := by
  unfold dyadicChebyshevError psiError
  rw [psi_eq_coe_chebyshev,psi_eq_coe_chebyshev]
  have h : (↑(Chebyshev.psi (2*x))-(↑(2*x):ℂ))-(↑(Chebyshev.psi x)-(x:ℂ)) =
      ((Chebyshev.psi (2*x)-Chebyshev.psi x-x:ℝ):ℂ) := by push_cast; ring
  rw [h,Complex.norm_real,Real.norm_eq_abs]

private theorem log_square_absorption {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℝ in atTop, (1+Real.log X)^2≤4*X^ε := by
  filter_upwards [eventually_log_rpow_absorbed 2 hε, eventually_ge_atTop (Real.exp 1)] with X h hX
  have hX0 := (Real.exp_pos 1).trans_le hX
  have hL : 1≤Real.log X := by
    have h' := Real.log_le_log (Real.exp_pos 1) hX
    rwa [Real.log_exp] at h'
  have htwo : (Real.log X)^(2:ℕ)≤X^ε := by
    change (Real.log X)^(2:ℝ)≤X^ε at h
    simpa only [Real.rpow_two] using h
  calc
    _ ≤ (2*Real.log X)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    _ = 4*(Real.log X)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htwo (by norm_num)

theorem dyadic_remainder_order {a ε : ℝ} (ha : 5/6≤a) (hε : 0<ε) :
    ∀ᶠ X : ℝ in atTop, X^(5/6:ℝ)*(1+Real.log X)^2≤4*X^(a+ε) := by
  filter_upwards [log_square_absorption hε,eventually_ge_atTop (1:ℝ)] with X hX h1
  have hXp := zero_lt_one.trans_le h1
  calc
    _ ≤ X^(5/6:ℝ)*(4*X^ε) := mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 4*X^(5/6+ε) := by rw [Real.rpow_add hXp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (by norm_num)

theorem fixed_strip_iff_retained_dyadic_amplitude {a : ℝ} (ha : 5/6≤a) (ha1 : a<1) :
    (∀ s : ℂ, a<s.re → riemannZeta s≠0) ↔
      (∀ ε : ℝ, 0<ε → retainedDyadicAmplitude =O[atTop] (fun X : ℝ => X^(a+ε))) := by
  constructor
  · intro hStrip ε hε
    obtain ⟨C,hC,hR⟩ := retained_bound_of_strip hStrip
    apply IsBigO.of_bound (4*C*Real.exp (-a))
    filter_upwards [log_square_absorption hε, eventually_ge_atTop (Real.exp 2)] with X hLog hX
    have hx := (Real.exp_pos 2).trans_le hX
    let T := Real.log X-1
    have hT : 1≤T := by
      have hh := Real.log_le_log (Real.exp_pos 2) hX
      rw [Real.log_exp] at hh
      dsimp [T]
      linarith
    have he : (X/Real.exp 1)*Real.exp ((a-1)*T) = Real.exp (-a)*X^a := by
      rw [←Real.exp_log hx,←Real.exp_sub,←Real.exp_add,Real.rpow_def_of_pos (Real.exp_pos _),
        Real.log_exp,←Real.exp_add]
      congr 1
      dsimp [T]
      ring
    have hLog' : (T+2)^2≤4*X^ε := by
      convert hLog using 2
      dsimp [T]
      ring
    have hR₀ : 0≤retained T := le_max_of_le_left (norm_nonneg _)
    rw [Real.norm_of_nonneg (show 0≤retainedDyadicAmplitude X from
      mul_nonneg (by positivity) hR₀),Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
    calc
      _ ≤ (X/Real.exp 1)*(C*Real.exp ((a-1)*T)*(4*X^ε)) :=
        mul_le_mul_of_nonneg_left ((hR T hT).trans (mul_le_mul_of_nonneg_left hLog' (by positivity)))
          (by positivity)
      _ = (4*C)*(((X/Real.exp 1)*Real.exp ((a-1)*T))*X^ε) := by ring
      _ = _ := by rw [he,Real.rpow_add hx]; ring
  · intro hAmp
    apply (fixed_strip_iff_dyadic_chebyshev_power (by linarith : 1/2≤a) ha1).mpr
    intro ε hε
    obtain ⟨C,hC,hC'⟩ := (hAmp ε hε).exists_nonneg
    obtain ⟨D,hD,hR⟩ := sharp_dyadic_X
    apply IsBigO.of_bound (C+4*D)
    filter_upwards [dyadic_remainder_order ha hε, eventually_ge_atTop (Real.exp 2),hC'.bound] with
      X hErr hX hAmpX
    have hX0 := (Real.exp_pos 2).trans_le hX
    rw [norm_dyadic_chebyshev_error]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)] at hAmpX ⊢
    refine (hR X hX).trans ?_
    have h' : retainedDyadicAmplitude X≤C*X^(a+ε) :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hAmpX)
    have hRem := mul_le_mul_of_nonneg_left hErr hD
    change retainedDyadicAmplitude X+D*X^(5/6:ℝ)*(1+Real.log X)^2≤_
    nlinarith only [h',hRem]

end RHConnections.SharpRightEndpoint
