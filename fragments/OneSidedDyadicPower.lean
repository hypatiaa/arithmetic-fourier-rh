import Verified
import OneSidedPrimePower

noncomputable section
open Filter
namespace RHConnections.PrimeErrorPower
open RHConnections.PrimeErrorLaplace

def realDyadicPrimeError (X : ℝ) : ℝ := realPrimeError (2*X)-realPrimeError X

theorem signed_dyadic_to_endpoint_bound {a σ C : ℝ} (ha : 0<a) (hσ : |σ|=1) (hC : 0≤C)
    (hStep : ∀ᶠ x : ℝ in atTop, -(C*x^a)≤σ*realDyadicPrimeError x) :
    ∃ B : ℝ, 0≤B ∧ ∀ x>1, -(B*x^a)≤σ*realPrimeError x := by
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hStep
  let W := max 2 Y
  let b := C/((2:ℝ)^a-1)
  let g (x : ℝ) := σ*realPrimeError x+b*x^a
  let D := Real.log 4+5
  let K := D*(2*W)
  have hW : 2≤W := le_max_left _ _
  have hW0 : 0<W := by linarith
  have hbden : 0<(2:ℝ)^a-1 := sub_pos.mpr (Real.one_lt_rpow (by norm_num) ha)
  have hb : 0≤b := div_nonneg hC hbden.le
  have hD : 0≤D := by dsimp [D]; linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
  have hK : 0≤K := by dsimp [K]; positivity
  have hlocal (x : ℝ) (hx : 0≤x) (hxU : x≤2*W) : -K≤σ*realPrimeError x := by
    have h := neg_abs_le (σ*realPrimeError x)
    rw [abs_mul,hσ,one_mul] at h
    have hE := (real_prime_error_linear hx).trans (mul_le_mul_of_nonneg_left hxU hD)
    dsimp [K,D] at *
    linarith only [h,hE]
  have hmono (x : ℝ) (hx : W≤x) : g x≤g (2*x) := by
    have hxp := hW0.le.trans hx
    have hSt := hY x ((le_max_right _ _).trans hx)
    have hId : b*((2:ℝ)^a-1)=C := div_mul_cancel₀ _ hbden.ne'
    have hId' := congrArg (fun z : ℝ => z*x^a) hId
    dsimp only [g]
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hxp]
    unfold realDyadicPrimeError at hSt
    nlinarith only [hSt,hId']
  have hiter (x : ℝ) (hx : W≤x) (n : ℕ) : g x≤g ((2:ℝ)^n*x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hx0 := hW0.le.trans hx
      have hx' : W≤(2:ℝ)^n*x := hx.trans (le_mul_of_one_le_left hx0
        (one_le_pow₀ (by norm_num) (n := n)))
      exact ih.trans ((hmono _ hx').trans_eq (by congr 1; rw [pow_succ]; ring))
  refine ⟨b+K,add_nonneg hb hK,?_⟩
  intro X hX
  have hX1 : 1≤X := hX.le
  have hpow : 1≤X^a := Real.one_le_rpow hX1 ha.le
  have hKpow := le_mul_of_one_le_right hK hpow
  by_cases hHigh : W≤X
  · obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near
      ((le_div_iff₀ hW0).mpr (by simpa using hHigh)) (by norm_num : (1:ℝ)<2)
    let x := X/(2:ℝ)^n
    have hp : 0<(2:ℝ)^n := by positivity
    have hxW : W≤x := (le_div_iff₀ hp).mpr (by
      have h := (le_div_iff₀ hW0).mp hn
      nlinarith only [h])
    have hxU : x≤2*W := (div_le_iff₀ hp).mpr (by
      have h := (div_lt_iff₀ hW0).mp hn'
      rw [pow_succ] at h <;> nlinarith only [h])
    have hXeq : (2:ℝ)^n*x=X := by dsimp [x]; field_simp
    have hLower : -K≤g x := by
      dsimp only [g]
      have h := hlocal x (hW0.le.trans hxW) hxU
      linarith only [h,mul_nonneg hb (Real.rpow_nonneg (hW0.le.trans hxW) a)]
    have h := hLower.trans (hiter x hxW n)
    rw [hXeq] at h
    dsimp only [g] at h
    linarith only [h,hKpow,show (b+K)*X^a=b*X^a+K*X^a by ring]
  · have h := hlocal X (by linarith) (by linarith [lt_of_not_ge hHigh])
    have hn := mul_nonneg hb (Real.rpow_nonneg (by linarith : 0≤X) a)
    linarith only [h,hn,hKpow,show (b+K)*X^a=b*X^a+K*X^a by ring]

theorem zero_free_of_signed_dyadic_power {a σ C : ℝ} (ha : 0<a) (ha1 : a<1)
    (hσ : σ=1 ∨ σ= -1) (hC : 0≤C)
    (hStep : ∀ᶠ x : ℝ in atTop, -(C*x^a)≤σ*realDyadicPrimeError x) :
    ∀ s : ℂ, a<s.re → riemannZeta s≠0 := by
  have hσ' : |σ|=1 := by rcases hσ with rfl|rfl <;> norm_num
  obtain ⟨B,_,hB⟩ := signed_dyadic_to_endpoint_bound ha hσ' hC hStep
  apply zero_free_of_signed_prime_power ha.le ha1 hσ (C := B)
  intro X hX
  have hX0 : 0<X := by linarith
  rw [Real.rpow_neg hX0.le,←div_eq_mul_inv]
  have hP := Real.rpow_pos_of_pos hX0 a
  have hBound : -B*X^a≤σ*realPrimeError X := by rw [neg_mul]; exact hB X hX
  have h := (le_div_iff₀ hP).mpr hBound
  linarith

theorem dyadic_prime_error_oscillates_beyond_power_of_zero {s : ℂ} (hz : riemannZeta s=0)
    {a : ℝ} (ha : 0<a) (ha1 : a<1) (hs : a<s.re)
    (C : ℝ) (hC : 0≤C) (Y : ℝ) :
    (∃ X≥Y, C*X^a<realDyadicPrimeError X) ∧
      (∃ X≥Y, realDyadicPrimeError X< -(C*X^a)) := by
  constructor
  · by_contra! h
    have h' : ∀ᶠ X : ℝ in atTop, -(C*X^a)≤(-1:ℝ)*realDyadicPrimeError X := by
      filter_upwards [eventually_ge_atTop Y] with X hX
      linarith [h X hX]
    exact zero_free_of_signed_dyadic_power ha ha1 (Or.inr rfl) hC h' s hs hz
  · by_contra! h
    have h' : ∀ᶠ X : ℝ in atTop, -(C*X^a)≤(1:ℝ)*realDyadicPrimeError X := by
      filter_upwards [eventually_ge_atTop Y] with X hX
      simpa only [one_mul] using h X hX
    exact zero_free_of_signed_dyadic_power ha ha1 (Or.inl rfl) hC h' s hs hz

end RHConnections.PrimeErrorPower
