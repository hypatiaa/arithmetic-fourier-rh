import Verified
import OneSidedRHCriteria

noncomputable section
open Filter
namespace RHConnections.PrimeErrorPower
open PrimeErrorLaplace

private theorem psi_nat_succ (n : ℕ) :
    Chebyshev.psi ((n+1:ℕ):ℝ)=Chebyshev.psi (n:ℝ)+ArithmeticFunction.vonMangoldt (n+1) := by
  rw [Chebyshev.psi_eq_sum_Icc,Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  rw [show Finset.Icc 0 (n+1)=insert (n+1) (Finset.Icc 0 n) by ext i; simp; omega]
  rw [Finset.sum_insert (by simp)]
  ring

theorem dyadic_prime_error_floor_error {X : ℝ} (hX : 1≤X) :
    |realDyadicPrimeError X-realDyadicPrimeError (⌊X⌋₊:ℝ)|≤1+Real.log (2*X) := by
  let n := ⌊X⌋₊
  have hX0 := zero_le_one.trans hX
  have hnX : (n:ℝ)≤X := Nat.floor_le hX0
  have hXn : X<(n:ℝ)+1 := Nat.lt_floor_add_one X
  have h2n : (2*n:ℕ)≤⌊2*X⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by push_cast; linarith)
  have h2n' : ⌊2*X⌋₊≤2*n+1 := by
    have h := Nat.floor_le (show 0≤2*X by positivity)
    have h' : (⌊2*X⌋₊:ℝ)<((2*n+2:ℕ):ℝ) := by push_cast; linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast h')
  have hψ (x : ℝ) : Chebyshev.psi x=Chebyshev.psi (⌊x⌋₊:ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc,Chebyshev.psi_eq_sum_Icc,Nat.floor_natCast]
  let e := Chebyshev.psi (2*X)-Chebyshev.psi ((2*n:ℕ):ℝ)
  have he0 : 0≤e := sub_nonneg.mpr (Chebyshev.psi_mono (by push_cast; linarith))
  have he1 : e≤Real.log (2*X) := by
    have hCases : ⌊2*X⌋₊=2*n ∨ ⌊2*X⌋₊=2*n+1 := by omega
    dsimp only [e]
    rw [hψ (2*X)]
    rcases hCases with h | h
    · rw [h,sub_self]
      exact Real.log_nonneg (by linarith)
    · rw [h,psi_nat_succ,add_sub_cancel_left]
      have hval : ((2*n+1:ℕ):ℝ)≤2*X := by
        have hh := Nat.floor_le (show 0≤2*X by positivity)
        rwa [h] at hh
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by positivity) hval)
  have he : realDyadicPrimeError X-realDyadicPrimeError (n:ℝ)=e-(X-(n:ℝ)) := by
    unfold realDyadicPrimeError realPrimeError
    rw [hψ X]
    change _ = Chebyshev.psi (2*X)-Chebyshev.psi ((2*n:ℕ):ℝ)-(X-(n:ℝ))
    push_cast
    ring
  rw [he]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem signed_natural_dyadic_gives_real_power {a σ C : ℝ}
    (ha : 0<a) (hσ : |σ|=1) (hC : 0≤C)
    (hStep : ∀ᶠ n : ℕ in atTop, -(C*(n:ℝ)^a)≤σ*realDyadicPrimeError (n:ℝ)) :
    ∃ D : ℝ, 0≤D ∧ ∀ᶠ X : ℝ in atTop, -(D*X^a)≤σ*realDyadicPrimeError X := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hStep
  let D := C+(1+Real.log 2+a⁻¹)
  have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop ((N:ℝ)+1)] with X hX
  have hX1 : 1≤X := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hX0 := zero_lt_one.trans_le hX1
  let n := ⌊X⌋₊
  have hn : N≤n := (Nat.le_floor_iff hX0.le).mpr (by linarith)
  have hφ := hN n hn
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg n) (Nat.floor_le hX0.le) ha.le
  have he := dyadic_prime_error_floor_error hX1
  have hsg := neg_abs_le (σ*(realDyadicPrimeError X-realDyadicPrimeError (n:ℝ)))
  rw [abs_mul,hσ,one_mul,mul_sub] at hsg
  have hL : 1+Real.log (2*X)≤(1+Real.log 2+a⁻¹)*X^a := by
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hX0.ne']
    have h := Real.log_le_rpow_div hX0.le ha
    rw [div_eq_mul_inv] at h
    have hXpow := Real.one_le_rpow hX1 ha.le
    calc
      _ ≤ (1+Real.log 2)*X^a+a⁻¹*X^a := by
        have h' := le_mul_of_one_le_right (show 0≤1+Real.log 2 by linarith) hXpow
        nlinarith only [h,h']
      _ = _ := by ring
  dsimp only [D]
  nlinarith only [hsg,hφ,he,hL,mul_le_mul_of_nonneg_left hp hC]

theorem zero_free_of_signed_natural_dyadic_power {a σ C : ℝ} (ha : 0<a) (ha1 : a<1)
    (hσ : σ=1 ∨ σ= -1) (hC : 0≤C)
    (hStep : ∀ᶠ n : ℕ in atTop, -(C*(n:ℝ)^a)≤σ*realDyadicPrimeError (n:ℝ)) :
    ∀ s : ℂ, a<s.re → riemannZeta s≠0 := by
  have hσ' : |σ|=1 := by rcases hσ with rfl|rfl <;> norm_num
  obtain ⟨D,hD,h⟩ := signed_natural_dyadic_gives_real_power ha hσ' hC hStep
  exact zero_free_of_signed_dyadic_power ha ha1 hσ hD h

theorem rh_iff_one_sided_natural_dyadic_prime_error {σ : ℝ} (hσ : σ=1 ∨ σ= -1) :
    RiemannHypothesis ↔
      (∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0≤C ∧
        ∀ᶠ n : ℕ in atTop, -(C*(n:ℝ)^(1/2+ε))≤σ*realDyadicPrimeError (n:ℝ)) := by
  constructor
  · intro h ε hε
    obtain ⟨C,hC,h⟩ := (rh_iff_one_sided_dyadic_prime_error hσ).mp h ε hε
    exact ⟨C,hC,tendsto_natCast_atTop_atTop.eventually h⟩
  · intro h
    apply PoleCompensation.riemannHypothesis_of_right_zero_free
    intro s hs
    let ε := min ((s.re-1/2)/2) (1/4)
    have he : 0<ε := lt_min (by linarith) (by norm_num)
    have he1 : (1/2:ℝ)+ε<1 := by linarith [min_le_right ((s.re-1/2)/2) (1/4:ℝ)]
    have hs' : (1/2:ℝ)+ε<s.re := by linarith [min_le_left ((s.re-1/2)/2) (1/4:ℝ)]
    obtain ⟨C,hC,hN⟩ := h ε he
    exact zero_free_of_signed_natural_dyadic_power (by linarith) he1 hσ hC hN s hs'

end RHConnections.PrimeErrorPower
