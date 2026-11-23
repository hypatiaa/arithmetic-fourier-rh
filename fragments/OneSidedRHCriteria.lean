import Verified
import OneSidedDyadicPower
import OneSidedFourierScalar

noncomputable section
open Filter Asymptotics

namespace RHConnections.ArithmeticFourierInversion

theorem fixed_strip_iff_one_sided_fourier_scalar (B : ℕ) {a σ : ℝ}
    (ha : 1/2≤a) (ha1 : a<1) (hσ : σ=1 ∨ σ= -1) :
    (∀ s : ℂ, a<s.re → riemannZeta s≠0) ↔
      (∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0≤C ∧
        ∀ᶠ n : ℕ in atTop, -(C*(n:ℝ)^(a+ε))≤σ*S B n) := by
  constructor
  · intro h ε hε
    obtain ⟨C,hC,h⟩ := (fixed_strip_iff_fourier_scalar_power B ha ha1).mp h ε hε
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hσ' : |σ|=1 := by rcases hσ with rfl|rfl <;> norm_num
    have hh := neg_abs_le (σ*S B n)
    rw [abs_mul,hσ',one_mul] at hh
    linarith [h n hn]
  · intro h s hs
    let ε := min ((s.re-a)/2) ((1-a)/2)
    have hε : 0<ε := lt_min (by linarith) (by linarith)
    have hb0 : 0≤a+ε := by linarith
    have hb1 : a+ε<1 := by linarith [min_le_right ((s.re-a)/2) ((1-a)/2)]
    have hbs : a+ε<s.re := by linarith [min_le_left ((s.re-a)/2) ((1-a)/2)]
    obtain ⟨C,hC,hStep⟩ := h ε hε
    exact zero_free_of_one_sided_fourier_scalar B hb0 hb1 hσ hC hStep s hbs

theorem rh_iff_one_sided_fourier_scalar (B : ℕ) {σ : ℝ} (hσ : σ=1 ∨ σ= -1) :
    RiemannHypothesis ↔
      (∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0≤C ∧
        ∀ᶠ n : ℕ in atTop, -(C*(n:ℝ)^(1/2+ε))≤σ*S B n) :=
  ⟨fun h => (fixed_strip_iff_one_sided_fourier_scalar B le_rfl (by norm_num) hσ).mp
    (ZetaDiskLog.right_zero_free_of_RH h),
    fun h => PoleCompensation.riemannHypothesis_of_right_zero_free
      ((fixed_strip_iff_one_sided_fourier_scalar B le_rfl (by norm_num) hσ).mpr h)⟩

end RHConnections.ArithmeticFourierInversion

namespace RHConnections.PrimeErrorPower
open RHConnections.DyadicEndpoint RHConnections.PrimeErrorLaplace

theorem norm_dyadic_prime_error_eq (x : ℝ) : ‖dyadicChebyshevError x‖ = |realDyadicPrimeError x| := by
  rw [SharpRightEndpoint.norm_dyadic_chebyshev_error]
  unfold realDyadicPrimeError realPrimeError
  congr 1
  ring

theorem fixed_strip_iff_one_sided_dyadic_prime_error {a σ : ℝ}
    (ha : 1/2≤a) (ha1 : a<1) (hσ : σ=1 ∨ σ= -1) :
    (∀ s : ℂ, a<s.re → riemannZeta s≠0) ↔
      (∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0≤C ∧
        ∀ᶠ X : ℝ in atTop, -(C*X^(a+ε))≤σ*realDyadicPrimeError X) := by
  constructor
  · intro h ε hε
    obtain ⟨C,hC,h⟩ := ((fixed_strip_iff_dyadic_chebyshev_power ha ha1).mp h ε hε).exists_nonneg
    refine ⟨C,hC,?_⟩
    filter_upwards [h.bound,eventually_ge_atTop (1:ℝ)] with X hX h1
    rw [norm_dyadic_prime_error_eq,Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans h1) _)] at hX
    have hσ' : |σ|=1 := by rcases hσ with rfl|rfl <;> norm_num
    have hh := neg_abs_le (σ*realDyadicPrimeError X)
    rw [abs_mul,hσ',one_mul] at hh
    linarith
  · intro h s hs
    let ε := min ((s.re-a)/2) ((1-a)/2)
    have hε : 0<ε := lt_min (by linarith) (by linarith)
    have hb0 : 0<a+ε := by linarith
    have hb1 : a+ε<1 := by linarith [min_le_right ((s.re-a)/2) ((1-a)/2)]
    have hbs : a+ε<s.re := by linarith [min_le_left ((s.re-a)/2) ((1-a)/2)]
    obtain ⟨C,hC,hStep⟩ := h ε hε
    exact zero_free_of_signed_dyadic_power hb0 hb1 hσ hC hStep s hbs

theorem rh_iff_one_sided_dyadic_prime_error {σ : ℝ} (hσ : σ=1 ∨ σ= -1) :
    RiemannHypothesis ↔
      (∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0≤C ∧
        ∀ᶠ X : ℝ in atTop, -(C*X^(1/2+ε))≤σ*realDyadicPrimeError X) :=
  ⟨fun h => (fixed_strip_iff_one_sided_dyadic_prime_error le_rfl (by norm_num) hσ).mp
    (ZetaDiskLog.right_zero_free_of_RH h),
    fun h => PoleCompensation.riemannHypothesis_of_right_zero_free
      ((fixed_strip_iff_one_sided_dyadic_prime_error le_rfl (by norm_num) hσ).mpr h)⟩

end RHConnections.PrimeErrorPower
