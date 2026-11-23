import Verified
import SharpChebyshevError

noncomputable section
namespace RHConnections.ArithmeticFourierDyadic
open ArithmeticFourierInversion ArithmeticFourierShortBlocks SharpChebyshevError

theorem prime_remainder_log_power (A : ℝ) (hA : 0<A) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 2≤n →
      |primeRemainder n|≤C*(n:ℝ)/(Real.log (n:ℝ))^A := by
  obtain ⟨a,D,ha,hD,hsharp⟩ := chebyshev_quantitative_error
  obtain ⟨k,hk⟩ := exists_nat_gt (2*A)
  let F := (k.factorial:ℝ)/a^k
  let E := Real.log 4+5
  let C := D*F+E*2^A
  have hF : 0≤F := by dsimp [F]; positivity
  have hE : 0≤E := by
    have h := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
    dsimp [E]; linarith
  refine ⟨C,by dsimp [C]; positivity,fun n hn => ?_⟩
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : (0:ℝ)<n := zero_lt_one.trans hn1
  have hlog : 0<Real.log (n:ℝ) := Real.log_pos hn1
  have hlogpow : 0<(Real.log (n:ℝ))^A := Real.rpow_pos_of_pos hlog _
  apply (le_div_iff₀ hlogpow).mpr
  by_cases hN : Real.exp 2≤(n:ℝ)
  · let v := Real.sqrt (Real.log (n:ℝ))
    have hv : 1≤v := by
      have he := Real.log_le_log (Real.exp_pos 2) hN
      rw [Real.log_exp] at he
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by linarith)
    have hvsq : v^2 = Real.log (n:ℝ) := Real.sq_sqrt hlog.le
    have hpower : (Real.log (n:ℝ))^A ≤ v^k := by
      rw [← hvsq]
      calc
        _ = v^(2*A) := by
          symm
          simpa only [Nat.cast_ofNat] using Real.rpow_natCast_mul (show 0≤v by positivity) 2 A
        _ ≤ v^(k:ℝ) := Real.rpow_le_rpow_of_exponent_le hv hk.le
        _ = _ := Real.rpow_natCast _ _
    have hexp : v^k ≤ F*Real.exp (a*v) := by
      have h := Real.pow_div_factorial_le_exp (a*v) (by positivity) k
      have hfac : (0:ℝ)<k.factorial := by exact_mod_cast Nat.factorial_pos k
      have hh := (div_le_iff₀ hfac).mp h
      rw [mul_pow] at hh
      unfold F
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (pow_pos ha k)).mpr
      simpa [mul_comm] using hh
    have hdecay : Real.exp (-a*v)*(Real.log (n:ℝ))^A ≤ F := by
      calc
        _ ≤ Real.exp (-a*v)*v^k := mul_le_mul_of_nonneg_left hpower (Real.exp_pos _).le
        _ ≤ Real.exp (-a*v)*(F*Real.exp (a*v)) := mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
        _ = _ := by rw [mul_left_comm,← Real.exp_add,show -a*v+a*v=0 by ring,Real.exp_zero,mul_one]
    have hh := hsharp (n:ℝ) hN
    change |primeRemainder n|≤D*(n:ℝ)*Real.exp (-a*v) at hh
    calc
      _ ≤ (D*(n:ℝ)*Real.exp (-a*v))*(Real.log (n:ℝ))^A := mul_le_mul_of_nonneg_right hh hlogpow.le
      _ = (D*(n:ℝ))*(Real.exp (-a*v)*(Real.log (n:ℝ))^A) := by ring
      _ ≤ D*(n:ℝ)*F := mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ ≤ C*(n:ℝ) := by
        have hCD : D*F≤C := le_add_of_nonneg_right (by positivity)
        exact (mul_le_mul_of_nonneg_right hCD hn0.le).trans_eq' (by ring)
  · have hlo := Real.log_le_log hn0 (le_of_not_ge hN)
    rw [Real.log_exp] at hlo
    have hpow := Real.rpow_le_rpow hlog.le hlo hA.le
    have hbound := PrimeErrorLaplace.real_prime_error_linear hn0.le
    change |primeRemainder n|≤E*(n:ℝ) at hbound
    calc
      _ ≤ (E*(n:ℝ))*(Real.log (n:ℝ))^A := mul_le_mul_of_nonneg_right hbound hlogpow.le
      _ ≤ E*(n:ℝ)*2^A := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ C*(n:ℝ) := by
        have hEC : E*2^A≤C := by
          dsimp [C]
          exact le_add_of_nonneg_left (mul_nonneg hD hF)
        exact (mul_le_mul_of_nonneg_right hEC hn0.le).trans_eq' (by ring)

theorem unconditional_unblocked_log_saving (A : ℝ) (hA : 0<A) :
    ∃ D : ℝ, 0≤D ∧ ∀ B X Q : ℕ, 2≤Q →
      |∑ q ∈ Finset.Ioc Q (2*Q),(shortWeight B q-1)*S B (X/q)| ≤
        D*(X:ℝ)/(Real.log (Q:ℝ))^A := by
  obtain ⟨C,hC,hprime⟩ := prime_remainder_log_power A hA
  have hlog : 0≤Real.log 4 := by positivity
  exact ⟨3*C+2*(Real.log 4+4)*A^A,by positivity,
    fun B X Q hQ => dyadic_unblocked_log_power_transfer A C hA hC hprime B X Q hQ⟩

end RHConnections.ArithmeticFourierDyadic
