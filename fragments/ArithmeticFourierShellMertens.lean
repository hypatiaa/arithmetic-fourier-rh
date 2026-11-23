import Verified

open Finset ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierShell
open ArithmeticFourierInversion

def oddUpTo (X : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter Odd

theorem upper_odd_shell_eq_sdiff (X : ℕ) :
    upperOddShell X = oddUpTo X \ oddUpTo (X/2) := by
  ext n
  simp only [upper_odd_shell_iff,Finset.mem_sdiff,oddUpTo,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨hn,hX,hO,hlo⟩
    exact ⟨⟨⟨hn,hX⟩,hO⟩,fun h => by omega⟩
  · rintro ⟨⟨⟨hn,hX⟩,hO⟩,hN⟩
    exact ⟨hn,hX,hO,by by_contra! h; exact hN ⟨⟨hn,by omega⟩,hO⟩⟩

private theorem mobius_double (n : ℕ) : muR (2*n) = if Odd n then -muR n else 0 := by
  by_cases hn : Odd n
  · rw [if_pos hn]
    have h := isMultiplicative_moebius.map_mul_of_coprime (Nat.coprime_two_left.mpr hn)
    rw [moebius_apply_prime Nat.prime_two,neg_one_mul] at h
    change (moebius (2*n):ℝ) = -(moebius n:ℝ)
    exact_mod_cast h
  · rw [if_neg hn]
    obtain ⟨k,hk⟩ := Nat.not_odd_iff_even.mp hn
    have hd : 2*2 ∣ 2*n := ⟨k,by rw [hk]; ring⟩
    have hsq : ¬Squarefree (2*n) := fun h =>
      (Nat.squarefree_iff_prime_squarefree.mp h 2 Nat.prime_two) hd
    change (moebius (2*n):ℝ) = 0
    exact_mod_cast moebius_eq_zero_of_not_squarefree hsq

private theorem even_up_to_image (X : ℕ) :
    (Finset.Icc 1 X).filter (fun n => ¬ Odd n) =
      (Finset.Icc 1 (X/2)).image (fun n => 2*n) := by
  ext n
  simp only [mem_filter,Finset.mem_Icc,Finset.mem_image,Nat.not_odd_iff_even]
  constructor
  · rintro ⟨⟨hn,hX⟩,⟨k,hk⟩⟩
    exact ⟨k,⟨by omega,by omega⟩,by omega⟩
  · rintro ⟨k,⟨hk,hkX⟩,rfl⟩
    exact ⟨⟨by omega,by omega⟩,⟨k,by ring⟩⟩

theorem odd_shell_sum_eq_M (X : ℕ) : ∑ n ∈ upperOddShell X, muR n = M X := by
  classical
  have hodd : oddUpTo (X/2) ⊆ oddUpTo X := by
    intro n hn
    have h := mem_filter.mp hn
    exact mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp h.1).1,by have := (Finset.mem_Icc.mp h.1).2; omega⟩,h.2⟩
  have hSplit : (∑ n ∈ Finset.Icc 1 X, muR n) =
      (∑ n ∈ oddUpTo X, muR n) + ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬Odd n), muR n := by
    symm
    exact sum_filter_add_sum_filter_not (Finset.Icc 1 X) Odd _
  have hEven : (∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ Odd n),muR n) =
      -∑ n ∈ oddUpTo (X/2),muR n := by
    rw [even_up_to_image,sum_image (show Function.Injective (fun n : ℕ => 2*n) from
      fun l k h => by change 2*l=2*k at h; omega).injOn]
    simp_rw [mobius_double]
    rw [← sum_filter]
    simp only [oddUpTo,sum_neg_distrib]
  have hI : Finset.Ioc (0:ℕ) X = Finset.Icc 1 X := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hD : (∑ n ∈ oddUpTo X \ oddUpTo (X/2),muR n) +
      (∑ n ∈ oddUpTo (X/2),muR n) = ∑ n ∈ oddUpTo X,muR n := sum_sdiff hodd
  rw [upper_odd_shell_eq_sdiff,M,hI,hSplit,hEven]
  linarith

theorem balanced_complement_sum_eq_M {X : ℕ} {A : Finset ℕ} (hA : A ⊆ upperOddShell X)
    (hzero : ∑ n ∈ A, muR n = 0) :
    ∑ n ∈ upperOddShell X \ A, muR n = M X := by
  have he : (∑ n ∈ upperOddShell X \ A,muR n)+(∑ n ∈ A,muR n) =
      ∑ n ∈ upperOddShell X,muR n := sum_sdiff hA
  rwa [hzero,add_zero,odd_shell_sum_eq_M] at he

end RHConnections.ArithmeticFourierShell
