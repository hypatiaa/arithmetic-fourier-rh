import Verified

open ArithmeticFunction
noncomputable section
namespace RHConnections.RadixFloor
open ArithmeticFourierInversion ArithmeticFourierMertensKernel

def test (r t n : ℕ) : ℝ :=
  ((t/n:ℕ):ℝ)-(r:ℝ)*((t/(r*n):ℕ):ℝ)+(if n=1 then (r:ℝ)-1 else 0)

theorem test_mod (r t n : ℕ) :
    test r t n = ((t/n%r:ℕ):ℝ)+(if n=1 then (r:ℝ)-1 else 0) := by
  have h := Nat.mod_add_div (t/n) r
  have hc : ((t/n%r:ℕ):ℝ)+(r:ℝ)*((t/n/r:ℕ):ℝ)=((t/n:ℕ):ℝ) := by exact_mod_cast h
  have hd : t/(r*n) = t/n/r := by rw [Nat.div_div_eq_div_mul,mul_comm n r]
  unfold test
  rw [hd]
  linarith only [hc]

private theorem floor_mobius_exact {m N : ℕ} (hm : 0<m) (hN : m≤N) :
    (∑ n ∈ Finset.Ioc 0 N,muR n*((m/n:ℕ):ℝ)) = 1 := by
  have hsub : Finset.Ioc (0:ℕ) m ⊆ Finset.Ioc 0 N := fun n hn =>
    Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,(Finset.mem_Ioc.mp hn).2.trans hN⟩
  have he : (∑ n ∈ Finset.Ioc 0 m,muR n*((m/n:ℕ):ℝ)) =
      ∑ n ∈ Finset.Ioc 0 N,muR n*((m/n:ℕ):ℝ) := by
    refine Finset.sum_subset hsub (fun n hn hnot => ?_)
    have hn0 := (Finset.mem_Ioc.mp hn).1
    have hlt : m<n := by
      by_contra! h
      exact hnot (Finset.mem_Ioc.mpr ⟨hn0,h⟩)
    rw [Nat.div_eq_of_lt hlt,Nat.cast_zero,mul_zero]
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum muR m
  rw [show muR*(↑ArithmeticFunction.zeta:ArithmeticFunction ℝ)=1 from
    coe_moebius_mul_coe_zeta,he] at h
  rw [← h]
  simp [ArithmeticFunction.one_apply,hm.ne']

theorem radix_test_mobius_orthogonal {r t N : ℕ} (hr : 0<r) (ht : r≤t) (hN : t≤N) :
    dot N muR (test r t) = 0 := by
  have h₁ := floor_mobius_exact (hr.trans_le ht) hN
  have h₂ := floor_mobius_exact (Nat.div_pos ht hr) ((Nat.div_le_self t r).trans hN)
  have hδ : (∑ n ∈ Finset.Ioc 0 N,muR n*(if n=1 then (r:ℝ)-1 else 0)) = (r:ℝ)-1 := by
    rw [Finset.sum_eq_single 1]
    · simp [muR]
    · intro n _ hn; simp [hn]
    · intro h; exact (h (Finset.mem_Ioc.mpr ⟨Nat.zero_lt_one,by omega⟩)).elim
  have hd (n : ℕ) : t/(r*n)=t/r/n := by rw [Nat.div_div_eq_div_mul]
  simp only [dot,test,hd,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hm : (∑ n ∈ Finset.Ioc 0 N,muR n*((r:ℝ)*((t/r/n:ℕ):ℝ))) = (r:ℝ) := by
    calc
      _ = (r:ℝ)*∑ n ∈ Finset.Ioc 0 N,muR n*((t/r/n:ℕ):ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by rw [h₂,mul_one]
  rw [h₁,hm,hδ]
  ring

def radixFactor (r : ℕ) (s : ℂ) : ℂ := 1 - (r:ℂ)^(1-s)

private theorem radix_zero_frequency {r : ℕ} (hr : 0<r) {y : ℝ}
    (h : radixFactor r (1+(y:ℂ)*Complex.I)=0) :
    ∃ k : ℤ, -(y*Real.log r)=(k:ℝ)*(2*Real.pi) := by
  have hb : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  have hv : (r:ℂ)^(1-(1+(y:ℂ)*Complex.I))=1 := (sub_eq_zero.mp h).symm
  rw [Complex.cpow_def_of_ne_zero hb] at hv
  obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp hv
  refine ⟨k,?_⟩
  have hkc := congrArg Complex.im hk
  have hl : Complex.log (r:ℂ) = (Real.log (r:ℝ):ℂ) := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_log (Nat.cast_nonneg _)]
  rw [hl] at hkc
  simp only [Complex.mul_im,Complex.mul_re,Complex.sub_im,Complex.sub_re,Complex.add_re,
    Complex.add_im,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,Complex.ofReal_im,
    Complex.ofReal_re,Complex.natCast_re,Complex.natCast_im,Complex.intCast_re,Complex.intCast_im] at hkc
  norm_num at hkc
  simpa using (show -(y*Real.log r)=(k:ℝ)*(2*Real.pi) by linear_combination hkc)

theorem binary_ternary_no_common_radix_zero {y : ℝ} (hy : y≠0) :
    radixFactor 2 (1+(y:ℂ)*Complex.I)≠0 ∨ radixFactor 3 (1+(y:ℂ)*Complex.I)≠0 := by
  by_contra! hz
  obtain ⟨k,hk⟩ := radix_zero_frequency (r := 2) (by norm_num) hz.1
  obtain ⟨l,hl⟩ := radix_zero_frequency (r := 3) (by norm_num) hz.2
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0<Real.log 3 := Real.log_pos (by norm_num)
  have hk0 : k≠0 := by
    intro h
    rw [h,Int.cast_zero,zero_mul,neg_eq_zero,mul_eq_zero] at hk
    exact hk.elim hy h2.ne'
  have hcancel : y*((l:ℝ)*Real.log 2-(k:ℝ)*Real.log 3)=0 := by
    linear_combination -(l:ℝ)*hk+(k:ℝ)*hl
  have he := sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left hy)
  have heabs := congrArg abs he
  rw [abs_mul,abs_mul,abs_of_pos h2,abs_of_pos h3] at heabs
  have habs (j : ℤ) : |(j:ℝ)| = (j.natAbs:ℝ) := by
    rw [← Int.cast_abs,← Int.natCast_natAbs]
    norm_num
  rw [habs,habs,← Real.log_pow,← Real.log_pow] at heabs
  have hn : (2:ℝ)^l.natAbs = (3:ℝ)^k.natAbs :=
    Real.log_injOn_pos (by change (0:ℝ)<2^l.natAbs; positivity)
      (by change (0:ℝ)<3^k.natAbs; positivity) heabs
  have hnn : (2:ℕ)^l.natAbs = (3:ℕ)^k.natAbs := by exact_mod_cast hn
  have hl0 : l≠0 := by
    intro h
    rw [h,Int.cast_zero,zero_mul,neg_eq_zero,mul_eq_zero] at hl
    exact hl.elim hy h3.ne'
  have hd : 2 ∣ (3:ℕ)^k.natAbs := by
    rw [← hnn]
    exact dvd_pow_self _ ((Int.natAbs_pos.mpr hl0).ne')
  have := Nat.prime_two.dvd_of_dvd_pow hd
  norm_num at this

end RHConnections.RadixFloor
