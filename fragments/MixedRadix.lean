import Verified
import RadixFloor

open ArithmeticFunction
noncomputable section
namespace RHConnections.MixedRadix
open ArithmeticFourierInversion ArithmeticFourierMertensKernel

def weight (k : ℕ) : ℝ := ((k%2:ℕ):ℝ)/2+((k%3:ℕ):ℝ)/2

def column (t n : ℕ) : ℝ :=
  weight (t/n)+(if 3≤t ∧ n=1 then (3:ℝ)/2 else 0)

theorem mixed_column_at_two (n : ℕ) : column 2 n = floorTest 2 n := by
  rw [floor_test_parity,column,weight]
  by_cases hn : n=1
  · subst n
    norm_num
  · have hq : 2/n<2 := by
      by_cases hz : n=0
      · simp [hz]
      · exact (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hz)).mpr (by omega)
    interval_cases h : 2/n <;> norm_num [hn,h]

theorem mixed_column_of_three_le (t n : ℕ) (ht : 3≤t) :
    column t n = (RadixFloor.test 2 t n+RadixFloor.test 3 t n)/2 := by
  rw [RadixFloor.test_mod,RadixFloor.test_mod,column,weight]
  by_cases hn : n=1 <;> simp [ht,hn] <;> ring

theorem mixed_column_mobius_orthogonal (N t : ℕ) (ht : 2≤t) (hN : t≤N) :
    dot N muR (column t) = 0 := by
  by_cases h2 : t=2
  · subst t
    rw [funext mixed_column_at_two]
    exact floor_test_mobius_orthogonal N 2 ht hN
  · have h3 : 3≤t := by omega
    have h₂ := RadixFloor.radix_test_mobius_orthogonal (r := 2) (by norm_num) ht hN
    have h₃ := RadixFloor.radix_test_mobius_orthogonal (r := 3) (by norm_num) h3 hN
    unfold dot at *
    simp only [mixed_column_of_three_le _ _ h3]
    have hpoint (n : ℕ) : muR n*((RadixFloor.test 2 t n+RadixFloor.test 3 t n)/2) =
        (muR n*RadixFloor.test 2 t n+muR n*RadixFloor.test 3 t n)/2 := by ring
    simp only [hpoint,← Finset.sum_div,Finset.sum_add_distrib,h₂,h₃,add_zero,zero_div]

private theorem mixed_diag {t : ℕ} (ht : 1<t) : column t t=1 := by
  have hn : t≠1 := by omega
  norm_num [column,weight,Nat.div_self (by omega : 0<t),hn]

private theorem mixed_above {t n : ℕ} (ht : 1<t) (hn : t<n) : column t n=0 := by
  simp [column,weight,Nat.div_eq_of_lt hn,show n≠1 by omega]

noncomputable def coefficients : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, _ => 0
  | N+1, G => fun t =>
    if t=N+1 then G (N+1)
    else coefficients N (fun n => G n-G (N+1)*column (N+1) n) t

theorem mixed_coefficients_reconstruct_tail (N : ℕ) (G : ℕ → ℝ) :
    ∀ n ∈ Finset.Ioc 1 N,
      G n=∑ t ∈ Finset.Ioc 1 N,coefficients N G t*column t n := by
  induction N generalizing G with
  | zero => simp
  | succ N ih =>
    by_cases hN : N=0
    · subst N
      simp
    have hN1 : 1≤N := Nat.one_le_iff_ne_zero.mpr hN
    intro n hn
    let R := fun q => G q-G (N+1)*column (N+1) q
    obtain ⟨hn1,hnN⟩ := Finset.mem_Ioc.mp hn
    rw [Finset.sum_Ioc_succ_top hN1]
    have hlow : (∑ t ∈ Finset.Ioc 1 N,coefficients (N+1) G t*column t n) =
        ∑ t ∈ Finset.Ioc 1 N,coefficients N R t*column t n := by
      refine Finset.sum_congr rfl (fun t ht => ?_)
      have hne : t≠N+1 := by have := (Finset.mem_Ioc.mp ht).2; omega
      simp [coefficients,hne,R]
    have htop : coefficients (N+1) G (N+1)=G (N+1) := by simp [coefficients]
    rw [hlow,htop]
    by_cases he : n=N+1
    · subst n
      rw [mixed_diag (by omega)]
      have hz : (∑ t ∈ Finset.Ioc 1 N,coefficients N R t*column t (N+1))=0 := by
        refine Finset.sum_eq_zero (fun t ht => ?_)
        obtain ⟨ht1,htN⟩ := Finset.mem_Ioc.mp ht
        rw [mixed_above ht1 (by omega),mul_zero]
      rw [hz,mul_one,zero_add]
    · rw [← ih R n (Finset.mem_Ioc.mpr ⟨hn1,by omega⟩)]
      dsimp only [R]
      ring

theorem mixed_coefficients_reconstruct (N : ℕ) (hN : 0<N) (G : ℕ → ℝ)
    (hG : dot N muR G=0) :
    ∀ n ∈ Finset.Ioc 0 N,
      G n=∑ t ∈ Finset.Ioc 1 N,coefficients N G t*column t n := by
  let V := fun n => ∑ t ∈ Finset.Ioc 1 N,coefficients N G t*column t n
  have hV : dot N muR V=0 := by
    unfold dot V
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t ht
    have h := mixed_column_mobius_orthogonal N t (by have := (Finset.mem_Ioc.mp ht).1; omega)
      (Finset.mem_Ioc.mp ht).2
    calc
      _ = coefficients N G t*dot N muR (column t) := by
        rw [dot,Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = 0 := by rw [h,mul_zero]
  have he : ∀ n>1, n≤N → G n=V n :=
    fun n hl hu => mixed_coefficients_reconstruct_tail N G n (Finset.mem_Ioc.mpr ⟨hl,hu⟩)
  intro n hn
  change G n=V n
  by_cases h1 : n=1
  · subst n
    have hsum : (∑ n ∈ Finset.Ioc 0 N,muR n*(G n-V n))=0 := by
      rw [show (∑ n ∈ Finset.Ioc 0 N,muR n*(G n-V n))=dot N muR G-dot N muR V by
        simp only [dot,mul_sub,Finset.sum_sub_distrib],hG,hV,sub_self]
    rw [Finset.sum_eq_single 1] at hsum
    · simpa [muR,sub_eq_zero] using hsum
    · intro j hj hne
      obtain ⟨hj₀,hjN⟩ := Finset.mem_Ioc.mp hj
      rw [he j (by omega) hjN,sub_self,mul_zero]
    · intro h; exact (h (Finset.mem_Ioc.mpr ⟨Nat.zero_lt_one,hN⟩)).elim
  · obtain ⟨hn₀,hnN⟩ := Finset.mem_Ioc.mp hn
    exact he n (by omega) hnN

theorem mixed_coefficient_descending_rule (N t : ℕ) (ht : 1<t) (hN : t≤N) (G : ℕ → ℝ) :
    coefficients N G t =
      G t - ∑ s ∈ Finset.Ioc t N,coefficients N G s*weight (s/t) := by
  let a := coefficients N G
  let f := fun s => a s*column s t
  have hs : (∑ s ∈ Finset.Icc t N,f s) = ∑ s ∈ Finset.Ioc 1 N,f s := by
    refine Finset.sum_subset (fun s hs => Finset.mem_Ioc.mpr
      ⟨ht.trans_le (Finset.mem_Icc.mp hs).1,(Finset.mem_Icc.mp hs).2⟩) (fun s hs hnot => ?_)
    have hu := (Finset.mem_Ioc.mp hs).2
    have hlt : s<t := by
      by_contra! h
      exact hnot (Finset.mem_Icc.mpr ⟨h,hu⟩)
    unfold f
    rw [mixed_above (Finset.mem_Ioc.mp hs).1 hlt,mul_zero]
  have hI : insert t (Finset.Ioc t N) = Finset.Icc t N := by
    ext s
    simp only [Finset.mem_insert,Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hn : t∉Finset.Ioc t N := fun h => (lt_irrefl t) (Finset.mem_Ioc.mp h).1
  have h := mixed_coefficients_reconstruct_tail N G t (Finset.mem_Ioc.mpr ⟨ht,hN⟩)
  change G t = ∑ s ∈ Finset.Ioc 1 N,f s at h
  rw [← hs,← hI,Finset.sum_insert hn] at h
  have ht' : t≠1 := by omega
  have hcol (s : ℕ) : f s = a s*weight (s/t) := by simp [f,column,ht']
  simp only [hcol] at h
  have hm : weight (t/t)=1 := by rw [Nat.div_self (by omega)]; norm_num [weight]
  rw [hm,mul_one] at h
  change a t = _
  linarith only [h]

end RHConnections.MixedRadix
