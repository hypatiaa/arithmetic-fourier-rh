import Verified

open ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierMertensKernel
open ArithmeticFourierInversion

def dot (N : ℕ) (u v : ℕ → ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 N, u n*v n

def sqNorm (N : ℕ) (u : ℕ → ℝ) : ℝ := dot N u u

theorem sqNorm_nonneg (N : ℕ) (u : ℕ → ℝ) : 0 ≤ sqNorm N u := by
  unfold sqNorm dot
  exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

theorem square_completion (N : ℕ) (mu K G : ℕ → ℝ) (t : ℝ) (hG : dot N mu G = 0) :
    sqNorm N (fun n => K n-G n-t*mu n) =
      sqNorm N (fun n => K n-G n)+t^2*sqNorm N mu-2*t*dot N mu K := by
  have hpoint (n : ℕ) : (K n-G n-t*mu n)*(K n-G n-t*mu n) =
      (K n-G n)*(K n-G n)+t^2*(mu n*mu n)-2*t*(mu n*K n)+2*t*(mu n*G n) := by ring
  unfold sqNorm dot at *
  simp only [hpoint,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,hG,mul_zero,add_zero]

theorem correction_projection (N : ℕ) (mu K : ℕ → ℝ) (hmu : 0 < sqNorm N mu) :
    let c := dot N mu K / sqNorm N mu
    let G := fun n => K n-c*mu n
    dot N mu G = 0 ∧
      sqNorm N (fun n => K n-G n) = (dot N mu K)^2 / sqNorm N mu := by
  let c := dot N mu K / sqNorm N mu
  change dot N mu (fun n => K n-c*mu n) = 0 ∧
    sqNorm N (fun n => K n-(K n-c*mu n)) = _
  have hdot : dot N mu (fun n => K n-c*mu n) = dot N mu K - c*sqNorm N mu := by
    simp only [dot,sqNorm,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring
  refine ⟨?_,?_⟩
  · rw [hdot,show c*sqNorm N mu = dot N mu K from div_mul_cancel₀ _ hmu.ne',sub_self]
  · calc
      _ = c^2*sqNorm N mu := by
        simp only [sqNorm,dot,sub_sub_cancel,Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by dsimp only [c]; field_simp

theorem correction_lower_bound (N : ℕ) (mu K G : ℕ → ℝ)
    (hmu : 0 < sqNorm N mu) (hG : dot N mu G = 0) :
    (dot N mu K)^2 / sqNorm N mu ≤ sqNorm N (fun n => K n-G n) := by
  have h := sqNorm_nonneg N (fun n => K n-G n-(dot N mu K / sqNorm N mu)*mu n)
  rw [square_completion N mu K G _ hG] at h
  apply (div_le_iff₀ hmu).mpr
  have hh := mul_nonneg h hmu.le
  field_simp at hh
  nlinarith only [hh]

def floorTest (t n : ℕ) : ℝ :=
  ((t/n:ℕ):ℝ) - 2*((t/(2*n):ℕ):ℝ) + if n=1 then 1 else 0

theorem floor_test_parity (t n : ℕ) :
    floorTest t n = ((t/n%2:ℕ):ℝ) + if n=1 then 1 else 0 := by
  have hd : t/(2*n) = t/n/2 := by rw [Nat.div_div_eq_div_mul,mul_comm n 2]
  have he := Nat.mod_add_div (t/n) 2
  have hcast : ((t/n%2:ℕ):ℝ)+2*((t/n/2:ℕ):ℝ)=((t/n:ℕ):ℝ) := by exact_mod_cast he
  unfold floorTest
  rw [hd]
  linarith only [hcast]

private theorem floor_test_at_top {t : ℕ} (ht : 1<t) : floorTest t t=1 := by
  rw [floor_test_parity,Nat.div_self (by omega),ite_eq_right (by omega)]
  norm_num

private theorem floor_test_above_top {t n : ℕ} (ht : 1<t) (hn : t<n) : floorTest t n=0 := by
  rw [floor_test_parity,Nat.div_eq_of_lt hn,ite_eq_right (by omega)]
  norm_num

private theorem mobius_floor_sum (t : ℕ) (ht : 0<t) :
    (∑ n ∈ Finset.Ioc 0 t, muR n*((t/n:ℕ):ℝ)) = 1 := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum muR t
  rw [show muR * (↑ArithmeticFunction.zeta:ArithmeticFunction ℝ)=1 from
    ArithmeticFunction.coe_moebius_mul_coe_zeta] at h
  rw [← h]
  simp [ArithmeticFunction.one_apply,ht.ne']

private theorem extend_mobius_floor_sum {N t : ℕ} (ht : 0<t) (hN : t≤N) :
    (∑ n ∈ Finset.Ioc 0 N, muR n*((t/n:ℕ):ℝ)) = 1 := by
  rw [← mobius_floor_sum t ht]
  symm
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,(Finset.mem_Ioc.mp hn).2.trans hN⟩
  · intro n hn he
    have hlt : t < n := by
      by_contra! h
      exact he (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,h⟩)
    rw [Nat.div_eq_of_lt hlt,Nat.cast_zero,mul_zero]

theorem floor_test_mobius_orthogonal (N t : ℕ) (ht : 2≤t) (hN : t≤N) :
    dot N muR (floorTest t) = 0 := by
  have ht2 : 0<t/2 := Nat.div_pos (by omega) (by omega)
  have hhalf := extend_mobius_floor_sum ht2 ((Nat.div_le_self t 2).trans hN)
  have hall := extend_mobius_floor_sum (show 0<t by omega) hN
  have hδ : (∑ n ∈ Finset.Ioc 0 N, muR n*(if n=1 then (1:ℝ) else 0)) = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp [muR]
    · intro n _ hn; simp [hn]
    · intro h; exact (h (Finset.mem_Ioc.mpr ⟨by norm_num,by omega⟩)).elim
  have hd (n : ℕ) : t/(2*n) = (t/2)/n := by rw [Nat.div_div_eq_div_mul]
  simp only [dot,floorTest,hd,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have htwice :
      (∑ n ∈ Finset.Ioc 0 N, muR n*(2*((t/2/n:ℕ):ℝ))) =
      2*∑ n ∈ Finset.Ioc 0 N, muR n*((t/2/n:ℕ):ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hall,htwice,hhalf,hδ]
  ring

theorem floor_test_spans_tail (N : ℕ) (F : ℕ → ℝ) :
    ∃ a : ℕ → ℝ, ∀ n ∈ Finset.Ioc 1 N, F n=∑ t ∈ Finset.Ioc 1 N,a t*floorTest t n := by
  induction N generalizing F with
  | zero => exact ⟨0,by simp⟩
  | succ N ih =>
    by_cases hN : N=0
    · subst N
      exact ⟨0,by simp⟩
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    let c := F (N+1)
    let R := fun n => F n-c*floorTest (N+1) n
    obtain ⟨a,ha⟩ := ih R
    let b := fun t => if t=N+1 then c else a t
    refine ⟨b,?_⟩
    intro n hn
    have hr := Finset.mem_Ioc.mp hn
    have hbLast : b (N+1)=c := by simp [b]
    rw [Finset.sum_Ioc_succ_top hN1,hbLast]
    have hb : (∑ t ∈ Finset.Ioc 1 N,b t*floorTest t n) =
      ∑ t ∈ Finset.Ioc 1 N,a t*floorTest t n := by
      refine Finset.sum_congr rfl (fun t ht => ?_)
      have hne : t ≠ N+1 := by have := (Finset.mem_Ioc.mp ht).2; omega
      simp [b,hne]
    rw [hb]
    by_cases ht : n=N+1
    · subst n
      rw [floor_test_at_top (by omega)]
      have he : (∑ t ∈ Finset.Ioc 1 N,a t*floorTest t (N+1)) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp ht
        rw [floor_test_above_top hl (by omega),mul_zero]
      rw [he,mul_one,zero_add]
    · rw [← ha n (Finset.mem_Ioc.mpr ⟨hr.1,by omega⟩)]
      dsimp only [R]
      ring

theorem floor_tests_span_mobius_null (N : ℕ) (hN : 0<N) (F : ℕ → ℝ)
    (hF : dot N muR F=0) :
    ∃ a : ℕ → ℝ, ∀ n ∈ Finset.Ioc 0 N, F n=∑ t ∈ Finset.Ioc 1 N,a t*floorTest t n := by
  obtain ⟨a,ha⟩ := floor_test_spans_tail N F
  let G := fun n => ∑ t ∈ Finset.Ioc 1 N,a t*floorTest t n
  have hG : dot N muR G=0 := by
    unfold dot G
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t ht
    have h := floor_test_mobius_orthogonal N t (by have := (Finset.mem_Ioc.mp ht).1; omega)
      (Finset.mem_Ioc.mp ht).2
    calc
      _ = a t * dot N muR (floorTest t) := by
        rw [dot,Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = 0 := by rw [h,mul_zero]
  refine ⟨a,?_⟩
  intro n hn
  change F n=G n
  by_cases h1 : n=1
  · subst n
    have hsub : (Finset.Ioc (0:ℕ) N) \ {1} = Finset.Ioc 1 N := by
      ext n
      simp only [Finset.mem_sdiff,Finset.mem_singleton,Finset.mem_Ioc]
      omega
    have hone : ({1} : Finset ℕ) ⊆ Finset.Ioc 0 N := by
      intro n hn
      have h := Finset.mem_singleton.mp hn
      subst n
      exact Finset.mem_Ioc.mpr ⟨Nat.zero_lt_one,hN⟩
    have parts (V : ℕ → ℝ) : dot N muR V = (∑ n ∈ Finset.Ioc 1 N,muR n*V n)+V 1 := by
      unfold dot
      have h := (Finset.sum_sdiff (f := fun n => muR n*V n) hone).symm
      simpa [hsub,muR] using h
    rw [parts] at hF hG
    have htail : (∑ n ∈ Finset.Ioc 1 N,muR n*F n) = ∑ n ∈ Finset.Ioc 1 N,muR n*G n :=
      Finset.sum_congr rfl (fun n hn => by rw [ha n hn])
    linarith only [hF,hG,htail]
  · exact ha n (Finset.mem_Ioc.mpr ⟨by have := (Finset.mem_Ioc.mp hn).1; omega,(Finset.mem_Ioc.mp hn).2⟩)

end RHConnections.ArithmeticFourierMertensKernel
