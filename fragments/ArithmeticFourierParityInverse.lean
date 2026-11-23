import Verified

open ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierMertensKernel
open ArithmeticFourierInversion

def parityFloor (L n : ℕ) : ℝ := ((L/n%2:ℕ):ℝ)

private theorem floor_even_split (L n j : ℕ) :
    ((L/2^j/n:ℕ):ℝ) =
      parityFloor (L/2^j) n + 2*((L/2^(j+1)/n:ℕ):ℝ) := by
  have hd : L/2^j/n/2 = L/2^(j+1)/n := by
    simp only [Nat.div_div_eq_div_mul,pow_succ]
    rw [mul_assoc (2^j) n 2,mul_comm n 2,← mul_assoc]
  have h := Nat.mod_add_div (L/2^j/n) 2
  unfold parityFloor
  rw [← hd]
  exact_mod_cast h.symm

theorem floor_parity_telescoping (L n J : ℕ) :
    (∑ j ∈ Finset.range J,(2:ℝ)^j*parityFloor (L/2^j) n) =
      ((L/n:ℕ):ℝ)-(2:ℝ)^J*((L/2^J/n:ℕ):ℝ) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ,ih,pow_succ (2:ℝ)]
    linear_combination -(2:ℝ)^J*(floor_even_split L n J)

private theorem below_next_two_power (L : ℕ) : L < 2^(L+1) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [show L.succ+1=(L+1)+1 by rfl,pow_succ]
    omega

private theorem mobius_floor_indicator (L n : ℕ) (hn : 0<n) :
    (∑ k ∈ Finset.Ioc 0 L,muR k*((L/k/n:ℕ):ℝ)) = if n≤L then 1 else 0 := by
  have he (k : ℕ) : L/k/n = L/n/k := by
    rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,mul_comm k n]
  simp only [he]
  have hsub : Finset.Ioc (0:ℕ) (L/n) ⊆ Finset.Ioc 0 L := fun k hk =>
    Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hk).1,(Finset.mem_Ioc.mp hk).2.trans (Nat.div_le_self _ _)⟩
  have hsum : (∑ k ∈ Finset.Ioc 0 (L/n),muR k*((L/n/k:ℕ):ℝ)) =
      ∑ k ∈ Finset.Ioc 0 L,muR k*((L/n/k:ℕ):ℝ) := by
    apply Finset.sum_subset hsub
    intro k hk hnmem
    have hlt : L/n<k := by
      by_contra! h
      exact hnmem (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hk).1,h⟩)
    rw [Nat.div_eq_of_lt hlt,Nat.cast_zero,mul_zero]
  have hs := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum muR (L/n)
  rw [show muR*(↑ArithmeticFunction.zeta:ArithmeticFunction ℝ)=1 from
    coe_moebius_mul_coe_zeta,hsum] at hs
  rw [← hs]
  by_cases h : n≤L
  · have hp := Nat.div_pos h hn
    simp [ArithmeticFunction.one_apply,h,hp.ne']
  · have hz : L/n=0 := Nat.div_eq_of_lt (lt_of_not_ge h)
    simp [hz,h]

theorem prefix_parity_expansion (L n : ℕ) (hn : 0<n) :
    (∑ k ∈ Finset.Ioc 0 L,∑ j ∈ Finset.range (L+1),
      muR k*(2:ℝ)^j*parityFloor (L/k/2^j) n) = if n≤L then 1 else 0 := by
  rw [← mobius_floor_indicator L n hn]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [mul_assoc]
  rw [← Finset.mul_sum,floor_parity_telescoping]
  have hsmall := (Nat.div_le_self L k).trans_lt (below_next_two_power L)
  rw [Nat.div_eq_of_lt hsmall]
  simp

def prefixCoefficient (L t : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 L,∑ j ∈ Finset.range (L+1),
    if L/k/2^j=t then muR k*(2:ℝ)^j else 0

theorem prefix_grouped_parity_expansion (L n : ℕ) (hn : 0<n) :
    (∑ t ∈ Finset.Icc 0 L,prefixCoefficient L t*parityFloor t n) =
      if n≤L then 1 else 0 := by
  rw [← prefix_parity_expansion L n hn]
  unfold prefixCoefficient
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hs (t : ℕ) : ((if L/k/2^j=t then muR k*(2:ℝ)^j else 0)*parityFloor t n) =
      if L/k/2^j=t then muR k*(2:ℝ)^j*parityFloor t n else 0 := by
    split_ifs <;> simp
  simp only [hs,Finset.sum_ite_eq]
  rw [ite_eq_left (Finset.mem_Icc.mpr ⟨Nat.zero_le _,
    (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)⟩)]

private theorem singleton_quotient_fibre {L d t m : ℕ} (hd : 0<d)
    (hdt : d<t) (hm : 0<m) (hL : L=d*t) :
    L/m=t ↔ m=d := by
  constructor
  · intro h
    have htop := (Nat.div_lt_iff_lt_mul hm).mp (show L/m<t+1 by omega)
    have hbottom := (Nat.le_div_iff_mul_le hm).mp h.ge
    rw [hL] at htop hbottom
    by_contra! hne
    rcases lt_or_gt_of_ne hne with hlt|hlt
    · have hu := Nat.mul_le_mul_left (t+1) (show m+1≤d by omega)
      nlinarith only [hu,htop,hdt]
    · have hu := Nat.mul_le_mul_left t (show d+1≤m by omega)
      nlinarith only [hu,hbottom,hdt,hd]
  · rintro rfl
    rw [hL,mul_comm]
    exact Nat.mul_div_cancel _ hd

theorem power_two_prefix_coefficient (r : ℕ) (hr : 0<r) :
    prefixCoefficient (2^(2*r+2)) (2^(r+2)) = (2:ℝ)^(r-1) := by
  let L : ℕ := 2^(2*r+2)
  let t : ℕ := 2^(r+2)
  let d : ℕ := 2^r
  have hdt : d<t := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hd : 0<d := by unfold d; positivity
  have hL : L=d*t := by
    dsimp [L,d,t]
    rw [← pow_add]
    congr 1
    omega
  have h2L : 2≤L := by
    change 2^1≤2^(2*r+2)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrL : r≤L := by
    have h1 := below_next_two_power r
    have h2 : 2^(r+1)≤L := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hf (k j : ℕ) (hk : 0<k) : L/k/2^j=t ↔ k*2^j=d := by
    rw [Nat.div_div_eq_div_mul]
    exact singleton_quotient_fibre hd hdt (by positivity) hL
  let U : Finset (ℕ × ℕ) := {(1,r),(2,r-1)}
  let V := (Finset.Ioc 0 L).product (Finset.range (L+1))
  let f := fun p : ℕ × ℕ => if L/p.1/2^p.2=t then muR p.1*(2:ℝ)^p.2 else 0
  have hsub : U ⊆ V := by
    intro p hp
    simp only [U,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl <;>
      exact Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,by omega⟩,
        Finset.mem_range.mpr (by omega)⟩
  have hsum := Finset.sum_subset (f := f) hsub (fun p hp hn => by
    obtain ⟨hk,_⟩ := Finset.mem_product.mp hp
    have hk0 := (Finset.mem_Ioc.mp hk).1
    unfold f
    split_ifs with hq
    · have hprod := (hf p.1 p.2 hk0).mp hq
      have hdiv : p.1∣2^r := ⟨2^p.2,hprod.symm⟩
      obtain ⟨a,_,ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
      rw [ha,← pow_add] at hprod
      have hex : a+p.2=r := Nat.pow_right_injective (by norm_num : 2≤2) hprod
      by_cases h0 : a=0
      · have he : p = (1,r) := Prod.ext (by simpa [h0] using ha) (by omega)
        exact (hn (by simp [U,he])).elim
      by_cases h1 : a=1
      · have he : p = (2,r-1) := Prod.ext (by simpa [h1] using ha) (by omega)
        exact (hn (by simp [U,he])).elim
      · change (moebius p.1:ℝ)*2^p.2 = 0
        rw [ha,moebius_apply_prime_pow Nat.prime_two h0,ite_eq_right h1,Int.cast_zero,zero_mul]
    · rfl)
  change prefixCoefficient L t = _
  change (∑ k ∈ Finset.Ioc 0 L,∑ j ∈ Finset.range (L+1), f (k,j)) = _
  rw [← Finset.sum_product]
  change (∑ p ∈ V,f p) = _
  rw [← hsum]
  have he1 : L/1/2^r=t := (hf _ _ (by norm_num)).mpr (by simp [d])
  have he2 : L/2/2^(r-1)=t := (hf _ _ (by norm_num)).mpr (by
    rw [mul_comm,← pow_succ]
    congr 1
    omega)
  have hp : (1,r) ∉ ({(2,r-1)} : Finset (ℕ×ℕ)) := by
    rw [Finset.mem_singleton]
    intro h
    have := congrArg Prod.fst h
    norm_num at this
  simp only [U,Finset.sum_insert hp,Finset.sum_singleton,f,ite_eq_left he1,ite_eq_left he2]
  have hm1 : muR 1=1 := by simp [muR]
  have hm2 : muR 2= -1 := by
    change (moebius 2:ℝ)= -1
    rw [moebius_apply_prime Nat.prime_two]
    norm_num
  have hexp : (2:ℝ)^r = 2^(r-1)*2 := by
    rw [← pow_succ,show r-1+1=r by omega]
  rw [hm1,hm2,hexp]
  ring

theorem power_two_prefix_coefficient_sqrt (r : ℕ) (hr : 0<r) :
    prefixCoefficient (2^(2*r+2)) (2^(r+2)) = Real.sqrt (((2:ℕ)^(2*r+2)):ℝ)/4 := by
  rw [power_two_prefix_coefficient r hr]
  have hd : (((2:ℕ)^(2*r+2)):ℝ) = ((2:ℝ)^(r+1))^2 := by
    rw [← pow_mul,show 2*r+2=(r+1)*2 by omega]
    rfl
  have he : (2:ℝ)^(r+1) = 2^(r-1)*4 := by
    rw [← show (2:ℝ)^2 = 4 by norm_num,← pow_add]
    congr 1
    omega
  rw [hd,Real.sqrt_sq (by positivity),he]
  ring

theorem centered_prefix_expansion (N L : ℕ) (hN : 0<N) (hL : L≤N) :
    ∀ n ∈ Finset.Ioc 0 N,
      (if n≤L then (1:ℝ) else 0) =
        (∑ t ∈ Finset.Ioc 1 L,prefixCoefficient L t*floorTest t n) +
          if n=1 then M L else 0 := by
  classical
  let G := fun n => ∑ t ∈ Finset.Ioc 1 L,prefixCoefficient L t*floorTest t n
  let H := fun n : ℕ => if n≤L then (1:ℝ) else 0
  have he_tail (n : ℕ) (hn : 1<n) : H n=G n := by
    unfold H G
    rw [← prefix_grouped_parity_expansion L n (by omega)]
    symm
    calc
      _ = ∑ t ∈ Finset.Ioc 1 L,prefixCoefficient L t*parityFloor t n := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [floor_test_parity,ite_eq_right (by omega : n≠1),add_zero]
        rfl
      _ = _ := by
        apply Finset.sum_subset
        · intro t ht
          exact Finset.mem_Icc.mpr ⟨Nat.zero_le _ ,(Finset.mem_Ioc.mp ht).2⟩
        · intro t ht hnot
          have ht1 : t≤1 := by
            by_contra! h
            exact hnot (Finset.mem_Ioc.mpr ⟨h,(Finset.mem_Icc.mp ht).2⟩)
          rw [parityFloor,Nat.div_eq_of_lt (ht1.trans_lt hn)]
          norm_num
  have hg : dot N muR G = 0 := by
    unfold dot G
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t ht
    have h := floor_test_mobius_orthogonal N t (by have := (Finset.mem_Ioc.mp ht).1; omega)
      ((Finset.mem_Ioc.mp ht).2.trans hL)
    calc
      _ = prefixCoefficient L t*dot N muR (floorTest t) := by
        rw [dot,Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = 0 := by rw [h,mul_zero]
  have hh : dot N muR H = M L := by
    unfold dot H M
    simp only [mul_ite,mul_one,mul_zero,← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter,Finset.mem_Ioc]
    omega
  have hgap : H 1-G 1=M L := by
    have hsum : dot N muR H-dot N muR G =
        ∑ n ∈ Finset.Ioc 0 N,muR n*(H n-G n) := by
      simp only [dot,mul_sub,Finset.sum_sub_distrib]
    rw [hh,hg,sub_zero,Finset.sum_eq_single 1] at hsum
    · simpa [muR] using hsum.symm
    · intro n hn hn1
      have hn0 := (Finset.mem_Ioc.mp hn).1
      rw [he_tail n (by omega),sub_self,mul_zero]
    · intro h
      exact (h (Finset.mem_Ioc.mpr ⟨Nat.zero_lt_one,hN⟩)).elim
  intro n hn
  change H n=G n+(if n=1 then M L else 0)
  by_cases h : n=1
  · simpa only [h,ite_true] using (eq_add_of_sub_eq hgap).trans (add_comm _ _)
  · rw [ite_eq_right h,add_zero]
    exact he_tail n (by have := (Finset.mem_Ioc.mp hn).1; omega)

end RHConnections.ArithmeticFourierMertensKernel
