import Verified

open Finset ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierShell
open ArithmeticFourierInversion

def increasingPairs (C : Finset ℕ) : Finset (ℕ × ℕ) :=
  (C.product C).filter (fun p => p.1 < p.2)

def longPairs (C : Finset ℕ) (H : ℕ) : Finset (ℕ × ℕ) :=
  (increasingPairs C).filter (fun p => p.1+2*H < p.2)

def shortPairs (C : Finset ℕ) (H : ℕ) : Finset (ℕ × ℕ) :=
  (increasingPairs C).filter (fun p => ¬ p.1+2*H < p.2)

def nonzeroMobius (C : Finset ℕ) : Finset ℕ := C.filter (fun n => muR n ≠ 0)

def shellLongContribution (X H y : ℕ) (C : Finset ℕ) : ℝ :=
  2*∑ p ∈ longPairs C H, muR p.1*muR p.2*fourierWeight X H y p.1 p.2

theorem sum_increasing_pairs (C : Finset ℕ) (f : ℕ → ℝ) :
    2*(∑ p ∈ increasingPairs C, f p.1*f p.2) =
      (∑ n ∈ C, f n)^2 - ∑ n ∈ C, (f n)^2 := by
  let V := fun l k => if l < k then f l*f k else 0
  let D := fun l k => if l = k then (f l)^2 else 0
  have hV : ∑ p ∈ increasingPairs C, f p.1*f p.2 = ∑ l ∈ C, ∑ k ∈ C, V l k := by
    simp [increasingPairs,sum_filter,sum_product,V]
  have hswap : (∑ l ∈ C,∑ k ∈ C, V k l) = ∑ l ∈ C,∑ k ∈ C,V l k := sum_comm
  have hD : (∑ l ∈ C,∑ k ∈ C,D l k) = ∑ l ∈ C,(f l)^2 := by
    apply sum_congr rfl
    intro l hl
    simp [D,hl]
  have hpoint (l k : ℕ) : f l*f k = D l k+V l k+V k l := by
    rcases lt_trichotomy l k with hl | rfl | hk
    · simp [D,V,hl,hl.ne,not_lt_of_ge hl.le]
    · simp [D,V,pow_two]
    · simp [D,V,hk,hk.ne',not_lt_of_ge hk.le,mul_comm]
  have hS : (∑ n ∈ C,f n)^2 = (∑ n ∈ C,(f n)^2)+2*(∑ l ∈ C,∑ k ∈ C,V l k) := by
    rw [pow_two, sum_mul]
    simp_rw [mul_sum,hpoint,sum_add_distrib]
    rw [hswap,hD]
    have htwo : (∑ l ∈ C,∑ k ∈ C, 2*V l k) = 2*(∑ l ∈ C,∑ k ∈ C, V l k) := by
      simp_rw [Finset.mul_sum]
    rw [htwo]
    ring
  rw [hV,hS]
  ring

private theorem shortPairs_card_le {C : Finset ℕ} (hC : ∀ n ∈ C, Odd n) (H : ℕ) :
    (shortPairs C H).card ≤ H*C.card := by
  let F : ℕ × ℕ → ℕ × ℕ := fun p => (p.1,(p.2-p.1)/2)
  have hp (p : ℕ × ℕ) (hm : p ∈ shortPairs C H) :
      p.1 ∈ C ∧ 1 ≤ (p.2-p.1)/2 ∧ (p.2-p.1)/2 ≤ H ∧ p.2=p.1+2*((p.2-p.1)/2) := by
    rcases p with ⟨l,k⟩
    obtain ⟨hInc,hshort⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmem,hlt⟩ := Finset.mem_filter.mp hInc
    have hl := (Finset.mem_product.mp hmem).1
    have hk := (Finset.mem_product.mp hmem).2
    obtain ⟨i,hi⟩ := hC l hl
    obtain ⟨j,hj⟩ := hC k hk
    exact ⟨hl,by omega,by omega,by omega⟩
  have hmap : Set.MapsTo F (shortPairs C H) (C.product (Finset.Icc 1 H)) := by
    intro p hm
    have h := hp p hm
    exact mem_product.mpr ⟨h.1,Finset.mem_Icc.mpr ⟨h.2.1,h.2.2.1⟩⟩
  have hinj : (shortPairs C H : Set (ℕ × ℕ)).InjOn F := by
    intro p hm q hn he
    apply Prod.ext
    · have h : (F p).1 = (F q).1 := congrArg Prod.fst he
      exact h
    · have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      change p.1=q.1 at h₁
      change (p.2-p.1)/2=(q.2-q.1)/2 at h₂
      have hp' := (hp p hm).2.2.2
      have hq' := (hp q hn).2.2.2
      omega
  have h := card_le_card_of_injOn F hmap hinj
  change (shortPairs C H).card ≤ (C.product (Finset.Icc 1 H)).card at h
  simpa [Finset.card_product,Nat.card_Icc,mul_comm] using h

private theorem muR_abs_le_one (n : ℕ) : |muR n| ≤ 1 := by
  change |(moebius n:ℝ)| ≤ 1
  exact_mod_cast (abs_moebius_le_one (n := n))

private theorem muR_sq_of_nonzero {n : ℕ} (hn : muR n ≠ 0) : (muR n)^2 = 1 := by
  have h : moebius n ≠ 0 := by
    change (moebius n:ℝ) ≠ 0 at hn
    exact_mod_cast hn
  have hq := moebius_sq_eq_one_of_squarefree (moebius_ne_zero_iff_squarefree.mp h)
  change (moebius n:ℝ)^2 = 1
  exact_mod_cast hq

private theorem nonzeroMobius_subset (C : Finset ℕ) : nonzeroMobius C ⊆ C := filter_subset _ _

private theorem long_pair_sum_filter_mobius (C : Finset ℕ) (H : ℕ) :
    ∑ p ∈ longPairs (nonzeroMobius C) H, muR p.1*muR p.2 =
      ∑ p ∈ longPairs C H, muR p.1*muR p.2 := by
  apply sum_subset
  · intro p hp
    obtain ⟨hInc,hlong⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hInc
    obtain ⟨h₁,h₂⟩ := mem_product.mp hp
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr
      ⟨nonzeroMobius_subset C h₁,nonzeroMobius_subset C h₂⟩,hlt⟩,hlong⟩
  · intro p hp hnot
    obtain ⟨hInc,hlong⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hInc
    obtain ⟨h₁,h₂⟩ := mem_product.mp hp
    by_contra hn
    obtain ⟨g₁,g₂⟩ := mul_ne_zero_iff.mp hn
    apply hnot
    exact mem_filter.mpr ⟨mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_filter.mpr ⟨h₁,g₁⟩,mem_filter.mpr ⟨h₂,g₂⟩⟩,hlt⟩,hlong⟩

theorem complement_long_pair_bound {X : ℕ} {A : Finset ℕ} (hA : A ⊆ upperOddShell X)
    (hzero : ∑ n ∈ A, muR n = 0) (H y : ℕ) :
    let C := upperOddShell X \ A
    |shellLongContribution X H y C - shellWeight H*(M X)^2| ≤
      shellWeight H*(1+2*(H:ℝ))*(nonzeroMobius C).card := by
  let C := upperOddShell X \ A
  let D := nonzeroMobius C
  let Q : ℝ := D.card
  let w := shellWeight H
  have hw : 0 ≤ w := sum_nonneg fun _ _ => by positivity
  have hD : D ⊆ C := nonzeroMobius_subset _
  have hC : C ⊆ upperOddShell X := Finset.sdiff_subset
  have hsum : ∑ n ∈ D, muR n = M X := by
    rw [← balanced_complement_sum_eq_M hA hzero]
    apply sum_subset hD
    intro n hn hnd
    by_contra hn'
    exact hnd (mem_filter.mpr ⟨hn,hn'⟩)
  have hsq : (∑ n ∈ D, (muR n)^2) = Q := by
    calc
      _ = ∑ _n ∈ D, (1:ℝ) := Finset.sum_congr rfl
        (fun _ hn => muR_sq_of_nonzero (Finset.mem_filter.mp hn).2)
      _ = _ := by simp [Q]
  have hAll := sum_increasing_pairs D muR
  rw [hsum,hsq] at hAll
  have hSplit : (∑ p ∈ longPairs D H, muR p.1*muR p.2) +
    (∑ p ∈ shortPairs D H, muR p.1*muR p.2) =
    ∑ p ∈ increasingPairs D, muR p.1*muR p.2 :=
    sum_filter_add_sum_filter_not (increasingPairs D) (fun p => p.1+2*H<p.2) _
  have hAbs : |∑ p ∈ shortPairs D H, muR p.1*muR p.2| ≤ (H:ℝ)*Q := by
    calc
      _ ≤ ∑ p ∈ shortPairs D H, |muR p.1*muR p.2| := by
        simpa only [Real.norm_eq_abs] using norm_sum_le (shortPairs D H) (fun p => muR p.1*muR p.2)
      _ ≤ ∑ _p ∈ shortPairs D H, (1:ℝ) := sum_le_sum fun p _ => by
        rw [abs_mul]
        exact (mul_le_mul (muR_abs_le_one _) (muR_abs_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ ≤ _ := by
        have hcount := shortPairs_card_le (C := D)
          (fun n hn => (upper_odd_shell_iff.mp (hC (hD hn))).2.2.1) H
        simp only [sum_const,nsmul_eq_mul,mul_one,Q]
        exact_mod_cast hcount
  have hlong : shellLongContribution X H y C =
      2*w*(∑ p ∈ longPairs D H, muR p.1*muR p.2) := by
    unfold shellLongContribution
    have he : (∑ p ∈ longPairs C H,muR p.1*muR p.2*fourierWeight X H y p.1 p.2) =
        ∑ p ∈ longPairs C H,muR p.1*muR p.2*w := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨hmem,_⟩ := mem_filter.mp (mem_filter.mp hp).1
      obtain ⟨h₁,h₂⟩ := mem_product.mp hmem
      rw [fourier_weight_on_shell H y (hC h₁) (hC h₂)]
    rw [he,← sum_mul,← long_pair_sum_filter_mobius C H]
    ring
  let U := ∑ p ∈ shortPairs D H, muR p.1*muR p.2
  have hrel : shellLongContribution X H y C - w*(M X)^2 = -w*Q-2*w*U := by
    rw [hlong]
    dsimp only [U]
    linear_combination w*(hAll+2*hSplit)
  change |shellLongContribution X H y C-w*(M X)^2| ≤ w*(1+2*(H:ℝ))*Q
  rw [hrel]
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  calc
    _ ≤ |-w*Q|+|2*w*U| := abs_sub _ _
    _ = w*Q+2*w*|U| := by
      rw [abs_mul (-w),abs_neg,abs_of_nonneg hw,abs_of_nonneg hQ,abs_mul (2*w),
        abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hw)]
    _ ≤ w*Q+2*w*((H:ℝ)*Q) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hAbs (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hw))
    _ = _ := by ring

end RHConnections.ArithmeticFourierShell
