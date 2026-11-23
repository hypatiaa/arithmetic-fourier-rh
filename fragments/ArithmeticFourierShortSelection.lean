import Verified

open ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierShortBlocks

def primeRemainder (n : ℕ) : ℝ := Chebyshev.psi (n:ℝ) - n

theorem block_discrepancy_eq_remainder (Q H : ℕ) :
    blockDiscrepancy Q H = primeRemainder (Q+H)-primeRemainder Q := by
  have hsub : Finset.Icc 0 Q ⊆ Finset.Icc 0 (Q+H) := fun n hn =>
    Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Icc.mp hn).2.trans (Nat.le_add_right Q H)⟩
  have he : Finset.Icc 0 (Q+H) \ Finset.Icc 0 Q = Finset.Ioc Q (Q+H) := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_Ioc,true_and,Nat.zero_le]
    omega
  have hsum := Finset.sum_sdiff (f := vonMangoldt) hsub
  rw [he] at hsum
  unfold blockDiscrepancy primeRemainder
  simp only [Chebyshev.psi_eq_sum_Icc,Nat.cast_add,Nat.floor_natCast]
  rw [← Nat.cast_add,Nat.floor_natCast,Nat.cast_add]
  linarith only [hsum]

private theorem sqrt_mono_nat {m n : ℕ} (h : m ≤ n) : m.sqrt ≤ n.sqrt :=
  Nat.le_sqrt.mpr ((Nat.sqrt_le m).trans h)

private theorem prime_remainder_neighbor (n : ℕ) :
    primeRemainder (n+1)-primeRemainder n = vonMangoldt (n+1)-1 := by
  have h := block_discrepancy_eq_remainder n 1
  have he : Finset.Ioc n (n+1) = {n+1} := by
    ext q
    simp only [Finset.mem_Ioc,Finset.mem_singleton]
    omega
  rw [← h,blockDiscrepancy,he,Finset.sum_singleton,Nat.cast_one]

private noncomputable def walk (Q : ℕ) : ℕ → ℕ
  | 0 => Q
  | k+1 => walk Q k+(walk Q k).sqrt

private theorem walk_ge (Q : ℕ) (hQ : 0<Q) (k : ℕ) : Q+k ≤ walk Q k := by
  induction k with
  | zero => simp [walk]
  | succ k ih =>
    have hpos := Nat.sqrt_pos.mpr (show 0 < walk Q k by omega)
    simp only [walk]
    omega

private theorem walk_brackets (Q n : ℕ) (hQ : 0<Q) (hn : Q ≤ n) :
    ∃ k, walk Q k ≤ n ∧ n < walk Q (k+1) := by
  let hk : ∃ k, n < walk Q k := ⟨n+1,by have := walk_ge Q hQ (n+1); omega⟩
  have hf := Nat.find_spec hk
  cases hfind : Nat.find hk with
  | zero => rw [hfind,walk] at hf; omega
  | succ k =>
    refine ⟨k,le_of_not_gt (Nat.find_min hk (by omega)),?_⟩
    simpa only [hfind,Nat.succ_eq_add_one] using hf

private theorem walk_remainder_mono (Q : ℕ) (hQ : 0<Q)
    (h : ∀ n ≥ Q, 0 ≤ blockDiscrepancy n n.sqrt) (k : ℕ) :
    primeRemainder Q ≤ primeRemainder (walk Q k) := by
  induction k with
  | zero => simp [walk]
  | succ k ih =>
    have hs := h (walk Q k) ((Nat.le_add_right Q k).trans (walk_ge Q hQ k))
    rw [block_discrepancy_eq_remainder] at hs
    exact ih.trans (sub_nonneg.mp hs)

private theorem walk_remainder_anti (Q : ℕ) (hQ : 0<Q)
    (h : ∀ n ≥ Q, blockDiscrepancy n n.sqrt ≤ 0) (k : ℕ) :
    primeRemainder (walk Q k) ≤ primeRemainder Q := by
  induction k with
  | zero => simp [walk]
  | succ k ih =>
    have hs := h (walk Q k) ((Nat.le_add_right Q k).trans (walk_ge Q hQ k))
    rw [block_discrepancy_eq_remainder] at hs
    exact (sub_nonpos.mp hs).trans ih

theorem late_nonnegative_block_lower (Q n : ℕ) (hQ : 0<Q) (hn : Q ≤ n)
    (h : ∀ q ≥ Q, 0 ≤ blockDiscrepancy q q.sqrt) :
    primeRemainder Q - (n.sqrt:ℝ) ≤ primeRemainder n := by
  obtain ⟨k,hl,hu⟩ := walk_brackets Q n hQ hn
  have hpsi := Chebyshev.psi_mono (show ((walk Q k:ℕ):ℝ) ≤ (n:ℝ) by exact_mod_cast hl)
  have hdiff : (n:ℝ) ≤ (walk Q k:ℝ)+(n.sqrt:ℝ) := by
    have := sqrt_mono_nat hl
    simp only [walk] at hu
    exact_mod_cast (show n ≤ walk Q k+n.sqrt by omega)
  have he := walk_remainder_mono Q hQ h k
  unfold primeRemainder at *
  linarith only [hpsi,hdiff,he]

theorem late_nonpositive_block_upper (Q n : ℕ) (hQ : 0<Q) (hn : Q ≤ n)
    (h : ∀ q ≥ Q, blockDiscrepancy q q.sqrt ≤ 0) :
    primeRemainder n ≤ primeRemainder Q + (n.sqrt:ℝ) := by
  obtain ⟨k,hl,hu⟩ := walk_brackets Q n hQ hn
  have hpsi := Chebyshev.psi_mono (show (n:ℝ) ≤ (walk Q (k+1):ℝ) by exact_mod_cast hu.le)
  have hdiff : (walk Q (k+1):ℝ) ≤ (n:ℝ)+(n.sqrt:ℝ) := by
    have := sqrt_mono_nat hl
    simp only [walk]
    exact_mod_cast (show walk Q k+(walk Q k).sqrt ≤ n+n.sqrt by omega)
  have he := walk_remainder_anti Q hQ h (k+1)
  unfold primeRemainder at *
  linarith only [hpsi,hdiff,he]

def TwoSidedPsiOscillations : Prop :=
  (∀ C : ℝ, ∀ N : ℕ, ∃ n ≥ N, primeRemainder n < -C*(n.sqrt:ℝ)) ∧
  (∀ C : ℝ, ∀ N : ℕ, ∃ n ≥ N, C*(n.sqrt:ℝ) < primeRemainder n)

theorem block_discrepancy_both_signs (h : TwoSidedPsiOscillations) (N : ℕ) :
    (∃ Q ≥ N, blockDiscrepancy Q Q.sqrt < 0) ∧
    (∃ Q ≥ N, 0 < blockDiscrepancy Q Q.sqrt) := by
  let Q := max 1 N
  have hQ : 0 < Q := lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)
  have hN : N ≤ Q := le_max_right ..
  have hnonneg (n : ℕ) (hn : Q ≤ n) : (1:ℝ) ≤ (n.sqrt:ℝ) := by
    exact_mod_cast (Nat.sqrt_pos.mpr (hQ.trans_le hn))
  have hcost (n : ℕ) (hn : Q ≤ n) := mul_le_mul_of_nonneg_left
    (hnonneg n hn) (abs_nonneg (primeRemainder Q))
  constructor
  · by_contra! hcontra
    obtain ⟨n,hn,he⟩ := h.1 (1+|primeRemainder Q|) Q
    have hL := late_nonnegative_block_lower Q n hQ hn (fun q hq => hcontra q (hN.trans hq))
    nlinarith only [hL,he,hcost n hn,neg_abs_le (primeRemainder Q)]
  · by_contra! hcontra
    obtain ⟨n,hn,he⟩ := h.2 (1+|primeRemainder Q|) Q
    have hU := late_nonpositive_block_upper Q n hQ hn (fun q hq => hcontra q (hN.trans hq))
    nlinarith only [hU,he,hcost n hn,le_abs_self (primeRemainder Q)]

private theorem sqrt_step (n : ℕ) : (n+1).sqrt = n.sqrt ∨ (n+1).sqrt = n.sqrt+1 := by
  have hl : n.sqrt ≤ (n+1).sqrt := sqrt_mono_nat (Nat.le_succ n)
  have hU : (n+1).sqrt ≤ n.sqrt+1 := by
    by_contra! hc
    have h1 := Nat.sqrt_le (n+1)
    have h2 := Nat.lt_succ_sqrt n
    have h3 := Nat.mul_le_mul (show n.sqrt+2 ≤ (n+1).sqrt by omega)
      (show n.sqrt+2 ≤ (n+1).sqrt by omega)
    nlinarith only [h1,h2,h3]
  omega

private theorem vm_in_log_window (N n : ℕ) (hn : 0<n) (hN : n≤N) :
    0 ≤ vonMangoldt n ∧ vonMangoldt n ≤ Real.log (N:ℝ) :=
  ⟨vonMangoldt_nonneg, vonMangoldt_le_log.trans (Real.log_le_log
    (by exact_mod_cast hn) (by exact_mod_cast hN))⟩

theorem block_discrepancy_neighbor (q : ℕ) :
    |blockDiscrepancy (q+1) (q+1).sqrt - blockDiscrepancy q q.sqrt| ≤
      3*Real.log (2+2*(q:ℝ))+1 := by
  have hS := Nat.sqrt_le_self q
  have hL : 0 ≤ Real.log (2+2*(q:ℝ)) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) q])
  have hv (r : ℕ) (hr : 0<r) (h : r ≤ 2+2*q) :
      vonMangoldt r ∈ Set.Icc 0 (Real.log (2+2*(q:ℝ))) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Set.mem_Icc] using vm_in_log_window _ r hr h
  have hv0 := hv (q+1) (by omega) (by omega)
  have hv1 := hv (q+q.sqrt+1) (by omega) (by omega)
  have hv2 := hv (q+q.sqrt+1+1) (by omega) (by omega)
  rw [block_discrepancy_eq_remainder,block_discrepancy_eq_remainder]
  rcases sqrt_step q with hs|hs
  · rw [hs,show q+1+q.sqrt=q+q.sqrt+1 by omega]
    have h₀ := prime_remainder_neighbor q
    have h₁ := prime_remainder_neighbor (q+q.sqrt)
    exact abs_le.mpr ⟨by linarith only [h₀,h₁,hL,hv0.2,hv1.1],
      by linarith only [h₀,h₁,hL,hv0.1,hv1.2]⟩
  · rw [hs,show q+1+(q.sqrt+1)=q+q.sqrt+1+1 by omega]
    have h₀ := prime_remainder_neighbor q
    have h₁ := prime_remainder_neighbor (q+q.sqrt)
    have h₂ := prime_remainder_neighbor (q+q.sqrt+1)
    exact abs_le.mpr ⟨by linarith only [h₀,h₁,h₂,hL,hv0.2,hv1.1,hv2.1],
      by linarith only [h₀,h₁,h₂,hL,hv0.1,hv1.2,hv2.2]⟩

theorem arbitrarily_late_balanced_blocks (h : TwoSidedPsiOscillations) (N : ℕ) :
    ∃ Q ≥ N, |blockDiscrepancy Q Q.sqrt| ≤ 3*Real.log (2+2*(Q:ℝ))+1 := by
  obtain ⟨⟨q,hq,hneg⟩,_⟩ := block_discrepancy_both_signs h N
  obtain ⟨_,r,hr,hpos⟩ := block_discrepancy_both_signs h (q+1)
  let E : ℕ → ℝ := fun x => blockDiscrepancy x x.sqrt
  let hex : ∃ k, 0 ≤ E (q+k) := ⟨r-q,by dsimp [E]; rw [Nat.add_sub_of_le (by omega : q ≤ r)]; exact hpos.le⟩
  have hfind := Nat.find_spec hex
  cases hk : Nat.find hex with
  | zero =>
    rw [hk,Nat.add_zero] at hfind
    exact (not_le_of_gt hneg hfind).elim
  | succ k =>
    have hprev := lt_of_not_ge (Nat.find_min hex (show k<Nat.find hex by omega))
    rw [hk,show q+k.succ=q+k+1 by omega] at hfind
    have hstep := block_discrepancy_neighbor (q+k)
    change |E (q+k+1)-E (q+k)| ≤ _ at hstep
    have hdiff := le_abs_self (E (q+k+1)-E (q+k))
    exact ⟨q+k,by omega,(abs_of_neg hprev).le.trans (by linarith only [hstep,hfind,hdiff])⟩

end RHConnections.ArithmeticFourierShortBlocks
