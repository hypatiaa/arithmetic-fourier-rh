import Verified

open Filter
noncomputable section
namespace RHConnections.ArithmeticFourierShortBlocks

private noncomputable def stride (Q : ℕ) : ℕ → ℕ
  | 0 => Q
  | k+1 => stride Q k+(stride Q k).sqrt

private theorem stride_monotone (Q : ℕ) : Monotone (stride Q) :=
  monotone_nat_of_le_succ (fun _ => Nat.le_add_right _ _)

private theorem stride_lower {Q : ℕ} (hQ : 0<Q) (k : ℕ) :
    Q+k≤stride Q k := by
  induction k with
  | zero => simp [stride]
  | succ k ih =>
    have hpos := Nat.sqrt_pos.mpr (show 0<stride Q k by omega)
    simp only [stride]
    omega

private theorem stride_brackets {Q n : ℕ} (hQ : 0<Q) (hn : Q≤n) :
    ∃ k, stride Q k ≤ n ∧ n<stride Q (k+1) := by
  let h : ∃ k, n<stride Q k := ⟨n+1,by have := stride_lower hQ (n+1); omega⟩
  have hh := Nat.find_spec h
  cases hk : Nat.find h with
  | zero => rw [hk,stride] at hh; omega
  | succ k =>
    exact ⟨k,le_of_not_gt (Nat.find_min h (by omega)),by simpa only [hk,Nat.succ_eq_add_one] using hh⟩

private theorem sqrt_stride_step (n : ℕ) : (n+n.sqrt).sqrt ≤ n.sqrt+1 := by
  by_contra! h
  have hsq := Nat.sqrt_le (n+n.sqrt)
  have htop := Nat.lt_succ_sqrt n
  have hlow := Nat.mul_le_mul (show n.sqrt+2 ≤ (n+n.sqrt).sqrt by omega)
    (show n.sqrt+2 ≤ (n+n.sqrt).sqrt by omega)
  nlinarith only [hsq,htop,hlow]

private theorem sqrt_stride_upper (Q k : ℕ) : (stride Q k).sqrt ≤ Q.sqrt+k := by
  induction k with
  | zero => simp [stride]
  | succ k ih =>
    exact (sqrt_stride_step _).trans (by omega)

private theorem cutoff_growth_from_big_discrepancy (Q : ℕ) (hQ : 0<Q)
    (σ : ℝ)
    (h : ∀ q≥Q, 2 ≤ σ*blockDiscrepancy q q.sqrt) :
    ∀ k : ℕ, σ*primeRemainder Q+2*(k:ℝ) ≤ σ*primeRemainder (stride Q k) := by
  intro k
  induction k with
  | zero => simp [stride]
  | succ k ih =>
    have hk := h (stride Q k) ((Nat.le_add_right Q k).trans (stride_lower hQ k))
    rw [block_discrepancy_eq_remainder,mul_sub] at hk
    simp only [stride,Nat.cast_succ]
    linarith only [ih,hk]

private theorem eventual_sign_from_big_discrepancy (Q : ℕ) (hQ : 0<Q)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1)
    (h : ∀ q≥Q, 2 ≤ σ*blockDiscrepancy q q.sqrt) :
    ∃ N, ∀ n≥N, 0≤σ*primeRemainder n := by
  obtain ⟨k₀,hk₀⟩ := exists_nat_gt ((Q.sqrt:ℝ)-σ*primeRemainder Q)
  refine ⟨stride Q k₀,fun n hn => ?_⟩
  have ht : Q≤n := ((Nat.le_add_right Q k₀).trans (stride_lower hQ k₀)).trans hn
  obtain ⟨k,hl,hu⟩ := stride_brackets hQ ht
  have hkk : k₀≤k := by
    by_contra! h
    exact (not_le_of_gt hu) (((stride_monotone Q) (show k+1≤k₀ by omega)).trans hn)
  have hs := sqrt_stride_upper Q k
  have hx : (n:ℝ) ≤ (stride Q k:ℝ)+(Q.sqrt:ℝ)+(k:ℝ) := by
    simp only [stride] at hu
    exact_mod_cast (show n ≤ stride Q k+Q.sqrt+k by omega)
  have hy : (stride Q (k+1):ℝ) ≤ (n:ℝ)+(Q.sqrt:ℝ)+(k:ℝ) := by
    change ((stride Q k+(stride Q k).sqrt:ℕ):ℝ) ≤ _
    exact_mod_cast (show stride Q k+(stride Q k).sqrt ≤ n+Q.sqrt+k by omega)
  have hka : (k₀:ℝ)≤(k:ℝ) := by exact_mod_cast hkk
  have hkL := cutoff_growth_from_big_discrepancy Q hQ σ h k
  have hkU := cutoff_growth_from_big_discrepancy Q hQ σ h (k+1)
  rcases hσ with rfl|rfl
  · have hp := Chebyshev.psi_mono (show (stride Q k:ℝ)≤n by exact_mod_cast hl)
    simp only [one_mul] at hk₀ hkL ⊢
    unfold primeRemainder at *
    linarith only [hp,hk₀,hkL,hx,hka]
  · have hp := Chebyshev.psi_mono (show (n:ℝ)≤stride Q (k+1) by exact_mod_cast hu.le)
    simp only [neg_one_mul,Nat.cast_succ] at hk₀ hkU ⊢
    unfold primeRemainder at *
    linarith only [hp,hk₀,hkU,hy,hka]

def LatePrimeErrorSigns : Prop :=
  (∀ N : ℕ, ∃ n≥N, primeRemainder n<0) ∧ (∀ N : ℕ, ∃ n≥N, 0<primeRemainder n)

theorem balanced_blocks_of_late_prime_error_signs (h : LatePrimeErrorSigns) (N : ℕ) :
    ∃ Q≥N, |blockDiscrepancy Q Q.sqrt| ≤ 3*Real.log (2+2*(Q:ℝ))+1 := by
  by_contra! hn
  let Q := max 1 N
  have hQ : 0<Q := by dsimp [Q]; omega
  have hN : N≤Q := le_max_right _ _
  let E := fun q : ℕ => blockDiscrepancy q q.sqrt
  let R := fun q : ℕ => 3*Real.log (2+2*(q:ℝ))+1
  have hlarge (q : ℕ) (hq : Q≤q) : R q < |E q| := hn q (hN.trans hq)
  have hR (q : ℕ) : 2≤R q := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<2)
      (show (2:ℝ)≤2+2*(q:ℝ) by linarith [Nat.cast_nonneg (α := ℝ) q])
    dsimp [R]
    linarith only [h,Real.log_two_gt_d9]
  have hstep (q : ℕ) (hq : Q≤q) :
      (2≤E q → 2≤E (q+1)) ∧ (E q≤ -2 → E (q+1)≤ -2) := by
    have hnear := block_discrepancy_neighbor q
    change |E (q+1)-E q|≤R q at hnear
    have hnr := abs_le.mp hnear
    have h1 := hlarge q hq
    have h2 := hlarge (q+1) (hq.trans (Nat.le_succ q))
    constructor
    · intro he
      rw [abs_of_nonneg (by linarith only [he])] at h1
      have hp : 0<E (q+1) := by linarith only [h1,hnr.1]
      rw [abs_of_nonneg hp.le] at h2
      exact (hR _).trans h2.le
    · intro he
      rw [abs_of_nonpos (by linarith only [he])] at h1
      have hp : E (q+1)<0 := by linarith only [h1,hnr.2]
      rw [abs_of_neg hp] at h2
      linarith only [h2,hR (q+1)]
  have hσ : ∃ σ : ℝ, (σ=1 ∨ σ= -1) ∧ ∀ q≥Q, 2≤σ*E q := by
    by_cases h0 : 0≤E Q
    · refine ⟨1,Or.inl rfl,fun q hq => ?_⟩
      have hb := (hR Q).trans (hlarge Q le_rfl).le
      rw [abs_of_nonneg h0] at hb
      simpa only [one_mul] using Nat.le_induction hb (fun q hq hh => (hstep q hq).1 hh) q hq
    · refine ⟨-1,Or.inr rfl,fun q hq => ?_⟩
      have hb := (hR Q).trans (hlarge Q le_rfl).le
      rw [abs_of_neg (lt_of_not_ge h0)] at hb
      have hb' : E Q≤ -2 := by linarith only [hb]
      have he : E q ≤ -2 := Nat.le_induction hb' (fun q hq hh => (hstep q hq).2 hh) q hq
      linarith only [he]
  obtain ⟨σ,hsg,hσ⟩ := hσ
  obtain ⟨K,hK⟩ := eventual_sign_from_big_discrepancy Q hQ σ hsg hσ
  rcases hsg with rfl|rfl
  · obtain ⟨n,hn,he⟩ := h.1 K
    simpa only [one_mul] using (not_le_of_gt he (by simpa only [one_mul] using hK n hn))
  · obtain ⟨n,hn,he⟩ := h.2 K
    simpa only [neg_one_mul,neg_nonneg] using (not_le_of_gt he (by simpa only [neg_one_mul,neg_nonneg] using hK n hn))

end RHConnections.ArithmeticFourierShortBlocks
