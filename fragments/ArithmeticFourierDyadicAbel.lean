import Verified
import ArithmeticFourierDyadicConvolution

open ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierDyadic
open ArithmeticFourierInversion ArithmeticFourierShortBlocks

theorem block_abel_identity (P V : ℕ → ℝ) (hP : P 0=0) (r : ℕ) :
    (∑ j ∈ Finset.range r,(P (j+1)-P j)*V j) =
      P r*V r + ∑ j ∈ Finset.range r,P (j+1)*(V j-V (j+1)) := by
  induction r with
  | zero => simp [hP]
  | succ r ih =>
    simp only [Finset.sum_range_succ,ih]
    ring

theorem sum_block_differences (f : ℕ → ℝ) (r : ℕ) :
    (∑ j ∈ Finset.range r,(f (j+1)-f j)) = f r-f 0 := by
  induction r with
  | zero => simp
  | succ r ih => simp only [Finset.sum_range_succ,ih]; ring

theorem endpoint_discrepancy_bound (P : ℕ → ℝ) (F : ℕ → ℝ) (v : ℕ → ℕ)
    (r : ℕ) (L : ℝ) (hL : 0≤L) (hP0 : P 0=0) (hP : ∀ j≤r, |P j|≤L)
    (hF : ∀ l m, l≤m → |F m-F l|≤(m:ℝ)-l) (hF0 : F 0=0) (hv : Antitone v) :
    |∑ j ∈ Finset.range r,(P (j+1)-P j)*F (v j)| ≤ L*(v 0:ℝ) := by
  have hAb := block_abel_identity P (F ∘ v) hP0 r
  simp only [Function.comp_apply] at hAb
  rw [hAb]
  have hlast : |F (v r)| ≤ (v r:ℝ) := by simpa [hF0] using hF 0 (v r) (Nat.zero_le _)
  have htel : (∑ j ∈ Finset.range r,((v j:ℝ)-(v (j+1):ℝ))) = (v 0:ℝ)-(v r:ℝ) := by
    have h := congrArg Neg.neg (sum_block_differences (fun j => (v j:ℝ)) r)
    simpa only [← Finset.sum_neg_distrib,neg_sub] using h
  calc
    _ ≤ |P r*F (v r)| + |∑ j ∈ Finset.range r,P (j+1)*(F (v j)-F (v (j+1)))| := abs_add_le _ _
    _ ≤ L*(v r:ℝ) + (∑ j ∈ Finset.range r,L*((v j:ℝ)-(v (j+1):ℝ))) := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul (hP _ le_rfl) hlast (abs_nonneg _) hL
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        refine Finset.sum_le_sum (fun j hj => ?_)
        rw [abs_mul]
        exact mul_le_mul (hP _ (by have := Finset.mem_range.mp hj; omega))
          (hF (v (j+1)) (v j) (hv (Nat.le_succ _))) (abs_nonneg _) hL
    _ = _ := by rw [← Finset.mul_sum,htel]; ring

def primeMass (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ q ∈ Finset.Ioc 0 n,f q

theorem primeMass_difference (f : ℕ → ℝ) {x y : ℕ} (hxy : x≤y) :
    primeMass f y-primeMass f x = ∑ q ∈ Finset.Ioc x y,f q := by
  have hs : Finset.Ioc (0:ℕ) x ⊆ Finset.Ioc 0 y := fun n hn =>
    Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,(Finset.mem_Ioc.mp hn).2.trans hxy⟩
  have he : Finset.Ioc (0:ℕ) y \ Finset.Ioc 0 x = Finset.Ioc x y := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_Ioc]
    omega
  have heq := Finset.sum_sdiff (f := f) hs
  rw [he] at heq
  unfold primeMass
  linarith only [heq]

theorem partition_sum_telescope (u : ℕ → ℕ) (hu : Monotone u) (r : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range r, ∑ q ∈ Finset.Ioc (u j) (u (j+1)),f q) =
      ∑ q ∈ Finset.Ioc (u 0) (u r),f q := by
  simp_rw [← primeMass_difference f (hu (Nat.le_succ _))]
  exact (sum_block_differences (primeMass f ∘ u) r).trans (primeMass_difference f (hu (Nat.zero_le _)))

def blockVM (u : ℕ → ℕ) (j : ℕ) : ℝ := primeRemainder (u (j+1))-primeRemainder (u j)

def blockCorrection (B : ℕ) (u : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc (u j) (u (j+1)),vonMangoldt q*g B q

theorem block_correction_nonneg (B : ℕ) (u : ℕ → ℕ) (j : ℕ) :
    0 ≤ blockCorrection B u j := by
  apply Finset.sum_nonneg
  intro q _
  apply mul_nonneg vonMangoldt_nonneg
  rw [g_apply]
  split_ifs <;> positivity

theorem dyadic_correction_mass (B Q r : ℕ) (hQ : 0<Q) (u : ℕ → ℕ) (hu : Monotone u)
    (h0 : u 0=Q) (hr : u r=2*Q) :
    (∑ j ∈ Finset.range r,blockCorrection B u j) ≤ Chebyshev.psi (2*(Q:ℝ))/(Q:ℝ) := by
  unfold blockCorrection
  rw [partition_sum_telescope u hu r,h0,hr]
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hsum :
      (∑ q ∈ Finset.Ioc Q (2*Q),vonMangoldt q*g B q) ≤
      ∑ q ∈ Finset.Ioc Q (2*Q),vonMangoldt q*(Q:ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro q hq
    apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
    rw [g_apply]
    split_ifs
    · exact inv_anti₀ hQr (by exact_mod_cast (Finset.mem_Ioc.mp hq).1.le)
    · positivity
  have hh : (∑ q ∈ Finset.Ioc Q (2*Q),vonMangoldt q) ≤ Chebyshev.psi (2*(Q:ℝ)) := by
    rw [show (2:ℝ)*(Q:ℝ)=((2*Q:ℕ):ℝ) by norm_num,Chebyshev.psi_eq_sum_Icc,Nat.floor_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun n hn =>
      Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Ioc.mp hn).2⟩) (fun _ _ _ => vonMangoldt_nonneg)
  rw [← Finset.sum_mul] at hsum
  exact hsum.trans (by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hh (by positivity))

theorem dyadic_scalar_aggregate_bound (B X Q r : ℕ) (hQ : 0<Q) (u : ℕ → ℕ)
    (hu : Monotone u) (h0 : u 0=Q) (hr : u r=2*Q)
    (v : ℕ → ℕ) (hv : Monotone v) (hvQ : Q≤v 0)
    (L : ℝ) (hL : 0≤L)
    (hp : ∀ n ∈ Finset.Icc Q (2*Q), |primeRemainder n-primeRemainder Q|≤L) :
    |aggregate (Finset.range r) v (fun j => blockVM u j-blockCorrection B u j) (S B) X| ≤
      (L+Chebyshev.psi (2*(Q:ℝ))/(Q:ℝ))*((X/Q:ℕ):ℝ) := by
  let P := fun j => primeRemainder (u j)-primeRemainder Q
  have hquot : Antitone (fun j => X/v j) := by
    intro i j hij
    apply Nat.div_le_div_left (hv hij)
    exact hQ.trans_le (hvQ.trans (hv (Nat.zero_le i)))
  have hs0 : S B 0=0 := by simp [S]
  have hP (j : ℕ) (hj : j≤r) : |P j|≤L := hp _ (Finset.mem_Icc.mpr
    ⟨h0 ▸ hu (Nat.zero_le j),hr ▸ hu hj⟩)
  have hAb := endpoint_discrepancy_bound P (S B) (fun j => X/v j) r L hL
    (by simp [P,h0]) hP (scalar_S_lipschitz B) hs0 hquot
  have hPdiff (j : ℕ) : P (j+1)-P j = blockVM u j := by
    unfold P blockVM
    ring
  simp only [hPdiff] at hAb
  have hle : ((X/v 0:ℕ):ℝ) ≤ ((X/Q:ℕ):ℝ) := by
    exact_mod_cast (Nat.div_le_div_left hvQ hQ)
  have hAbQ := hAb.trans (mul_le_mul_of_nonneg_left hle hL)
  change |aggregate (Finset.range r) v (blockVM u) (S B) X| ≤ _ at hAb
  have hc := aggregate_correction_bound (Finset.range r) v (blockCorrection B u) (S B)
    (fun n => by simpa [hs0] using scalar_S_lipschitz B 0 n (Nat.zero_le _)) X Q
    (fun j _ => hvQ.trans (hv (Nat.zero_le j))) hQ (fun j _ => block_correction_nonneg B u j)
  rw [aggregate_sub_weights]
  apply (abs_sub _ _).trans
  have hm := dyadic_correction_mass B Q r hQ u hu h0 hr
  have hc' := hc.trans (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _))
  calc
    _ ≤ L*((X/Q:ℕ):ℝ)+((X/Q:ℕ):ℝ)*(Chebyshev.psi (2*(Q:ℝ))/(Q:ℝ)) := add_le_add hAbQ hc'
    _ = _ := by ring

private theorem uniform_prime_correction_size (Q : ℕ) (hQ : 0<Q) :
    Chebyshev.psi (2*(Q:ℝ))/(Q:ℝ) ≤ 2*(Real.log 4+4) := by
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  apply (div_le_iff₀ hQr).mpr
  exact (Chebyshev.psi_le_const_mul_self (show 0≤(2:ℝ)*(Q:ℝ) by positivity)).trans_eq (by ring)

theorem dyadic_transfer_cost (B X Q r : ℕ) (hQ : 0<Q) (u : ℕ → ℕ)
    (hu : Monotone u) (h0 : u 0=Q) (hr : u r=2*Q) :
    let W := fun y => aggregate (Finset.range r) u
      (fun j => blockVM u j-blockCorrection B u j) (S B) y
    let U := fun y => aggregate (Finset.range r) u (blockVM u) M y
    |W X - ∑ k ∈ Finset.Ioc 0 (X/Q),g B k*U (X/k)| ≤
      2*(Real.log 4+4)*((X/Q:ℕ):ℝ) ∧
    |U X - ∑ k ∈ Finset.Ioc 0 (X/Q),h B k*W (X/k)| ≤
      2*(Real.log 4+4)*((X/Q:ℕ):ℝ) := by
  have hl (j : ℕ) (_ : j∈Finset.range r) : Q ≤ u j := h0 ▸ hu (Nat.zero_le j)
  have hcorr := (dyadic_correction_mass B Q r hQ u hu h0 hr).trans (uniform_prime_correction_size Q hQ)
  have hc := mul_le_mul_of_nonneg_left hcorr (show 0≤((X/Q:ℕ):ℝ) by positivity)
  rw [mul_comm (2*(Real.log 4+4)) ((X/Q:ℕ):ℝ)]
  exact ⟨(forward_corrected_aggregate (Finset.range r) u (blockVM u) (blockCorrection B u)
    B X Q hl hQ (fun j _ => block_correction_nonneg B u j)).trans hc,
    (inverse_corrected_aggregate (Finset.range r) u (blockVM u) (blockCorrection B u)
      B X Q hl hQ (fun j _ => block_correction_nonneg B u j)).trans hc⟩

theorem dyadic_log_power_transfer (A C : ℝ) (hA : 0<A) (hC : 0≤C)
    (hprime : ∀ n : ℕ, 2≤n → |primeRemainder n|≤C*(n:ℝ)/(Real.log (n:ℝ))^A)
    (B X Q r : ℕ) (hQ : 2≤Q) (u : ℕ → ℕ) (hu : Monotone u) (h0 : u 0=Q) (hr : u r=2*Q)
    (v : ℕ → ℕ) (hv : Monotone v) (hvQ : Q≤v 0) :
    |aggregate (Finset.range r) v (fun j => blockVM u j-blockCorrection B u j) (S B) X| ≤
      (3*C+2*(Real.log 4+4)*A^A)*(X:ℝ)/(Real.log (Q:ℝ))^A := by
  let ℓ := Real.log (Q:ℝ)
  have hQr : (0:ℝ)<Q := by exact_mod_cast (show 0<Q by omega)
  have h1Q : (1:ℝ)<Q := by exact_mod_cast (show 1<Q by omega)
  have hl : 0 < ℓ := Real.log_pos h1Q
  have hlA : 0 < ℓ^A := Real.rpow_pos_of_pos hl _
  have he (n : ℕ) (hn : n∈Finset.Icc Q (2*Q)) :
      |primeRemainder n-primeRemainder Q|≤3*C*(Q:ℝ)/ℓ^A := by
    obtain ⟨hqn,hnq⟩ := Finset.mem_Icc.mp hn
    have hnr : (n:ℝ) ≤ 2*(Q:ℝ) := by exact_mod_cast hnq
    have hlog := Real.log_le_log hQr (show (Q:ℝ)≤n by exact_mod_cast hqn)
    have hpow : ℓ^A ≤ (Real.log (n:ℝ))^A := Real.rpow_le_rpow hl.le hlog hA.le
    have hpn := (hprime n (hQ.trans hqn)).trans
      (div_le_div_of_nonneg_left (show 0≤C*(n:ℝ) by positivity) hlA hpow)
    have hPQ := hprime Q hQ
    have hu : C*(n:ℝ)/ℓ^A ≤ C*(2*(Q:ℝ))/ℓ^A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnr hC) hlA.le
    exact (abs_sub _ _).trans (by
      change _ ≤ 3*C*(Q:ℝ)/ℓ^A
      change |primeRemainder Q| ≤ C*(Q:ℝ)/ℓ^A at hPQ
      calc
        _ ≤ C*(2*(Q:ℝ))/ℓ^A+C*(Q:ℝ)/ℓ^A := add_le_add (hpn.trans hu) hPQ
        _ = _ := by ring)
  have hlcmp : ℓ^A ≤ A^A*(Q:ℝ) := by
    have hlog := Real.log_le_rpow_div hQr.le (one_div_pos.mpr hA)
    have hlog' : ℓ ≤ A*(Q:ℝ)^(1/A) := by
      change ℓ ≤ (Q:ℝ)^(1/A)/(1/A) at hlog
      convert hlog using 1
      field_simp
    refine (Real.rpow_le_rpow hl.le hlog' hA.le).trans_eq ?_
    rw [Real.mul_rpow hA.le (by positivity),← Real.rpow_mul hQr.le,
      show 1/A*A=1 from one_div_mul_cancel hA.ne',Real.rpow_one]
  have hc : 2*(Real.log 4+4) ≤ 2*(Real.log 4+4)*A^A*(Q:ℝ)/ℓ^A := by
    have hpos : 0≤2*(Real.log 4+4) := by
      linarith only [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
    apply (le_div_iff₀ hlA).mpr
    exact (mul_le_mul_of_nonneg_left hlcmp hpos).trans_eq (by ring)
  have hH := dyadic_scalar_aggregate_bound B X Q r (by omega) u hu h0 hr v hv hvQ
    (3*C*(Q:ℝ)/ℓ^A) (by positivity) he
  have hx : ((X/Q:ℕ):ℝ) ≤ (X:ℝ)/Q :=
    (le_div_iff₀ hQr).mpr (by exact_mod_cast Nat.div_mul_le_self X Q)
  have hcb := (uniform_prime_correction_size Q (by omega)).trans hc
  apply hH.trans
  calc
    _ ≤ (3*C*(Q:ℝ)/ℓ^A + 2*(Real.log 4+4)*A^A*(Q:ℝ)/ℓ^A)*((X:ℝ)/Q) := by
      apply mul_le_mul (add_le_add (le_refl _) hcb) hx (Nat.cast_nonneg _)
      have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      positivity
    _ = _ := by dsimp only [ℓ]; field_simp

theorem dyadic_unblocked_log_power_transfer (A C : ℝ) (hA : 0<A) (hC : 0≤C)
    (hprime : ∀ n : ℕ, 2≤n → |primeRemainder n|≤C*(n:ℝ)/(Real.log (n:ℝ))^A)
    (B X Q : ℕ) (hQ : 2≤Q) :
    |∑ q ∈ Finset.Ioc Q (2*Q),(shortWeight B q-1)*S B (X/q)| ≤
      (3*C+2*(Real.log 4+4)*A^A)*(X:ℝ)/(Real.log (Q:ℝ))^A := by
  let u := fun j => Q+j
  let v := fun j => Q+j+1
  have H := dyadic_log_power_transfer A C hA hC hprime B X Q Q hQ u
    (fun _ _ h => Nat.add_le_add_left h Q) (by simp [u]) (by dsimp [u]; omega)
    v (fun _ _ h => Nat.add_le_add_right (Nat.add_le_add_left h Q) 1) (by simp [v])
  have hweights (j : ℕ) : blockVM u j-blockCorrection B u j = shortWeight B (v j)-1 := by
    have he : Finset.Ioc (u j) (u (j+1)) = {v j} := by
      ext q
      simp only [Finset.mem_Ioc,Finset.mem_singleton,u,v]
      omega
    have hd := block_discrepancy_eq_remainder (u j) 1
    change blockDiscrepancy (u j) 1 = blockVM u j at hd
    rw [← hd,blockDiscrepancy,blockCorrection,show u j+1=u (j+1) by rfl,he,
      Finset.sum_singleton,Finset.sum_singleton,shortWeight,Nat.cast_one]
    ring
  have hre : (∑ j ∈ Finset.range Q,(shortWeight B (v j)-1)*S B (X/v j)) =
      ∑ q ∈ Finset.Ioc Q (2*Q),(shortWeight B q-1)*S B (X/q) := by
    apply Finset.sum_nbij v
    · intro j hj
      exact Finset.mem_Ioc.mpr ⟨by dsimp [v]; omega,by have := Finset.mem_range.mp hj; dsimp [v]; omega⟩
    · intro i _ j _ hij
      dsimp [v] at hij
      omega
    · intro q hq
      obtain ⟨hl,hr⟩ := Finset.mem_Ioc.mp hq
      exact ⟨q-Q-1,Finset.mem_range.mpr (by omega),by dsimp [v]; omega⟩
    · intros; rfl
  simp only [aggregate,hweights,hre] at H
  exact H

end RHConnections.ArithmeticFourierDyadic
