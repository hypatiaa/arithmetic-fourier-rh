import Verified

open Finset ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierShell
open ArithmeticFourierInversion

private theorem touched_mu_abs_le_one (n : ℕ) : |muR n| ≤ 1 := by
  change |(moebius n:ℝ)| ≤ 1
  exact_mod_cast (abs_moebius_le_one (n := n))

private theorem short_pair_coordinates {C : Finset ℕ} (hC : ∀ n ∈ C, Odd n)
    {H : ℕ} {p : ℕ × ℕ} (hp : p ∈ shortPairs C H) :
    p.1 ∈ C ∧ p.2 ∈ C ∧ p.1<p.2 ∧ ¬p.1+2*H<p.2 ∧
      1 ≤ (p.2-p.1)/2 ∧ (p.2-p.1)/2 ≤ H ∧ p.2=p.1+2*((p.2-p.1)/2) := by
  rcases p with ⟨l,k⟩
  obtain ⟨hI,hS⟩ := Finset.mem_filter.mp hp
  obtain ⟨hP,hlt⟩ := Finset.mem_filter.mp hI
  obtain ⟨hl,hk⟩ := Finset.mem_product.mp hP
  obtain ⟨i,hi⟩ := hC l hl
  obtain ⟨j,hj⟩ := hC k hk
  exact ⟨hl,hk,hlt,hS,by omega,by omega,by omega⟩

private theorem short_pairs_mono {C T : Finset ℕ} (hC : C ⊆ T) (H : ℕ) :
    shortPairs C H ⊆ shortPairs T H := by
  intro p hp
  obtain ⟨hI,hS⟩ := Finset.mem_filter.mp hp
  obtain ⟨hP,hlt⟩ := Finset.mem_filter.mp hI
  obtain ⟨hl,hk⟩ := Finset.mem_product.mp hP
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hC hl,hC hk⟩,hlt⟩,hS⟩

theorem touched_short_card {T A : Finset ℕ} (hT : ∀ n ∈ T, Odd n) (H : ℕ) :
    (shortPairs T H \ shortPairs (T \ A) H).card ≤ 2*H*A.card := by
  classical
  let S := shortPairs T H \ shortPairs (T \ A) H
  let U := (A.product (Finset.Icc 1 H)).product (Finset.univ : Finset Bool)
  let F : ℕ × ℕ → (ℕ × ℕ) × Bool := fun p =>
    if p.1 ∈ A then ((p.1,(p.2-p.1)/2),true) else ((p.2,(p.2-p.1)/2),false)
  have hTouch (p : ℕ × ℕ) (h : p ∈ S) : p.1 ∈ A ∨ p.2 ∈ A := by
    obtain ⟨ht,hn⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hl,hk,hlt,hS,_,_,_⟩ := short_pair_coordinates hT ht
    by_contra! hd
    apply hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hl,hd.1⟩,Finset.mem_sdiff.mpr ⟨hk,hd.2⟩⟩,hlt⟩,hS⟩
  have hmap : Set.MapsTo F S U := by
    intro p hp
    have h := short_pair_coordinates hT (Finset.mem_sdiff.mp hp).1
    have hd : (p.2-p.1)/2 ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨h.2.2.2.2.1,h.2.2.2.2.2.1⟩
    change F p ∈ U
    by_cases hA : p.1 ∈ A
    · rw [show F p = _ from ite_eq_left hA]
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hA,hd⟩, Finset.mem_univ _⟩
    · rw [show F p = _ from ite_eq_right hA]
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨(hTouch p hp).resolve_left hA,hd⟩, Finset.mem_univ _⟩
  have hinj : (S : Set (ℕ × ℕ)).InjOn F := by
    intro p hp q hq he
    have hprec := (short_pair_coordinates hT (Finset.mem_sdiff.mp hp).1).2.2.2.2.2.2
    have hqrec := (short_pair_coordinates hT (Finset.mem_sdiff.mp hq).1).2.2.2.2.2.2
    have hlast : (F p).2 = (F q).2 := congrArg Prod.snd he
    by_cases hpa : p.1 ∈ A <;> by_cases hqa : q.1 ∈ A
    · have hfst : p.1 = q.1 := by simpa only [F,ite_eq_left hpa,ite_eq_left hqa] using congrArg (fun r => r.1.1) he
      have hgap : (p.2-p.1)/2 = (q.2-q.1)/2 := by
        simpa only [F,ite_eq_left hpa,ite_eq_left hqa] using congrArg (fun r => r.1.2) he
      exact Prod.ext hfst (by omega)
    · simp [F,hpa,hqa] at hlast
    · simp [F,hpa,hqa] at hlast
    · have hsnd : p.2 = q.2 := by simpa only [F,ite_eq_right hpa,ite_eq_right hqa] using congrArg (fun r => r.1.1) he
      have hgap : (p.2-p.1)/2 = (q.2-q.1)/2 := by
        simpa only [F,ite_eq_right hpa,ite_eq_right hqa] using congrArg (fun r => r.1.2) he
      exact Prod.ext (by omega) hsnd
  have h := Finset.card_le_card_of_injOn F hmap hinj
  change S.card ≤ U.card at h
  simpa [U,S,Finset.card_product,Nat.card_Icc,mul_comm,mul_left_comm,mul_assoc] using h

theorem paired_block_touched_long_cost (X H y : ℕ) :
    let T := upperOddShell X
    let A := pairedBlock X
    let C := T \ A
    let w := shellWeight H
    |(shellLongContribution X H y T-shellLongContribution X H y C)+w*A.card| ≤
      4*w*(H:ℝ)*A.card := by
  let T := upperOddShell X
  let A := pairedBlock X
  let C := T \ A
  let w := shellWeight H
  let f := fun (p : ℕ × ℕ) => muR p.1 * muR p.2
  let S := shortPairs T H \ shortPairs C H
  have hA : A ⊆ T := paired_block_in_shell X
  have hC : C ⊆ T := Finset.sdiff_subset
  have hw : 0 ≤ w := Finset.sum_nonneg (fun _ _ => by positivity)
  have hSquares : (∑ n ∈ T,(muR n)^2) = (∑ n ∈ C,(muR n)^2)+(A.card:ℝ) := by
    have h := (show (∑ n ∈ C,(muR n)^2)+(∑ n ∈ A,(muR n)^2) = _ from Finset.sum_sdiff hA)
    have he : (∑ n ∈ A,(muR n)^2) = (A.card:ℝ) := by
      calc
        _ = ∑ _n ∈ A,(1:ℝ) := Finset.sum_congr rfl (fun _ hn => paired_block_unit_squares hn)
        _ = _ := by simp
    simpa only [he] using h.symm
  have hSum : (∑ n ∈ C,muR n) = ∑ n ∈ T,muR n := by
    rw [balanced_complement_sum_eq_M hA (paired_block_balanced X),odd_shell_sum_eq_M]
  have hBoth (U : Finset ℕ) (hU : U ⊆ T) : shellLongContribution X H y U =
      2*w*(∑ p ∈ longPairs U H, f p) := by
    unfold shellLongContribution
    have hE : (∑ p ∈ longPairs U H,f p*fourierWeight X H y p.1 p.2) =
        ∑ p ∈ longPairs U H,f p*w := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hI,_⟩ := Finset.mem_filter.mp hp
      obtain ⟨hP,_⟩ := Finset.mem_filter.mp hI
      obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hP
      rw [fourier_weight_on_shell H y (hU h₁) (hU h₂)]
    change 2*(∑ p ∈ longPairs U H,f p*fourierWeight X H y p.1 p.2) = _
    rw [hE,← Finset.sum_mul]
    ring
  have hSplit (U : Finset ℕ) : (∑ p ∈ longPairs U H,f p)+(∑ p ∈ shortPairs U H,f p) =
      ∑ p ∈ increasingPairs U,f p :=
    Finset.sum_filter_add_sum_filter_not (increasingPairs U) (fun p => p.1+2*H<p.2) _
  have hAllT := sum_increasing_pairs T muR
  have hAllC := sum_increasing_pairs C muR
  change 2*(∑ p ∈ increasingPairs T,f p) = _ at hAllT
  change 2*(∑ p ∈ increasingPairs C,f p) = _ at hAllC
  have hShort : (∑ p ∈ S,f p)+(∑ p ∈ shortPairs C H,f p) = ∑ p ∈ shortPairs T H,f p :=
    Finset.sum_sdiff (short_pairs_mono hC H)
  have hId : (shellLongContribution X H y T-shellLongContribution X H y C)+w*A.card =
       -(2*w)*(∑ p ∈ S,f p) := by
    rw [hBoth T le_rfl,hBoth C hC]
    rw [hSum] at hAllC
    rw [hSquares] at hAllT
    linear_combination w*(hAllT-hAllC+2*(hSplit T-hSplit C)+2*hShort)
  have hCrd := touched_short_card (T := T) (A := A)
    (fun n hn => (upper_odd_shell_iff.mp hn).2.2.1) H
  have hABS : |∑ p ∈ S,f p| ≤ (2*(H:ℝ))*(A.card:ℝ) := by
    calc
      _ ≤ ∑ p ∈ S, |f p| := by simpa only [Real.norm_eq_abs] using norm_sum_le S f
      _ ≤ ∑ _p ∈ S,(1:ℝ) := Finset.sum_le_sum fun p _ => by
        dsimp only [f]
        rw [abs_mul]
        exact (mul_le_mul (touched_mu_abs_le_one _) (touched_mu_abs_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one]; exact_mod_cast hCrd
  change |(shellLongContribution X H y T-shellLongContribution X H y C)+w*A.card| ≤ _
  rw [hId,abs_mul,abs_neg,abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hw)]
  exact (mul_le_mul_of_nonneg_left hABS (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hw)).trans_eq (by ring)

end RHConnections.ArithmeticFourierShell
