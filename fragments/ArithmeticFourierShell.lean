import Verified

open Finset
noncomputable section
namespace RHConnections.ArithmeticFourierShell

def upperOddShell (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun n => Odd n ∧ X < 2*n)

def monomials (X a b n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun m => m.Coprime 182 ∧ X < (2^b)*n*m ∧ (2^a)*n*m ≤ X)

def smoothPart (y n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, if p ≤ y then p^(n.factorization p) else 1

def projectedGram (y m n : ℕ) : ℝ :=
  ((Nat.gcd (smoothPart y m) (smoothPart y n) : ℝ)^2) / ((m:ℝ)*(n:ℝ))

def edgeWeight (a b : ℕ) : ℝ :=
  if a = 0 then ((2:ℝ)^b)⁻¹ else ((2:ℝ)^(b-a+1))⁻¹

def shellWeight (H : ℕ) : ℝ := ∑ b ∈ Finset.Ioc 0 H, ((2:ℝ)^b)⁻¹

def fourierWeight (X H y l k : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 0 H, ∑ b ∈ Finset.Ioc a H, edgeWeight a b *
    ∑ m ∈ monomials X a b l, ∑ n ∈ monomials X a b k, projectedGram y m n

theorem upper_odd_shell_iff {X n : ℕ} : n ∈ upperOddShell X ↔
    1 ≤ n ∧ n ≤ X ∧ Odd n ∧ X < 2*n := by
  simp only [upperOddShell,mem_filter,Finset.mem_Icc,and_assoc]

theorem distinct_shell_indices_do_not_divide {X l k : ℕ} (hl : l ∈ upperOddShell X)
    (hk : k ∈ upperOddShell X) (hne : l ≠ k) : ¬ l ∣ k := by
  obtain ⟨hl0,hlX,_,hl2⟩ := upper_odd_shell_iff.mp hl
  obtain ⟨hk0,hkX,_,_⟩ := upper_odd_shell_iff.mp hk
  rintro ⟨a,rfl⟩
  have ha : 2 ≤ a := by
    by_contra! hn
    interval_cases a <;> simp_all
  have h2 := Nat.mul_le_mul_left l ha
  omega

theorem shell_monomials_zero_left {X b n : ℕ} (hn : n ∈ upperOddShell X) (hb : 0 < b) :
    monomials X 0 b n = {1} := by
  obtain ⟨hn0,hnX,_,hn2⟩ := upper_odd_shell_iff.mp hn
  have hpow : 2 ≤ (2:ℕ)^b := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) (show 1 ≤ b from hb)
  ext m
  simp only [monomials,mem_filter,Finset.mem_Icc,pow_zero,one_mul,Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hm1,hmX⟩,hc,hb,hU⟩
    by_contra hm
    have hm2 : 2 ≤ m := by omega
    have hle : 2*n ≤ n*m := by simpa only [Nat.mul_comm 2 n] using Nat.mul_le_mul_left n hm2
    omega
  · rintro rfl
    have hle := Nat.mul_le_mul_right n hpow
    simp only [mul_one]
    exact ⟨⟨le_rfl,hn0.trans hnX⟩,by decide,hn2.trans_le hle,hnX⟩

theorem shell_monomials_positive_left {X a b n : ℕ} (hn : n ∈ upperOddShell X) (ha : 0 < a) :
    monomials X a b n = ∅ := by
  obtain ⟨_,_,_,hn2⟩ := upper_odd_shell_iff.mp hn
  have hpow : 2 ≤ (2:ℕ)^a := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) (show 1 ≤ a from ha)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  have h := mem_filter.mp hm
  have hle := Nat.mul_le_mul_right n hpow
  have hmul := Nat.mul_le_mul_left ((2^a)*n) (Finset.mem_Icc.mp h.1).1
  omega

theorem fourier_weight_on_shell {X l k : ℕ} (H y : ℕ)
    (hl : l ∈ upperOddShell X) (hk : k ∈ upperOddShell X) :
    fourierWeight X H y l k = shellWeight H := by
  unfold fourierWeight
  rw [sum_eq_single 0]
  · apply sum_congr rfl
    intro b hb
    have hb0 := (Finset.mem_Ioc.mp hb).1
    rw [shell_monomials_zero_left hl hb0,shell_monomials_zero_left hk hb0]
    simp [edgeWeight,projectedGram,smoothPart]
  · intro a _ ha
    apply sum_eq_zero
    intro b _
    rw [shell_monomials_positive_left hl (Nat.pos_of_ne_zero ha)]
    simp
  · simp

theorem shellWeight_eq (H : ℕ) : shellWeight H = 1-((2:ℝ)^H)⁻¹ := by
  induction H with
  | zero => simp [shellWeight]
  | succ H hi =>
    have he : Finset.Ioc (0:ℕ) (H+1) = insert (H+1) (Finset.Ioc 0 H) := by
      ext k
      simp only [Finset.mem_Ioc,Finset.mem_insert]
      omega
    rw [shellWeight,he,sum_insert (by simp),← shellWeight,hi,pow_succ,
      _root_.mul_inv_rev]
    norm_num
    ring

end RHConnections.ArithmeticFourierShell
