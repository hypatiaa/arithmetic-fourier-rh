import Verified
import ArithmeticFourierDenseTests
import ArithmeticFourierDyadicAbel

open ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierMertensKernel
open ArithmeticFourierInversion ArithmeticFourierDyadic ArithmeticFourierShortBlocks

def blockKernel {ι : Type*} (J : Finset ι) (u : ι → ℕ) (d : ι → ℝ) (X n : ℕ) : ℝ :=
  ∑ j ∈ J, if n≤X/u j then d j else 0

theorem aggregate_eq_mobius_kernel {ι : Type*} (J : Finset ι) (u : ι → ℕ) (d : ι → ℝ)
    (X Q : ℕ) (hQ : 0<Q) (hu : ∀ j ∈ J, Q≤u j) :
    aggregate J u d M X = dot (X/Q) muR (blockKernel J u d X) := by
  unfold aggregate dot blockKernel M
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hfilter : ((Finset.Ioc 0 (X/Q)).filter fun n => n≤X/u j) =
      Finset.Ioc 0 (X/u j) := by
    ext n
    have hle : X/u j ≤ X/Q := Nat.div_le_div_left (hu j hj) hQ
    simp only [Finset.mem_filter,Finset.mem_Ioc]
    omega
  simp only [mul_ite,mul_zero,← Finset.sum_filter,hfilter]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem mobius_kernel_constant_plateau (u : ℕ → ℕ) (r X Q : ℕ) (hQ : 0<Q)
    (hu : Monotone u) (h0 : u 0=Q) (hr : u r=2*Q) {n : ℕ} (hn : n≤X/(2*Q)) :
    blockKernel (Finset.range r) u (blockVM u) X n = primeRemainder (2*Q)-primeRemainder Q := by
  unfold blockKernel
  have active (j : ℕ) (hj : j∈Finset.range r) : n ≤ X/u j := by
    have hlu : u j ≤ 2*Q := hr ▸ hu (Finset.mem_range.mp hj).le
    have hp : 0<u j := hQ.trans_le (h0 ▸ hu (Nat.zero_le j))
    exact hn.trans (Nat.div_le_div_left hlu hp)
  calc
    _ = ∑ j ∈ Finset.range r, blockVM u j :=
      Finset.sum_congr rfl (fun j hj => ite_eq_left (active j hj))
    _ = _ := by
      unfold blockVM
      simpa only [Function.comp_apply,h0,hr] using sum_block_differences (primeRemainder ∘ u) r

theorem kernel_plateau_decomposition (u : ℕ → ℕ) (r X Q : ℕ) (hQ : 0<Q)
    (hu : Monotone u) (h0 : u 0=Q) (hr : u r=2*Q) :
    let K := blockKernel (Finset.range r) u (blockVM u) X
    aggregate (Finset.range r) u (blockVM u) M X =
      (primeRemainder (2*Q)-primeRemainder Q)*M (X/(2*Q)) +
        ∑ n ∈ Finset.Ioc (X/(2*Q)) (X/Q),muR n*K n := by
  let K := blockKernel (Finset.range r) u (blockVM u) X
  change aggregate _ _ _ _ _ = _ + ∑ n ∈ Finset.Ioc (X/(2*Q)) (X/Q),muR n*K n
  rw [aggregate_eq_mobius_kernel _ _ _ _ Q hQ (fun j _ => h0 ▸ hu (Nat.zero_le j))]
  change primeMass (fun n => muR n*K n) (X/Q) = _
  have hle : X/(2*Q) ≤ X/Q := Nat.div_le_div_left (by omega) hQ
  have hd := primeMass_difference (fun n => muR n*K n) hle
  have hplateau : primeMass (fun n => muR n*K n) (X/(2*Q)) =
      (primeRemainder (2*Q)-primeRemainder Q)*M (X/(2*Q)) := by
    unfold primeMass M
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n hn => by
      change muR n*blockKernel _ _ _ _ _ = _
      rw [mobius_kernel_constant_plateau u r X Q hQ hu h0 hr (Finset.mem_Ioc.mp hn).2,mul_comm])
  rw [hplateau] at hd
  exact (eq_add_of_sub_eq hd).trans (add_comm _ _)

theorem finite_plateau_cost (N L : ℕ) (hL : L≤N) (K G : ℕ → ℝ) (D : ℝ)
    (hK : ∀ n ∈ Finset.Ioc 0 L, K n = D) (covered : Finset ℕ)
    (hG : ∀ n ∈ Finset.Ioc 0 L, n∉covered → G n=0) :
    (((Finset.Ioc 0 L) \ covered).card:ℝ)*D^2 ≤ sqNorm N (fun n => K n-G n) := by
  classical
  let A := Finset.Ioc 0 L \ covered
  have ha : A ⊆ Finset.Ioc 0 N := fun n hn =>
    Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp (Finset.mem_sdiff.mp hn).1).1,
      (Finset.mem_Ioc.mp (Finset.mem_sdiff.mp hn).1).2.trans hL⟩
  calc
    _ = ∑ _n ∈ A,D^2 := by simp [A]
    _ = ∑ n ∈ A,(K n-G n)*(K n-G n) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      obtain ⟨h₁,h₂⟩ := Finset.mem_sdiff.mp hn
      rw [hK n h₁,hG n h₁ h₂,sub_zero,pow_two]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg ha (fun _ _ _ => mul_self_nonneg _)

theorem sparse_divisor_test_plateau_cost (N L : ℕ) (hL : L≤N) (K : ℕ → ℝ) (D : ℝ)
    (hK : ∀ n ∈ Finset.Ioc 0 L, K n = D) (T : Finset ℕ) (w : ℕ → ℝ)
    (hT : ∀ m ∈ T, m≠0) :
    ((L-∑ m ∈ T,m.divisors.card:ℕ):ℝ)*D^2 ≤ sqNorm N
      (fun n => K n-∑ m ∈ T, if n∣m then w m else 0) := by
  classical
  let C := T.biUnion Nat.divisors
  let G := fun n => ∑ m ∈ T, if n∣m then w m else 0
  have hz (n : ℕ) (_ : n∈Finset.Ioc 0 L) (hn : n∉C) : G n=0 := by
    apply Finset.sum_eq_zero
    intro m hm
    refine ite_eq_right (fun hd => hn ?_)
    exact Finset.mem_biUnion.mpr ⟨m,hm,Nat.mem_divisors.mpr ⟨hd,hT m hm⟩⟩
  have hc : C.card ≤ ∑ m ∈ T,m.divisors.card := Finset.card_biUnion_le
  have hsize : L-∑ m ∈ T,m.divisors.card ≤ ((Finset.Ioc 0 L) \ C).card := by
    have hu := Finset.card_sdiff_add_card_inter (Finset.Ioc 0 L) C
    have hi : ((Finset.Ioc 0 L) ∩ C).card ≤ C.card := Finset.card_le_card Finset.inter_subset_right
    rw [Nat.card_Ioc,Nat.sub_zero] at hu
    omega
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) (sq_nonneg D)).trans
    (finite_plateau_cost N L hL K G D hK C hz)

theorem dense_floor_residual_attains_signed_cost (N : ℕ) (hN : 0<N) (K : ℕ → ℝ) :
    ∃ a : ℕ → ℝ, sqNorm N (fun n => K n-∑ t ∈ Finset.Ioc 1 N,a t*floorTest t n) =
      (dot N muR K)^2 / sqNorm N muR := by
  have hmu : 0 < sqNorm N muR := by
    have h : muR 1 * muR 1 ≤ sqNorm N muR := by
      unfold sqNorm dot
      exact Finset.single_le_sum (f := fun n => muR n*muR n)
        (fun n _ => mul_self_nonneg _) (Finset.mem_Ioc.mpr ⟨Nat.zero_lt_one,hN⟩)
    have hm : muR 1=1 := by simp [muR]
    rw [hm,one_mul] at h
    exact zero_lt_one.trans_le h
  obtain ⟨hg,he⟩ := correction_projection N muR K hmu
  let G := fun n => K n-(dot N muR K / sqNorm N muR)*muR n
  change dot N muR G=0 at hg
  change sqNorm N (fun n => K n-G n) = _ at he
  obtain ⟨a,ha⟩ := floor_tests_span_mobius_null N hN G hg
  refine ⟨a,?_⟩
  rw [← he]
  unfold sqNorm dot
  exact Finset.sum_congr rfl (fun n hn => by dsimp only; rw [ha n hn])

end RHConnections.ArithmeticFourierMertensKernel
