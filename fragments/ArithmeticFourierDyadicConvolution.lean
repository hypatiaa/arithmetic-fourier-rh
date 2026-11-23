import Verified

open ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierDyadic
open ArithmeticFourierInversion ArithmeticFourierShortBlocks

def aggregate {ι : Type*} (J : Finset ι) (u : ι → ℕ) (d : ι → ℝ) (F : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ j ∈ J, d j * F (X / u j)

private theorem aggregate_convolution {ι : Type*} (J : Finset ι) (u : ι → ℕ) (d : ι → ℝ)
    (F V : ℕ → ℝ) (g₀ : ℕ → ℝ) (hF : F 0 = 0)
    (hV : ∀ n, V n = ∑ k ∈ Finset.Ioc 0 n, g₀ k * F (n/k))
    (X Q : ℕ) (hu : ∀ j ∈ J, Q ≤ u j) (hQ : 0<Q) :
    aggregate J u d V X = ∑ k ∈ Finset.Ioc 0 (X/Q),g₀ k * aggregate J u d F (X/k) := by
  classical
  have extend (j : ι) (hj : j ∈ J) :
      V (X/u j) = ∑ k ∈ Finset.Ioc 0 (X/Q), g₀ k * F ((X/u j)/k) := by
    rw [hV (X/u j)]
    apply Finset.sum_subset
    · intro k hk
      obtain ⟨hk0,hkm⟩ := Finset.mem_Ioc.mp hk
      exact Finset.mem_Ioc.mpr ⟨hk0,hkm.trans (Nat.div_le_div_left (hu j hj) hQ)⟩
    · intro k hk hkn
      have hlt : X/u j < k := by
        by_contra! h
        exact hkn (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hk).1,h⟩)
      rw [Nat.div_eq_of_lt hlt,hF,mul_zero]
  unfold aggregate
  calc
    _ = ∑ j ∈ J, ∑ k ∈ Finset.Ioc 0 (X/Q), g₀ k*(d j*F ((X/k)/u j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [extend j hj,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,mul_comm k (u j)]
      ring
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

theorem forward_aggregate {ι : Type*} (J : Finset ι) (u : ι → ℕ) (d : ι → ℝ)
    (B X Q : ℕ) (hu : ∀ j ∈ J, Q ≤ u j) (hQ : 0<Q) :
    aggregate J u d (S B) X = ∑ k ∈ Finset.Ioc 0 (X/Q),g B k * aggregate J u d M (X/k) :=
  aggregate_convolution J u d M (S B) (g B) (by simp [M]) (S_from_M B) X Q hu hQ

theorem inverse_aggregate {ι : Type*} (J : Finset ι) (u : ι → ℕ) (d : ι → ℝ)
    (B X Q : ℕ) (hu : ∀ j ∈ J, Q ≤ u j) (hQ : 0<Q) :
    aggregate J u d M X = ∑ k ∈ Finset.Ioc 0 (X/Q),h B k * aggregate J u d (S B) (X/k) :=
  aggregate_convolution J u d (S B) M (h B) (by simp [S]) (M_from_S B) X Q hu hQ

theorem aggregate_sub_weights {ι : Type*} (J : Finset ι) (u : ι → ℕ) (d c : ι → ℝ)
    (F : ℕ → ℝ) (X : ℕ) :
    aggregate J u (fun j => d j-c j) F X =
      aggregate J u d F X-aggregate J u c F X := by
  simp only [aggregate,sub_mul,Finset.sum_sub_distrib]

theorem aggregate_correction_bound {ι : Type*} (J : Finset ι) (u : ι → ℕ) (c : ι → ℝ)
    (F : ℕ → ℝ) (hF : ∀ n, |F n|≤(n:ℝ)) (X Q : ℕ)
    (hu : ∀ j ∈ J, Q ≤ u j) (hQ : 0<Q) (hc : ∀ j ∈ J, 0 ≤ c j) :
    |aggregate J u c F X| ≤ ((X/Q:ℕ):ℝ) * ∑ j ∈ J, c j := by
  unfold aggregate
  calc
    _ ≤ ∑ j ∈ J, |c j * F (X/u j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ J, ((X/Q:ℕ):ℝ)*c j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul,abs_of_nonneg (hc j hj),mul_comm ((X/Q:ℕ):ℝ)]
      exact mul_le_mul_of_nonneg_left ((hF _).trans (by exact_mod_cast
        (Nat.div_le_div_left (hu j hj) hQ))) (hc j hj)
    _ = _ := (Finset.mul_sum ..).symm

theorem forward_corrected_aggregate {ι : Type*} (J : Finset ι) (u : ι → ℕ) (d c : ι → ℝ)
    (B X Q : ℕ) (hu : ∀ j ∈ J, Q ≤ u j) (hQ : 0<Q) (hc : ∀ j ∈ J, 0 ≤ c j) :
    |aggregate J u (fun j => d j-c j) (S B) X -
      ∑ k ∈ Finset.Ioc 0 (X/Q),g B k * aggregate J u d M (X/k)| ≤
      ((X/Q:ℕ):ℝ) * ∑ j ∈ J, c j := by
  rw [← forward_aggregate J u d B X Q hu hQ,aggregate_sub_weights,sub_sub_cancel_left,abs_neg]
  have hz : S B 0=0 := by simp [S]
  exact aggregate_correction_bound J u c (S B) (fun n => by
    simpa [hz] using scalar_S_lipschitz B 0 n (Nat.zero_le _)) X Q hu hQ hc

theorem inverse_corrected_aggregate {ι : Type*} (J : Finset ι) (u : ι → ℕ) (d c : ι → ℝ)
    (B X Q : ℕ) (hu : ∀ j ∈ J, Q ≤ u j) (hQ : 0<Q) (hc : ∀ j ∈ J, 0 ≤ c j) :
    |aggregate J u d M X -
      ∑ k ∈ Finset.Ioc 0 (X/Q),h B k * aggregate J u (fun j => d j-c j) (S B) (X/k)| ≤
      ((X/Q:ℕ):ℝ) * ∑ j ∈ J, c j := by
  rw [← inverse_aggregate J u (fun j => d j-c j) B X Q hu hQ,aggregate_sub_weights,sub_sub_cancel]
  have hz : M 0=0 := by simp [M]
  exact aggregate_correction_bound J u c M (fun n => by
    simpa [hz] using mertens_M_lipschitz 0 n (Nat.zero_le _)) X Q hu hQ hc

end RHConnections.ArithmeticFourierDyadic
