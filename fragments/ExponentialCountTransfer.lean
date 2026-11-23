import Verified

noncomputable section
namespace RHConnections.PhaseWindow

theorem weighted_exponential_from_counts {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i∈s, 0≤a i) {C : ℝ} (hC : 0≤C)
    (hcount : ∀ u : ℝ, 0≤u →
      (((s.filter (fun i => a i≤u)).card:ℕ):ℝ) ≤ C*Real.exp (u/2)) :
    (∑ i∈s,Real.exp (-a i)) ≤
      (C*Real.exp (1/2))*(1-Real.exp (-(1/2)))⁻¹ := by
  classical
  let k (i : ι) := ⌊a i⌋₊
  let J := s.image k
  let r := Real.exp (-(1/2))
  let B := C*Real.exp (1/2)
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hB : 0≤B := by dsimp [B]; positivity
  have hmaps : ∀ i∈s, k i∈J := fun i hi => Finset.mem_image_of_mem _ hi
  have hbin (j : ℕ) : (∑ i∈s with k i=j, Real.exp (-a i)) ≤ B*r^j := by
    let S := s.filter (fun i => k i=j)
    have hs : S⊆s.filter (fun i => a i≤(j:ℝ)+1) := by
      intro i hi
      obtain ⟨his,hij⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨his,?_⟩
      have hh := Nat.lt_floor_add_one (a i)
      change a i<(k i:ℝ)+1 at hh
      simpa only [hij] using hh.le
    have hc : (S.card:ℝ)≤C*Real.exp (((j:ℝ)+1)/2) := by
      exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (hcount (j+1) (by positivity))
    have he (i) (hi : i∈S) : Real.exp (-a i)≤Real.exp (-(j:ℝ)) := by
      obtain ⟨his,hij⟩ := Finset.mem_filter.mp hi
      have h := Nat.floor_le (ha i his)
      change (k i:ℝ)≤a i at h
      rw [hij] at h
      exact Real.exp_le_exp.mpr (neg_le_neg h)
    calc
      _ ≤ ∑ _i∈S,Real.exp (-(j:ℝ)) := Finset.sum_le_sum he
      _ = (S.card:ℝ)*Real.exp (-(j:ℝ)) := by simp [nsmul_eq_mul]
      _ ≤ (C*Real.exp (((j:ℝ)+1)/2))*Real.exp (-(j:ℝ)) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = B*r^j := by
        dsimp [B,r]
        rw [←Real.exp_nat_mul, mul_assoc, ←Real.exp_add]
        conv_rhs => rw [mul_assoc,←Real.exp_add]
        rw [show ((j:ℝ)+1)/2+ -(j:ℝ)=1/2+(j:ℝ)* -(1/2) by ring]
  calc
    _ = ∑ j∈J,∑ i∈s with k i=j, Real.exp (-a i) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ j∈J,B*r^j := Finset.sum_le_sum (fun j _ => hbin j)
    _ = B*(∑ j∈J,r^j) := (Finset.mul_sum ..).symm
    _ ≤ B*(∑' j : ℕ,r^j) := mul_le_mul_of_nonneg_left
      ((summable_geometric_of_lt_one hr0 hr1).sum_le_tsum J (fun _ _ => by positivity)) hB
    _ = _ := by rw [tsum_geometric_of_lt_one hr0 hr1]

end RHConnections.PhaseWindow
