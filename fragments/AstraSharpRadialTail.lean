import Verified
open Filter Set
noncomputable section
namespace RHConnections.SharpRadialTail
open SpectralTail

abbrev mass (r : NontrivialZetaZero) : ℝ := analyticOrderNatAt riemannZeta r.val

private theorem annulus_count : ∃ A : ℝ, 0 ≤ A ∧ ∀ (j : ℕ) (s : Finset NontrivialZetaZero),
    (∀ r ∈ s, ‖r.val‖ < (2:ℝ)^(j+1)) →
    ∑ r ∈ s, mass r ≤ A*((j:ℝ)+1)*2^j := by
  obtain ⟨C,hC,hcnt⟩ := zeta_quantitative_zero_count
  let N (t : ℝ) := C*(max t 1+2)*Real.log (max t 1+2)
  refine ⟨8*C*Real.log 2,by positivity,?_⟩
  intro j s hs
  apply le_trans _ (cumulative_count_dyadic N C hC (fun t ht => by simp [N,max_eq_left ht]) j)
  exact hcnt (max ((2:ℝ)^(j+1)) 1) s (le_max_right _ _)
    (fun r hr => ((Complex.abs_im_le_norm r.val).trans (hs r hr).le).trans (le_max_left _ _))

theorem high_inverse_square : ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℕ,
    (∑' r : {r : NontrivialZetaZero // (2:ℝ)^J ≤ ‖r.val‖}, mass r.val/‖r.val.val‖^2) ≤
      C*((J:ℝ)+1)/(2:ℝ)^J := by
  classical
  obtain ⟨A,hA,hcount⟩ := annulus_count
  let g (j : ℕ) := ((j:ℝ)+1)*(1/2:ℝ)^j
  have hg : Summable g := by
    have hq : ‖(1/2:ℝ)‖ < 1 := by norm_num
    simpa only [g,pow_one,add_mul,one_mul,Pi.add_apply] using
      (summable_pow_mul_geometric_of_norm_lt_one (R:=ℝ) 1 hq).add (summable_geometric_of_norm_lt_one hq)
  have hgn (j : ℕ) : 0 ≤ g j := by dsimp [g]; positivity
  refine ⟨A*(∑' j, g j),mul_nonneg hA (tsum_nonneg hgn),?_⟩
  intro J
  let H := (2:ℝ)^J
  have hH : 0 < H := by positivity
  let Z := {r : NontrivialZetaZero // H ≤ ‖r.val‖}
  let bin (r : Z) := heightBin (‖r.val.val‖/H)
  let f (r : Z) := mass r.val/‖r.val.val‖^2
  let D := A*((J:ℝ)+1)/H
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrange (r : Z) : (2:ℝ)^(J+bin r) ≤ ‖r.val.val‖ ∧ ‖r.val.val‖ < (2:ℝ)^(J+bin r+1) := by
    have hn : 0 ≤ ‖r.val.val‖/H := div_nonneg (norm_nonneg _) hH.le
    have hU := heightBin_upper (‖r.val.val‖/H)
    rw [abs_of_nonneg hn] at hU
    have hL : (2:ℝ)^(bin r) ≤ ‖r.val.val‖/H := by
      by_cases h : bin r=0
      · simpa only [h,pow_zero] using (one_le_div hH).mpr r.property
      · simpa only [bin,abs_of_nonneg hn] using heightBin_lower (‖r.val.val‖/H) h
    constructor
    · simpa only [pow_add,mul_comm,H] using (le_div_iff₀ hH).mp hL
    · rw [Nat.add_assoc,pow_add]
      exact ((div_lt_iff₀ hH).mp hU).trans_eq (mul_comm _ _)
  have hbin (j : ℕ) (s : Finset Z) (hs : ∀ r ∈ s, bin r=j) :
      (∑ r ∈ s, f r) ≤ D*g j := by
    let e : Z ↪ NontrivialZetaZero := ⟨Subtype.val,Subtype.val_injective⟩
    have hh := hcount (J+j) (s.map e) (by
      intro r hr
      obtain ⟨t,ht,rfl⟩ := Finset.mem_map.mp hr
      change ‖t.val.val‖ < (2:ℝ)^(J+j+1)
      simpa only [hs t ht] using (hrange t).2)
    simp only [e,Finset.sum_map,Function.Embedding.coeFn_mk] at hh
    let V := (2:ℝ)^(J+j)
    have hV : 0 < V := by positivity
    calc
      _ ≤ ∑ r ∈ s, mass r.val/V^2 := by
        apply Finset.sum_le_sum
        intro r hr
        have hx : V ≤ ‖r.val.val‖ := by simpa [V,hs r hr] using (hrange r).1
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (sq_pos_of_pos hV)
          (pow_le_pow_left₀ hV.le hx 2)
      _ = (∑ r ∈ s, mass r.val)/V^2 := (Finset.sum_div ..).symm
      _ ≤ (A*((J+j:ℕ)+1)*V)/V^2 := div_le_div_of_nonneg_right hh (sq_nonneg _)
      _ = A*((J:ℝ)+j+1)/V := by push_cast; field_simp
      _ ≤ A*(((J:ℝ)+1)*(j+1))/V := by
        apply div_le_div_of_nonneg_right _ hV.le
        apply mul_le_mul_of_nonneg_left _ hA
        nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) J) (Nat.cast_nonneg (α:=ℝ) j)]
      _ = D*g j := by simp [D,g,H,V,pow_add]; ring
  have hfin (s : Finset Z) : (∑ r ∈ s,f r) ≤ D*(∑' j, g j) := by
    calc
      _ = ∑ j ∈ s.image bin, ∑ r ∈ s.filter (fun r => bin r=j), f r :=
        (Finset.sum_fiberwise_of_maps_to (fun r hr => Finset.mem_image_of_mem bin hr) f).symm
      _ ≤ ∑ j ∈ s.image bin, D*g j := Finset.sum_le_sum fun j _ =>
        hbin j _ (fun r hr => (Finset.mem_filter.mp hr).2)
      _ ≤ ∑' j, D*g j := (hg.mul_left D).sum_le_tsum _ (fun j _ => mul_nonneg hD (hgn j))
      _ = _ := tsum_mul_left
  have hs := summable_of_sum_le (f:=f) (fun r => by dsimp [f,mass]; positivity) hfin
  exact (le_of_tendsto hs.hasSum (Eventually.of_forall hfin)).trans_eq (by dsimp only [D,H]; ring)

theorem low_inverse_first : ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℕ,
    (∑' r : {r : NontrivialZetaZero // ‖r.val‖ ≤ (2:ℝ)^J}, mass r.val/‖r.val.val‖) ≤
      C*((J:ℝ)+1)^2 := by
  classical
  obtain ⟨A,hA,hcount⟩ := annulus_count
  obtain ⟨δ,hδ,hδr⟩ := zeta_zero_norm_lower
  let B := max 1 δ⁻¹
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  refine ⟨A*B,mul_nonneg hA hB0,?_⟩
  intro J
  let Z := {r : NontrivialZetaZero // ‖r.val‖ ≤ (2:ℝ)^J}
  let bin (r : Z) := heightBin ‖r.val.val‖
  let f (r : Z) := mass r.val / ‖r.val.val‖
  have hn (r : Z) : 0 < ‖r.val.val‖ := hδ.trans_le (hδr _)
  have hupper (r : Z) : ‖r.val.val‖ < 2^(bin r+1) := by simpa [bin] using heightBin_upper ‖r.val.val‖
  have hlower (r : Z) (hr : bin r ≠ 0) : (2:ℝ)^(bin r) ≤ ‖r.val.val‖ := by
    simpa [bin] using heightBin_lower ‖r.val.val‖ hr
  have hbinJ (r : Z) : bin r ≤ J := by
    by_cases h : bin r=0
    · simp [h]
    · by_contra! bad
      exact (not_lt_of_ge ((hlower r h).trans r.property)) (pow_lt_pow_right₀ (by norm_num) bad)
  have hinv (r : Z) : ‖r.val.val‖⁻¹ ≤ B/(2:ℝ)^(bin r) := by
    by_cases h : bin r=0
    · rw [h,pow_zero,div_one]
      exact (inv_anti₀ hδ (hδr _)).trans (le_max_right _ _)
    · exact (inv_anti₀ (by positivity : (0:ℝ)<2^(bin r)) (hlower r h)).trans
        (by simpa only [one_div] using div_le_div_of_nonneg_right hB (by positivity : (0:ℝ)≤2^(bin r)))
  have hbin (j : ℕ) (s : Finset Z) (hs : ∀ r ∈ s, bin r=j) :
      (∑ r ∈ s, f r) ≤ A*B*((j:ℝ)+1) := by
    let e : Z ↪ NontrivialZetaZero := ⟨Subtype.val,Subtype.val_injective⟩
    have hh := hcount j (s.map e) (by
      intro r hr
      obtain ⟨t,ht,rfl⟩ := Finset.mem_map.mp hr
      change ‖t.val.val‖ < (2:ℝ)^(j+1)
      simpa only [hs t ht] using hupper t)
    simp only [e,Finset.sum_map,Function.Embedding.coeFn_mk] at hh
    calc
      _ ≤ ∑ r ∈ s, mass r.val*(B/(2:ℝ)^j) := by
        apply Finset.sum_le_sum
        intro r hr
        dsimp only [f]; rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa only [hs r hr] using hinv r) (Nat.cast_nonneg _)
      _ = (∑ r ∈ s, mass r.val)*(B/(2:ℝ)^j) := (Finset.sum_mul ..).symm
      _ ≤ (A*((j:ℝ)+1)*2^j)*(B/(2:ℝ)^j) := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = _ := by field_simp
  have hfin (s : Finset Z) : (∑ r ∈ s,f r) ≤ A*B*((J:ℝ)+1)^2 := by
    calc
      _ = ∑ j ∈ Finset.range (J+1), ∑ r ∈ s.filter (fun r => bin r=j), f r :=
        (Finset.sum_fiberwise_of_maps_to (fun r _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hbinJ r))) f).symm
      _ ≤ ∑ _j ∈ Finset.range (J+1), A*B*((J:ℝ)+1) := by
        apply Finset.sum_le_sum
        intro j hj
        apply (hbin j _ (fun r hr => (Finset.mem_filter.mp hr).2)).trans
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA hB0)
        have hle : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact_mod_cast Nat.add_le_add_right hle 1
      _ = _ := by simp; ring
  have hs := summable_of_sum_le (f:=f) (fun r => by dsimp [f,mass]; positivity) hfin
  exact le_of_tendsto hs.hasSum (Eventually.of_forall hfin)

#print axioms high_inverse_square
#print axioms low_inverse_first
end RHConnections.SharpRadialTail
