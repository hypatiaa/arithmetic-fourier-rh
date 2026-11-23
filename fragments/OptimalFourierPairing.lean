import Verified

open Finset ArithmeticFunction
noncomputable section
namespace RHConnections.ArithmeticFourierShell
open ArithmeticFourierInversion

def positiveMobius (C : Finset ℕ) : Finset ℕ := C.filter (fun n => muR n = 1)
def negativeMobius (C : Finset ℕ) : Finset ℕ := C.filter (fun n => muR n = -1)

private theorem muR_signs (n : ℕ) : muR n = 0 ∨ muR n = 1 ∨ muR n = -1 := by
  rcases moebius_eq_or n with h|h|h
  all_goals unfold muR; simp [ArithmeticFunction.intCoe_apply,h]

private theorem opposite_sets_disjoint (C : Finset ℕ) :
    Disjoint (positiveMobius C) (negativeMobius C) := by
  rw [Finset.disjoint_left]
  intro n hn hm
  have h1 : muR n = 1 := (Finset.mem_filter.mp hn).2
  have h2 : muR n = -1 := (Finset.mem_filter.mp hm).2
  linarith

theorem nonzeroMobius_partition (C : Finset ℕ) :
    nonzeroMobius C = positiveMobius C ∪ negativeMobius C := by
  ext n
  simp only [nonzeroMobius,positiveMobius,negativeMobius,Finset.mem_filter,Finset.mem_union]
  rcases muR_signs n with h|h|h <;> norm_num [h]

theorem signed_sum_count_difference (C : Finset ℕ) :
    (∑ n ∈ C, muR n) = ((positiveMobius C).card:ℝ)-((negativeMobius C).card:ℝ) := by
  have hS : ∑ n ∈ nonzeroMobius C, muR n = ∑ n ∈ C, muR n := by
    apply sum_subset (Finset.filter_subset _ _)
    intro n hn hnz
    by_contra h
    exact hnz (Finset.mem_filter.mpr ⟨hn,h⟩)
  rw [← hS,nonzeroMobius_partition,sum_union (opposite_sets_disjoint C)]
  have hp : (∑ n ∈ positiveMobius C,muR n) = (positiveMobius C).card := by
    calc
      _ = ∑ _n ∈ positiveMobius C, (1:ℝ) := Finset.sum_congr rfl
        (fun _ hn => (Finset.mem_filter.mp hn).2)
      _ = _ := by simp
  have hn : (∑ n ∈ negativeMobius C,muR n) = -((negativeMobius C).card:ℝ) := by
    calc
      _ = ∑ _n ∈ negativeMobius C, (-1:ℝ) := Finset.sum_congr rfl
        (fun _ hn => (Finset.mem_filter.mp hn).2)
      _ = _ := by simp
  rw [hp,hn,sub_eq_add_neg]

theorem balanced_complement_nonzero_lower {X : ℕ} {A : Finset ℕ}
    (hA : A ⊆ upperOddShell X) (hzero : ∑ n ∈ A,muR n = 0) :
    |M X| ≤ ((nonzeroMobius (upperOddShell X \ A)).card:ℝ) := by
  let C := upperOddShell X \ A
  have hs : ∑ n ∈ C,muR n = M X := balanced_complement_sum_eq_M hA hzero
  rw [← hs,signed_sum_count_difference,nonzeroMobius_partition,
    card_union_of_disjoint (opposite_sets_disjoint C),Nat.cast_add]
  exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)])

theorem optimal_balanced_extension {X : ℕ} {A : Finset ℕ}
    (hA : A ⊆ upperOddShell X) (hzero : ∑ n ∈ A,muR n = 0) :
    ∃ U V : Finset ℕ, U ⊆ positiveMobius (upperOddShell X \ A) ∧
      V ⊆ negativeMobius (upperOddShell X \ A) ∧ Nonempty (↥U ≃ ↥V) ∧
      let B := A ∪ (U ∪ V)
      A ⊆ B ∧ B ⊆ upperOddShell X ∧ (∑ n ∈ B,muR n) = 0 ∧
      ((nonzeroMobius (upperOddShell X \ B)).card:ℝ) = |M X| := by
  classical
  let C := upperOddShell X \ A
  let P := positiveMobius C
  let N := negativeMobius C
  let k := min P.card N.card
  obtain ⟨U,hU,hUcard⟩ := Finset.exists_subset_card_eq (min_le_left P.card N.card)
  obtain ⟨V,hV,hVcard⟩ := Finset.exists_subset_card_eq (min_le_right P.card N.card)
  have hcEq : U.card = V.card := hUcard.trans hVcard.symm
  have hUC : U ⊆ C := hU.trans (filter_subset _ _)
  have hVC : V ⊆ C := hV.trans (filter_subset _ _)
  have hPN : Disjoint P N := opposite_sets_disjoint C
  have hUV : Disjoint U V := hPN.mono hU hV
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    exact fun _ h hn => (Finset.mem_sdiff.mp hn).2 h
  have hAC' : Disjoint A (U ∪ V) := hAC.mono_right (Finset.union_subset hUC hVC)
  let B := A ∪ (U ∪ V)
  have hBC : B ⊆ upperOddShell X := Finset.union_subset hA
    ((Finset.union_subset hUC hVC).trans Finset.sdiff_subset)
  have hBsum : ∑ n ∈ B, muR n = 0 := by
    change (∑ n ∈ A ∪ (U ∪ V), muR n) = 0
    rw [sum_union hAC',hzero,zero_add,sum_union hUV]
    rw [sum_congr rfl (fun _ hn => (Finset.mem_filter.mp (hU hn)).2),
      sum_congr rfl (fun _ hn => (Finset.mem_filter.mp (hV hn)).2)]
    simp [hcEq]
  have he : Nonempty (↥U ≃ ↥V) := by
    refine ⟨Fintype.equivOfCardEq ?_⟩
    simp [hcEq]
  refine ⟨U,V,hU,hV,he,Finset.subset_union_left,hBC,hBsum,?_⟩
  have hPdiff : positiveMobius (upperOddShell X \ B) = P \ U := by
    ext n
    simp only [positiveMobius,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union,B,P,C]
    constructor
    · rintro ⟨⟨hn,hnot⟩,hp⟩
      exact ⟨⟨⟨hn,fun h => hnot (Or.inl h)⟩,hp⟩,fun h => hnot (Or.inr (Or.inl h))⟩
    · rintro ⟨⟨⟨hn,ha⟩,hp⟩,hu⟩
      refine ⟨⟨hn,?_⟩,hp⟩
      rintro (hA'|hU'|hV')
      · exact ha hA'
      · exact hu hU'
      · have hn' : muR n = -1 := (Finset.mem_filter.mp (hV hV')).2
        linarith
  have hNdiff : negativeMobius (upperOddShell X \ B) = N \ V := by
    ext n
    simp only [negativeMobius,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union,B,N,C]
    constructor
    · rintro ⟨⟨hn,hnot⟩,hp⟩
      exact ⟨⟨⟨hn,fun h => hnot (Or.inl h)⟩,hp⟩,fun h => hnot (Or.inr (Or.inr h))⟩
    · rintro ⟨⟨⟨hn,ha⟩,hp⟩,hu⟩
      refine ⟨⟨hn,?_⟩,hp⟩
      rintro (hA'|hU'|hV')
      · exact ha hA'
      · have hn' : muR n = 1 := (Finset.mem_filter.mp (hU hU')).2
        linarith
      · exact hu hV'
  have hM := balanced_complement_sum_eq_M hA hzero
  rw [signed_sum_count_difference] at hM
  change (P.card:ℝ)-(N.card:ℝ) = M X at hM
  change ((nonzeroMobius (upperOddShell X \ B)).card:ℝ) = |M X|
  rw [nonzeroMobius_partition,card_union_of_disjoint (opposite_sets_disjoint _),hPdiff,hNdiff,
    card_sdiff_of_subset hU,card_sdiff_of_subset hV,← hM,Nat.cast_add,
    Nat.cast_sub (Finset.card_le_card hU),Nat.cast_sub (Finset.card_le_card hV)]
  have hu : U.card = k := hUcard
  have hv : V.card = k := hVcard
  rw [hu,hv]
  rcases le_total P.card N.card with h | h
  · have h' : (P.card:ℝ) ≤ N.card := by exact_mod_cast h
    simp only [k,min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h')]
    ring
  · have h' : (N.card:ℝ) ≤ P.card := by exact_mod_cast h
    simp only [k,min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h')]
    ring

end RHConnections.ArithmeticFourierShell
