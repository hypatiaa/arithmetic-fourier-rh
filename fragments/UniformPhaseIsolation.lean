import Verified
import PhaseWindowFactors

noncomputable section
open Filter
open scoped Topology
namespace RHConnections.PhaseWindow

private theorem small_signed_window {ι : Type*} (s : Finset ι) (freq : ι → ℂ)
    (hzero : ∀ i ∈ s, freq i≠0) {W : ℝ} (hW : 0<W) :
    ∃ L : List Shift, windowWidth L≤W ∧ (∀ e∈L, 0≤e.offset) ∧
      ∀ i∈s, ∃ e∈L, shiftFactor (freq i) e=0 := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty => exact ⟨[],by simpa [windowWidth] using hW.le,by simp,by simp⟩
  | insert i s hi ih =>
    have hW2 : 0<W/2 := by positivity
    obtain ⟨e,he,heW,hei⟩ := exists_signed_shift (hzero i (Finset.mem_insert_self _ _)) hW2
    obtain ⟨L,hL,hpos,hkill⟩ := ih (fun j hj => hzero j (Finset.mem_insert_of_mem hj)) hW2
    refine ⟨e::L,?_,?_,?_⟩
    · change e.offset+windowWidth L≤W
      linarith
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact he.le
      · exact hpos f hf
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨e,List.mem_cons_self ..,hei⟩
      · obtain ⟨f,hf,hfkill⟩ := hkill j hj
        exact ⟨f,List.mem_cons_of_mem _ hf,hfkill⟩

private theorem opposite_phase_window {ι : Type*} (s : Finset ι) (freq : ι → ℂ)
    (hzero : ∀ i∈s, (freq i).im≠0) :
    ∃ L : List Shift, windowWidth L=∑ i∈s,oppositeOffset (freq i) ∧
      windowCost L=1 ∧ (∀ e∈L, 0≤e.offset) ∧
      ∀ i∈s, ∃ e∈L, shiftFactor (freq i) e=0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[],by simp [windowWidth],by simp [windowCost],by simp,by simp⟩
  | insert i s hi ih =>
    let e := oppositeShift (freq i)
    have hz := hzero i (Finset.mem_insert_self _ _)
    obtain ⟨L,hL,hCost,hpos,hkill⟩ := ih (fun j hj => hzero j (Finset.mem_insert_of_mem hj))
    refine ⟨e::L,?_,?_,?_,?_⟩
    · simp only [windowWidth,List.map_cons,List.sum_cons,Finset.sum_insert hi]
      exact congrArg (oppositeOffset (freq i)+·) hL
    · simp only [windowCost,List.map_cons,List.prod_cons,show e=oppositeShift (freq i) from rfl,
        opposite_shift_cost,one_mul]
      exact hCost
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact (opposite_offset_positive hz).le
      · exact hpos f hf
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨e,List.mem_cons_self ..,opposite_shift_kills hz⟩
      · obtain ⟨f,hf,hfkill⟩ := hkill j hj
        exact ⟨f,List.mem_cons_of_mem _ hf,hfkill⟩

private theorem window_annihilates_sum {ι : Type*} (s : Finset ι)
    (A freq : ι → ℂ) (steps : List Shift) (z : ℝ)
    (hk : ∀ i∈s, ∃ e∈steps, shiftFactor (freq i) e=0) :
    applyWindow (fun x => ∑ i∈s,A i*Complex.exp (freq i*(x:ℂ))) z steps=0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,window_keeps_constants]
  | insert i s hi ih =>
    obtain ⟨e,he,hekill⟩ := hk i (Finset.mem_insert_self _ _)
    have hzero := window_kills_mode he hekill z
    simp only [Finset.sum_insert hi,apply_window_add,apply_window_mul_const,hzero,mul_zero,
      ih (fun j hj => hk j (Finset.mem_insert_of_mem hj)),add_zero]

theorem uniform_window_isolation {ι : Type*} (freq : ι → ℂ)
    (hzero : ∀ i, freq i≠0)
    (hreal : ∃ S : Finset ι, ∀ i, (freq i).im=0 → i∈S)
    (hsum : Summable (fun i => oppositeOffset (freq i))) {W : ℝ} (hW : 0<W) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Finset ι) (A : ι → ℂ) (target : ℂ) (B : ℝ),
      (∀ x ∈ Set.Icc 0 W, ‖target+∑ i∈s,A i*Complex.exp (freq i*(x:ℂ))‖≤B) →
      ‖target‖ ≤ C*B := by
  classical
  obtain ⟨S,hS⟩ := hreal
  have hW₂ : 0<W/2 := by positivity
  obtain ⟨T,hT⟩ := summable_iff_vanishing.mp hsum _ (Iio_mem_nhds hW₂)
  let near := T∪S
  obtain ⟨K,hKw,hKp,hKk⟩ := small_signed_window near freq (fun i _ => hzero i) hW₂
  have hKcost : 0≤windowCost K := List.prod_nonneg (fun r hr => by
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hr
    positivity)
  refine ⟨windowCost K,hKcost,?_⟩
  intro s A target B hb
  let far := s\near
  have hfd : Disjoint far T := by
    apply Finset.disjoint_left.mpr
    intro i hi hT
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hT)
  have hfzero (i) (hi : i∈far) : (freq i).im≠0 :=
    fun hz => (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_right _ (hS i hz))
  obtain ⟨L,hLw,hLc,hLp,hLk⟩ := opposite_phase_window far freq hfzero
  have hLsmall : windowWidth L < W/2 := by
    rw [hLw]
    exact hT far hfd
  let all := K++L
  have hallw : windowWidth all≤W := by
    change ((K++L).map Shift.offset).sum≤W
    rw [List.map_append,List.sum_append]
    change windowWidth K+windowWidth L≤W
    linarith
  have hallc : windowCost all=windowCost K := by
    change ((K++L).map _).prod = windowCost K
    rw [List.map_append,List.prod_append]
    change windowCost K*windowCost L=windowCost K
    rw [hLc,mul_one]
  have hallp (e) (he : e∈all) : 0≤e.offset := by
    rcases List.mem_append.mp he with h | h
    · exact hKp e h
    · exact hLp e h
  have hallk (i) (hi : i∈s) : ∃ e∈all, shiftFactor (freq i) e=0 := by
    by_cases hn : i∈near
    · obtain ⟨e,he,h⟩ := hKk i hn
      exact ⟨e,List.mem_append_left _ he,h⟩
    · obtain ⟨e,he,h⟩ := hLk i (Finset.mem_sdiff.mpr ⟨hi,hn⟩)
      exact ⟨e,List.mem_append_right _ he,h⟩
  have hA := apply_window_cost (fun x => target+∑ i∈s,A i*Complex.exp (freq i*(x:ℂ)))
    all 0 B hallp (fun x hl hr => hb x ⟨hl,by simpa only [zero_add] using hr.trans (by simpa using hallw)⟩)
  rw [apply_window_add,window_keeps_constants,window_annihilates_sum s A freq all 0 hallk,add_zero,hallc,mul_comm] at hA
  exact hA

end RHConnections.PhaseWindow
