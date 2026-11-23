import Verified

noncomputable section
open Set

namespace RHConnections.BlockFourier

def realActiveLength (J : ℕ) (u : ℕ → ℝ) (y : ℝ) : ℕ :=
  ((Finset.range J).filter fun j => u j≤y).card

theorem real_active_filter (J : ℕ) (u : ℕ → ℝ) (hu : Monotone u) (y : ℝ) :
    (Finset.range J).filter (fun j => u j≤y) = Finset.range (realActiveLength J u y) := by
  induction J with
  | zero => simp [realActiveLength]
  | succ J ih =>
    by_cases hy : u J≤y
    · have he : (Finset.range (J+1)).filter (fun j => u j≤y)=Finset.range (J+1) := by
        apply Finset.filter_true_of_mem
        intro j hj
        exact (hu (by have := Finset.mem_range.mp hj; omega)).trans hy
      rw [he,realActiveLength,he,Finset.card_range]
    · have he : (Finset.range (J+1)).filter (fun j => u j≤y) =
          (Finset.range J).filter (fun j => u j≤y) := by
        rw [Finset.range_add_one,Finset.filter_insert]
        simp [hy]
      rw [he,realActiveLength,he]
      exact ih

theorem real_grid_rounding (J : ℕ) (u : ℕ → ℝ) (hu : Monotone u)
    {H y : ℝ} (hH : 0≤H) (uy : u 0≤y) (hy : y≤u J)
    (hwidth : ∀ j<J, u (j+1)-u j≤H) :
    let k := realActiveLength J u y
    k≤J ∧ y≤u k ∧ u k-y≤H := by
  let k := realActiveLength J u y
  have hk : k≤J := by unfold k realActiveLength; exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range J)
  have hkLo : y≤u k := by
    rcases lt_or_eq_of_le hk with hlt | he
    · by_contra! hn
      have hm : k∈(Finset.range J).filter (fun j => u j≤y) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt,hn.le⟩
      rw [real_active_filter J u hu y,Finset.mem_range] at hm
      exact (lt_irrefl k) hm
    · simpa only [he] using hy
  refine ⟨hk,hkLo,?_⟩
  change u k-y≤H
  by_cases hz : k=0
  · rw [hz]
    linarith
  · have hp : k-1<k := by omega
    have hprev := Finset.mem_range.mpr hp
    rw [show k=realActiveLength J u y from rfl,←real_active_filter J u hu y] at hprev
    have hyn := (Finset.mem_filter.mp hprev).2
    have hw := hwidth (k-1) (hp.trans_le hk)
    rw [show k-1+1=k by omega] at hw
    linarith

theorem real_grid_potential (J : ℕ) (u : ℕ → ℝ) (hu : Monotone u) (y : ℝ) (F : ℝ → ℂ) :
    (∑ j ∈ (Finset.range J).filter (fun j => u j≤y),(F (u (j+1))-F (u j))) =
      F (u (realActiveLength J u y))-F (u 0) := by
  rw [real_active_filter J u hu y]
  generalize realActiveLength J u y = k
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ,ih]; ring

theorem real_grid_interval_discretization (J : ℕ) (u : ℕ → ℝ) (hu : Monotone u)
    {H D a b : ℝ} (hH : 0≤H) (hD : 0≤D)
    (ha : a ∈ Icc (u 0) (u J)) (hb : b ∈ Icc (u 0) (u J))
    (hwidth : ∀ j<J, u (j+1)-u j≤H)
    (F : ℝ → ℂ) (hLip : ∀ x∈Icc (u 0) (u J), ∀ y∈Icc (u 0) (u J),
      ‖F x-F y‖≤D*|x-y|) :
    let ka := realActiveLength J u a
    let kb := realActiveLength J u b
    ‖(F (u kb)-F (u ka))-(F b-F a)‖≤2*D*H := by
  obtain ⟨hka,hau,hda⟩ := real_grid_rounding J u hu hH ha.1 ha.2 hwidth
  obtain ⟨hkb,hbu,hdb⟩ := real_grid_rounding J u hu hH hb.1 hb.2 hwidth
  let ka := realActiveLength J u a
  let kb := realActiveLength J u b
  have hfa := hLip (u ka) ⟨hu (Nat.zero_le _),hu hka⟩ a ha
  have hfb := hLip (u kb) ⟨hu (Nat.zero_le _),hu hkb⟩ b hb
  rw [abs_of_nonneg (sub_nonneg.mpr hau)] at hfa
  rw [abs_of_nonneg (sub_nonneg.mpr hbu)] at hfb
  change ‖(F (u kb)-F (u ka))-(F b-F a)‖≤_
  rw [show (F (u kb)-F (u ka))-(F b-F a)=(F (u kb)-F b)-(F (u ka)-F a) by ring]
  refine (norm_sub_le _ _).trans ?_
  linarith only [hfa,hfb,mul_le_mul_of_nonneg_left hda hD,mul_le_mul_of_nonneg_left hdb hD]

theorem real_grid_interval_length_rounding (J : ℕ) (u : ℕ → ℝ) (hu : Monotone u)
    {H a b : ℝ} (hH : 0≤H) (ha : a ∈ Icc (u 0) (u J)) (hb : b ∈ Icc (u 0) (u J))
    (hwidth : ∀ j<J, u (j+1)-u j≤H)
    (hmesh : ∀ j≤J, |u j-(u 0+(j:ℝ)*H)|≤H) :
    let ka := realActiveLength J u a
    let kb := realActiveLength J u b
    |(b-a)-((kb:ℝ)-(ka:ℝ))*H|≤4*H := by
  obtain ⟨hka,hau,hda⟩ := real_grid_rounding J u hu hH ha.1 ha.2 hwidth
  obtain ⟨hkb,hbu,hdb⟩ := real_grid_rounding J u hu hH hb.1 hb.2 hwidth
  let ka := realActiveLength J u a
  let kb := realActiveLength J u b
  have hal := abs_le.mp (hmesh ka hka)
  have hbl := abs_le.mp (hmesh kb hkb)
  change |(b-a)-((kb:ℝ)-(ka:ℝ))*H|≤4*H
  exact abs_le.mpr ⟨by linarith [hal.1,hal.2,hbl.1,hbl.2],by linarith [hal.1,hal.2,hbl.1,hbl.2]⟩

end RHConnections.BlockFourier
