import Verified

noncomputable section
namespace RHConnections.MobiusRankLocalization
open RankPairing MobiusCrossingLengths ArithmeticFourierShell

def signSet (positive : Bool) (N : ℕ) : Finset ℕ :=
  if positive then positivePositions N else negativePositions N

theorem prefix_stable (s : Bool) {N n : ℕ} (hn : n ≤ N) :
    prefixCount (signSet s N) n = (signSet s n).card := by
  unfold prefixCount
  apply congrArg Finset.card
  ext i
  cases s <;> simp only [signSet, Bool.false_eq_true, ite_false, ite_true,
    negativePositions,positivePositions,positiveMobius,negativeMobius,Finset.mem_filter,Finset.mem_Ioc]
    <;> grind

theorem finite_window {N t w i : ℕ} {c ε : ℝ}
    (hw : w ≤ t) (hN : t+w ≤ N) (hε : 0 ≤ ε) (hgap : 3*ε*t ≤ c*w)
    (hcount : ∀ s : Bool, ∀ n ∈ ({t-w,t,t+w} : Finset ℕ),
      |((signSet s n).card:ℝ)-c*n| ≤ ε*n)
    (hiL : min ((signSet true t).card) ((signSet false t).card) ≤ i)
    (hiU : i < max ((signSet true t).card) ((signSet false t).card)) :
    ∀ s : Bool, i < (signSet s N).card ∧
      t-w < paddedAt N (signSet s N) i ∧ paddedAt N (signSet s N) i ≤ t+w := by
  intro s
  have hl := abs_le.mp (hcount s (t-w) (by simp))
  have hu := abs_le.mp (hcount s (t+w) (by simp))
  have h₁ := abs_le.mp (hcount true t (by simp))
  have h₂ := abs_le.mp (hcount false t (by simp))
  rw [Nat.cast_sub hw] at hl
  push_cast at hu
  have htw : (w:ℝ) ≤ t := by exact_mod_cast hw
  have hpos := mul_nonneg hε (Nat.cast_nonneg t : (0:ℝ) ≤ t)
  have hsmall := mul_le_mul_of_nonneg_left htw hε
  have hnon := mul_nonneg hε (Nat.cast_nonneg w : (0:ℝ) ≤ w)
  have hlo : (signSet s (t-w)).card ≤ min (signSet true t).card (signSet false t).card := by
    apply le_min <;> apply (Nat.cast_le (α := ℝ)).mp <;> linarith [hl.2,h₁.1,h₂.1]
  have hup : max (signSet true t).card (signSet false t).card ≤ (signSet s (t+w)).card := by
    apply max_le <;> apply (Nat.cast_le (α := ℝ)).mp <;> linarith [hu.1,h₁.2,h₂.2]
  have hl' := hlo.trans hiL
  have hu' := hiU.trans_le hup
  rw [← prefix_stable s (N := N) hN] at hu'
  rw [← prefix_stable s (N := N) (n := t-w) (by omega)] at hl'
  refine ⟨hu'.trans_le (Finset.card_filter_le _ _),?_,(padded_prefix hN).2 hu'⟩
  have hz := padded_prefix (S := signSet s N) (i := i) (t := t-w) (N := N) (by omega)
  omega

open ArithmeticFourierInversion

private theorem separated_of_spacing {N l u : ℕ} {B : ℝ} (hlu : l ≤ u) (hu : u ≤ N)
    (hlB : |M l| ≤ B) (huB : |M u| ≤ B) (hgap : 8*B+4*(u.sqrt:ℝ) ≤ ((u-l:ℕ):ℝ)) :
    max (prefixCount (signSet true N) l) (prefixCount (signSet false N) l) ≤
    min (prefixCount (signSet true N) u) (prefixCount (signSet false N) u) := by
  have hA : |M l|+|M u| ≤ (nonzeroActivity u:ℝ)-(nonzeroActivity l:ℝ) := by
    rw [nonzero_activity_interval hlu]
    linarith only [squarefree_interval_card_lower l u hlu,hlB,huB,hgap]
  have h1 := prefix_rank_imbalance (N := N) (hlu.trans hu)
  have h2 := prefix_rank_imbalance (N := N) hu
  have h3 := prefix_rank_activity (N := N) (hlu.trans hu)
  have h4 := prefix_rank_activity (N := N) hu
  rw [← h1,← h2,← h3,← h4,Nat.cast_add,Nat.cast_add] at hA
  apply RHConnections.CrossingPairing.separation_iff_activity.mpr
  exact_mod_cast (by linarith only [hA] :
    |(prefixCount (positivePositions N) l:ℝ)-prefixCount (negativePositions N) l|+
    |(prefixCount (positivePositions N) u:ℝ)-prefixCount (negativePositions N) u| ≤
    (prefixCount (positivePositions N) u:ℝ)+prefixCount (negativePositions N) u-
    prefixCount (positivePositions N) l-prefixCount (negativePositions N) l)

theorem activity_window {N t w i : ℕ} {B : ℝ} (hw : w ≤ t) (hN : t+w ≤ N)
    (hM : ∀ n ∈ ({t-w,t,t+w} : Finset ℕ), |M n| ≤ B)
    (hgap : 8*B+4*((t+w).sqrt:ℝ) ≤ w)
    (hiL : min ((signSet true t).card) ((signSet false t).card) ≤ i)
    (hiU : i < max ((signSet true t).card) ((signSet false t).card)) :
    ∀ s : Bool, i < (signSet s N).card ∧
      t-w < paddedAt N (signSet s N) i ∧ paddedAt N (signSet s N) i ≤ t+w := by
  have htN : t ≤ N := by omega
  have hrt : (t.sqrt : ℝ) ≤ (t+w).sqrt := by exact_mod_cast Nat.sqrt_le_sqrt (Nat.le_add_right t w)
  have hl := separated_of_spacing (N := N) (l := t-w) (u := t) (Nat.sub_le _ _) htN
    (hM _ (by simp)) (hM _ (by simp)) (by rw [show t-(t-w)=w by omega]; linarith)
  have hu := separated_of_spacing (N := N) (l := t) (u := t+w) (Nat.le_add_right t w) hN
    (hM _ (by simp)) (hM _ (by simp)) (by simpa using hgap)
  rw [← prefix_stable true htN,← prefix_stable false htN] at hiL hiU
  intro s
  have hlo : prefixCount (signSet s N) (t-w) ≤ i := by cases s <;> omega
  have hup : i < prefixCount (signSet s N) (t+w) := by cases s <;> omega
  have he := padded_prefix (N := N) (S := signSet s N) (i := i) (t := t-w) (by omega)
  exact ⟨hup.trans_le (Finset.card_filter_le _ _),by omega,(padded_prefix hN).2 hup⟩

open Filter
open scoped Topology

theorem mertens_sublinear {u : ℝ} (hu : 0 < u) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, |M n| ≤ u*n := by
  obtain ⟨a,C,ha,hC,hM⟩ := FinitePerron.quantitative_natural_mertens
  have ht : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n:ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hneg : Tendsto (fun n : ℕ => -a*Real.sqrt (Real.log (n:ℝ))) atTop atBot :=
    tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr ha) ht
  have h0 := (Real.tendsto_exp_atBot.comp hneg).const_mul C
  simp only [mul_zero] at h0
  obtain ⟨k,hk⟩ := eventually_atTop.mp (h0.eventually_lt_const hu)
  obtain ⟨k',hk'⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨max k k',fun n hn => ?_⟩
  have h := hM n (hk'.le.trans (by exact_mod_cast (le_max_right k k').trans hn))
  have h' := mul_le_mul_of_nonneg_right (hk n ((le_max_left k k').trans hn)).le (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  dsimp only [Function.comp_apply] at h'
  linarith

theorem uniform_interior {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℕ, ∀ t ≥ T, ∀ N : ℕ, 5*t ≤ 4*N → ∀ i : ℕ,
    min ((signSet true t).card) ((signSet false t).card) ≤ i →
    i < max ((signSet true t).card) ((signSet false t).card) →
    ∀ s : Bool, i < (signSet s N).card ∧
      |(paddedAt N (signSet s N) i:ℝ)-t| ≤ δ*t := by
  let η := min δ (1/4)
  have hη : 0 < η := lt_min hδ (by norm_num)
  have hη4 : η ≤ 1/4 := min_le_right _ _
  have hηδ : η ≤ δ := min_le_left _ _
  obtain ⟨k,hk⟩ := mertens_sublinear (show 0 < η/64 by positivity)
  obtain ⟨j,hj⟩ := exists_nat_gt (512/η^2 + 2/η)
  refine ⟨max (2*k) j,?_⟩
  intro t ht N hN i hiL hiU
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
  have hlarge : 512/η^2+2/η ≤ t := hj.le.trans (by exact_mod_cast (le_max_right (2*k) j).trans ht)
  have h512 : 512 ≤ η^2*t := by
    have hz := (div_le_iff₀ (sq_pos_of_pos hη)).mp (by linarith [show 0 ≤ 2/η by positivity] : 512/η^2 ≤ t)
    linarith
  have h2 : 2 ≤ η*t := by
    have hz := (div_le_iff₀ hη).mp (by linarith [show 0 ≤ 512/η^2 by positivity] : 2/η ≤ t)
    linarith
  let w := ⌊η*t⌋₊
  have hwU : (w:ℝ) ≤ η*t := Nat.floor_le (mul_nonneg hη.le ht0)
  have hwL : η*t < (w:ℝ)+1 := Nat.lt_floor_add_one _
  have hw4 : 4*w ≤ t := by
    exact_mod_cast (show 4*(w:ℝ) ≤ t by linarith [mul_le_mul_of_nonneg_right hη4 ht0])
  have htN : t+w ≤ N := by omega
  have hw : w ≤ t := by omega
  let B := (η/32)*t
  have hMB (n : ℕ) (hn : n ∈ ({t-w,t,t+w} : Finset ℕ)) : |M n| ≤ B := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    have hmin := (le_max_left (2*k) j).trans ht
    have hnlo : k ≤ n := by omega
    have hnhi : n ≤ 2*t := by omega
    have hreal : (n:ℝ) ≤ 2*t := by exact_mod_cast hnhi
    exact (hk n hnlo).trans (by unfold B; nlinarith [mul_le_mul_of_nonneg_left hreal hη.le])
  have hsq : ((t+w).sqrt:ℝ)^2 ≤ (t:ℝ)+w := by rw [pow_two]; exact_mod_cast Nat.sqrt_le (t+w)
  have hroot : ((t+w).sqrt:ℝ) ≤ η*t/16 := by
    have h1 := mul_le_mul_of_nonneg_right h512 ht0
    have h2' : 0 ≤ η*t := mul_nonneg hη.le ht0
    have h3 : (w:ℝ) ≤ t := by exact_mod_cast hw
    by_contra! hbad
    have hh := mul_self_lt_mul_self (show 0 ≤ η*t/16 by positivity) hbad
    nlinarith
  have hgap : 8*B+4*((t+w).sqrt:ℝ) ≤ w := by unfold B; linarith
  intro s
  obtain ⟨hg,hl,hu⟩ := activity_window hw htN hMB hgap hiL hiU s
  refine ⟨hg,abs_le.mpr ⟨?_,?_⟩⟩
  · have h : ((t:ℝ)-w) < paddedAt N (signSet s N) i := by
      rw [← Nat.cast_sub hw]; exact_mod_cast hl
    linarith [mul_le_mul_of_nonneg_right hηδ ht0]
  · have h : (paddedAt N (signSet s N) i:ℝ) ≤ (t:ℝ)+w := by exact_mod_cast hu
    linarith [mul_le_mul_of_nonneg_right hηδ ht0]

theorem index_stable {L N i : ℕ} (hLN : L ≤ N) (s : Bool) (hi : i < (signSet s L).card) :
    indexAt (signSet s N) i = indexAt (signSet s L) i := by
  have hi' : i < prefixCount (signSet s N) L := by rwa [prefix_stable s hLN]
  have hiN := hi'.trans_le (show prefixCount (signSet s N) L ≤ (signSet s N).card from Finset.card_filter_le _ _)
  have hN : indexAt (signSet s N) i ≤ L := (prefix_membership_of_rank hiN).2 hi'
  have hL : indexAt (signSet s L) i ≤ L := (prefix_membership_of_rank hi).2
    (show i < prefixCount (signSet s L) L by rwa [prefix_stable s le_rfl])
  have he (x : ℕ) (hx : x ≤ L) :
      indexAt (signSet s N) i ≤ x ↔ indexAt (signSet s L) i ≤ x := by
    rw [prefix_membership_of_rank hiN,prefix_membership_of_rank hi]
    change i < prefixCount (signSet s N) x ↔ i < prefixCount (signSet s L) x
    rw [prefix_stable s (hx.trans hLN),prefix_stable s hx]
  exact le_antisymm ((he _ hL).2 le_rfl) ((he _ hN).1 le_rfl)

theorem activity_window_stable {N t w i : ℕ} {B : ℝ} (hw : w ≤ t) (hN : t+w ≤ N)
    (hM : ∀ n ∈ ({t-w,t,t+w} : Finset ℕ), |M n| ≤ B) (hgap : 8*B+4*((t+w).sqrt:ℝ) ≤ w)
    (hiL : min ((signSet true t).card) ((signSet false t).card) ≤ i)
    (hiU : i < max ((signSet true t).card) ((signSet false t).card)) (s : Bool) :
    indexAt (signSet s N) i = indexAt (signSet s (t+w)) i :=
  index_stable hN s (activity_window hw le_rfl hM hgap hiL hiU s).1

end RHConnections.MobiusRankLocalization
