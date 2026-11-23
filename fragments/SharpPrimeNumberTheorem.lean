import Verified
import Mathlib.NumberTheory.Chebyshev

open Filter Set MeasureTheory
noncomputable section
namespace RHConnections.SmoothedPrimeLimit
open ArithmeticFunction

private def primeCut (X : ℝ) (n : ℕ) : ℝ :=
  if n ∈ Finset.Icc 1 ⌊X⌋₊ then vonMangoldt n else 0

private theorem primeCut_sum (X : ℝ) : ∑' n : ℕ, primeCut X n = Chebyshev.psi X := by
  rw [Chebyshev.psi_eq_sum_Icc,tsum_eq_sum (s := Finset.Icc 1 ⌊X⌋₊)]
  · calc
      _ = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, vonMangoldt n :=
        Finset.sum_congr rfl (fun n hn => if_pos hn)
      _ = _ := Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr
          ⟨Nat.zero_le n,(Finset.mem_Icc.mp hn).2⟩) (fun n hnI h => by
          have hn : n = 0 := by
            by_contra h0
            apply h
            exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h0, (Finset.mem_Icc.mp hnI).2⟩
          simp [hn])
  · exact fun n hn => if_neg hn

private theorem primeCut_summable (X : ℝ) : Summable (primeCut X) :=
  summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊X⌋₊) fun _ hn => if_neg hn

private theorem primeTest_summable {f : ℝ → ℝ} (hc : HasCompactSupport f) (T : ℝ) :
    Summable (fun n : ℕ => vonMangoldt n*f (Real.log n-T)) := by
  obtain ⟨B,hB⟩ := hc.isCompact.bddAbove
  let U := Real.exp (T+B)
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊U⌋₊)
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hnU : ⌊U⌋₊ < n := lt_of_not_ge (fun h => hn (Finset.mem_Icc.mpr ⟨hn1,h⟩))
  have hUp : U < (n:ℝ) := (Nat.floor_lt (Real.exp_pos _).le).mp hnU
  have hlog := Real.log_lt_log (Real.exp_pos (T+B)) hUp
  rw [show Real.log U = T+B from Real.log_exp _] at hlog
  have hf : f (Real.log n-T) = 0 := by
    by_contra h
    have hle : Real.log n-T ≤ B := hB (subset_tsupport f h)
    linarith
  simp [hf]

private theorem log_le_iff_nat_floor {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n:ℝ) ≤ Real.log X ↔ n ≤ ⌊X⌋₊ := by
  have hn0 : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  rw [Nat.le_floor_iff hX.le]
  exact (Real.strictMonoOn_log.le_iff_le (show (n:ℝ) ∈ Set.Ioi (0:ℝ) from hn0)
    (show X ∈ Set.Ioi (0:ℝ) from hX))

theorem real_prime_lower_cut {f : ℝ → ℝ} (hc : HasCompactSupport f)
    (hle : ∀ x, f x ≤ 1) (hz : ∀ x, 0 < x → f x = 0) (T : ℝ) :
    realPrimeTest f T ≤ Real.exp (-T)*Chebyshev.psi (Real.exp T) := by
  rw [realPrimeTest,← primeCut_sum]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  refine (primeTest_summable hc T).tsum_le_tsum ?_ (primeCut_summable _)
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp [primeCut]
  have hn1 := Nat.one_le_iff_ne_zero.mpr hn0
  by_cases hn : n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊
  · rw [primeCut,if_pos hn]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hle _) (vonMangoldt_nonneg (n := n))
  · have hnot : ¬ n ≤ ⌊Real.exp T⌋₊ := fun h => hn (Finset.mem_Icc.mpr ⟨hn1,h⟩)
    have hlog := lt_of_not_ge (fun h => hnot ((log_le_iff_nat_floor (Real.exp_pos T) hn1).mp
      (by simpa only [Real.log_exp] using h)))
    have hpos : 0 < Real.log (n:ℝ)-T := sub_pos.mpr hlog
    rw [primeCut,if_neg hn,hz _ hpos,mul_zero]

theorem real_prime_upper_cut {f : ℝ → ℝ} (hc : HasCompactSupport f)
    (h0 : ∀ x, 0 ≤ f x) {A : ℝ} (hone : ∀ x ∈ Icc (-A) 0, f x = 1) (T : ℝ) :
    Real.exp (-T)*Chebyshev.psi (Real.exp T) ≤ realPrimeTest f T +
      Real.exp (-T)*Chebyshev.psi (Real.exp (-A+T)) := by
  rw [realPrimeTest,← primeCut_sum,← primeCut_sum,← mul_add,
    ← (primeTest_summable hc T).tsum_add (primeCut_summable _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  refine (primeCut_summable _).tsum_le_tsum ?_ ((primeTest_summable hc T).add (primeCut_summable _))
  intro n
  have hnn : 0 ≤ vonMangoldt n*f (Real.log n-T) := mul_nonneg vonMangoldt_nonneg (h0 _)
  have hsmall0 : 0 ≤ primeCut (Real.exp (-A+T)) n := by unfold primeCut; split <;> positivity
  change primeCut (Real.exp T) n ≤ vonMangoldt n*f (Real.log n-T) + primeCut (Real.exp (-A+T)) n
  by_cases hn : n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊
  · rw [show primeCut (Real.exp T) n = vonMangoldt n from if_pos hn]
    by_cases hsmall : n ∈ Finset.Icc 1 ⌊Real.exp (-A+T)⌋₊
    · rw [show primeCut (Real.exp (-A+T)) n = vonMangoldt n from if_pos hsmall]
      linarith
    · have hn1 := (Finset.mem_Icc.mp hn).1
      have hnot : ¬ n ≤ ⌊Real.exp (-A+T)⌋₊ := fun h => hsmall (Finset.mem_Icc.mpr ⟨hn1,h⟩)
      have hlo := lt_of_not_ge (fun h => hnot ((log_le_iff_nat_floor (Real.exp_pos _) hn1).mp
        (by simpa only [Real.log_exp] using h)))
      have hup := (log_le_iff_nat_floor (Real.exp_pos _) hn1).mpr (Finset.mem_Icc.mp hn).2
      rw [Real.log_exp] at hup
      have hx : Real.log (n:ℝ)-T ∈ Icc (-A) 0 := ⟨by linarith,by linarith⟩
      rw [hone _ hx,mul_one]
      exact le_add_of_nonneg_right hsmall0
  · change primeCut (Real.exp T) n ≤ _
    simp only [primeCut,if_neg hn]
    exact add_nonneg hnn hsmall0

theorem chebyshev_prime_number_theorem_log_scale :
    Tendsto (fun T : ℝ => Real.exp (-T)*Chebyshev.psi (Real.exp T)) atTop (nhds 1) := by
  let C := Real.log 4+4
  have hC : 0 ≤ C := by dsimp [C]; linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
  have hTests (ε : ℝ) (hε : 0 < ε) :
      ∃ A δ : ℝ, 1 ≤ A ∧ 0 < δ ∧ δ ≤ 1/2 ∧ δ ≤ ε/8 ∧
        (C+1)*Real.exp (-A) < ε/4 := by
    have h := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (C+1)
    have hl : Tendsto (fun A : ℝ => (C+1)*Real.exp (-A)) atTop (nhds 0) := by
      simpa only [Function.comp_apply,mul_zero] using h
    obtain ⟨R,hR⟩ := eventually_atTop.mp (hl.eventually_lt_const (show 0 < ε/4 by positivity))
    exact ⟨max R 1,min (1/2) (ε/8),le_max_right _ _,lt_min (by norm_num) (by positivity),
      min_le_left _ _,min_le_right _ _,hR _ (le_max_left _ _)⟩
  apply tendsto_order.mpr
  constructor
  · intro y hy
    obtain ⟨A,δ,hA,hδ,hδ2,hδε,hTail⟩ := hTests (1-y) (by linarith)
    let φ := intervalBump (-A) (-δ) δ (by linarith) hδ
    have hlim := real_prime_test_limit φ.contDiff φ.hasCompactSupport
    have hphi : y < ∫ x : ℝ, Real.exp x*φ x := by
      have hi := (interval_bump_exp_integral (show -A < -δ by linarith) hδ).1
      have hE := Real.add_one_le_exp (-δ)
      have hT : Real.exp (-A) ≤ (C+1)*Real.exp (-A) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (show 1 ≤ C+1 by linarith) (Real.exp_pos _).le
      linarith
    filter_upwards [(tendsto_order.mp hlim).1 y hphi] with T ht
    exact ht.trans_le (real_prime_lower_cut φ.hasCompactSupport (fun x => φ.le_one)
      (fun x hx => interval_bump_zero (by linarith : -A < -δ) hδ
        (fun h => by linarith [h.2])) T)
  · intro y hy
    obtain ⟨A,δ,hA,hδ,hδ2,hδε,hTail⟩ := hTests (y-1) (by linarith)
    let φ := intervalBump (-A) 0 δ (by linarith) hδ
    let E := C*Real.exp (-A)
    have hlim := (real_prime_test_limit φ.contDiff φ.hasCompactSupport).add_const E
    have hphi : (∫ x : ℝ, Real.exp x*φ x)+E < y := by
      have hi := (interval_bump_exp_integral (show -A < (0:ℝ) by linarith) hδ).2
      rw [zero_add] at hi
      have hExp := Real.abs_exp_sub_one_le (show |δ| ≤ 1 by rw [abs_of_pos hδ]; linarith)
      have he : Real.exp δ-1 ≤ 2*δ := by
        exact (le_abs_self _).trans (by simpa [abs_of_pos hδ] using hExp)
      dsimp [E]
      linarith [Real.exp_pos (-A-δ),Real.exp_pos (-A)]
    filter_upwards [(tendsto_order.mp hlim).2 y hphi] with T ht
    apply lt_of_le_of_lt _ ht
    refine (real_prime_upper_cut φ.hasCompactSupport (fun x => φ.nonneg' x)
      (fun _ hx => interval_bump_one (by linarith : -A < (0:ℝ)) hδ hx) T).trans ?_
    apply add_le_add le_rfl
    calc
      _ ≤ Real.exp (-T)*(C*Real.exp (-A+T)) := mul_le_mul_of_nonneg_left
        (Chebyshev.psi_le_const_mul_self (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = E := by
        rw [← mul_left_comm,← Real.exp_add,show -T+(-A+T)= -A by ring]

theorem chebyshev_prime_number_theorem :
    Tendsto (fun X : ℝ => Chebyshev.psi X / X) atTop (nhds 1) := by
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  refine (chebyshev_prime_number_theorem_log_scale.comp hlog).congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  simp only [Function.comp_apply,Real.exp_log hX,Real.exp_neg,div_eq_mul_inv,mul_comm]

end RHConnections.SmoothedPrimeLimit
