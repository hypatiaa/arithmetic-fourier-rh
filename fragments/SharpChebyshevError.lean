import SmoothedPrimeUniform
import SmoothedPrimeSandwichUniform

open Filter Set MeasureTheory
open scoped ContDiff Topology
noncomputable section
namespace RHConnections.SharpChebyshevError
open SmoothedPrimeLimit SmoothedPrimeUniform SmoothedPrimeSandwichUniform ChebyshevCriterion ArithmeticFunction

def mass (f : ℝ → ℝ) := ∫ x in Ioi (0:ℝ), Real.exp x*f x

theorem smooth_shell_error :
    ∃ d C : ℝ, 0 < d ∧ 0 ≤ C ∧ ∀ {a b h : ℝ}, a ≤ b → 0 < a → b+h < 3 →
    0 < h → h ≤ 1 → ∀ T : ℝ, 1 ≤ T →
    |realPrimeTest (shell a b h) T - mass (shell a b h)| ≤ (C/h)*Real.exp (-d*Real.sqrt T) := by
  obtain ⟨d,W,hd,_,hW,hE⟩ := uniform_prime_error
  let B := Real.exp 3 * (2*curvatureMass)
  have hB : 0 ≤ B := by unfold B curvatureMass; positivity
  refine ⟨d,B*W+9,hd,by positivity,?_⟩
  intro a b h hab ha hb hh hh1 T hT
  let f := shell a b h
  let g := fun x : ℝ => (f x:ℂ)
  have hs : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp (shell_smooth a b h)
  have hz (x : ℝ) (hx : x ≤ 0) : g x = 0 := by simp [g,f,shell_left hab hh (hx.trans ha.le)]
  have gz (x : ℝ) (hx : x ∉ Ioc (0:ℝ) 3) : g x = 0 := by
    by_cases hx0 : x ≤ 0
    · exact hz x hx0
    · have hx3 : 3 < x := by by_contra! e; exact hx ⟨lt_of_not_ge hx0,e⟩
      simp [g,f,shell_right hab hh (hb.trans hx3).le]
  have hc : HasCompactSupport g := HasCompactSupport.intro (K := Icc (0:ℝ) 3) isCompact_Icc
    (fun x hx => gz x (fun e => hx ⟨e.1.le,e.2⟩))
  have hg1 (x : ℝ) : ‖g x‖ ≤ 1 := by
    have hf := shell_range hab hh x
    simpa [g,f,abs_of_nonneg hf.1] using hf.2
  have hi : (∫ x : ℝ, ‖g x‖) ≤ 3 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (0:ℝ) 3)
      (f := fun x => ‖g x‖) (fun x hx => by simp [gz x hx])]
    calc
      _ ≤ ∫ _x in Ioc (0:ℝ) 3, (1:ℝ) := integral_mono
        (hs.continuous.integrable_of_hasCompactSupport hc).norm.integrableOn
        (integrableOn_const (measure_Ioc_lt_top.ne)) hg1
      _ = _ := by simp
  have hi2 : ‖∫ x in Ioi (0:ℝ), g x‖ ≤ 3 :=
    (norm_integral_le_integral_norm _).trans ((setIntegral_le_integral
      (hs.continuous.integrable_of_hasCompactSupport hc).norm (Eventually.of_forall fun _ => norm_nonneg _)).trans hi)
  have he := hE hs hc hz (div_nonneg hB hh.le) (spectral_majorant hab hh ha hb) T hT
  have hc' : (B/h)*W + 2*(∫ x : ℝ, ‖g x‖) + ‖∫ x in Ioi (0:ℝ), g x‖ ≤ (B*W+9)/h := by
    calc
      _ ≤ B/h*W + 9 := by linarith
      _ ≤ _ := by apply (le_div_iff₀ hh).2; field_simp; nlinarith
  apply le_trans _ (mul_le_mul_of_nonneg_right hc' (Real.exp_pos _).le)
  unfold realPrimeTest mass
  simpa only [g,mangoldtCoeff,← Complex.ofReal_neg,← Complex.ofReal_exp,← Complex.ofReal_mul,
    ← Complex.ofReal_tsum,integral_complex_ofReal,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using he

private theorem exp_integral {a b : ℝ} (hab : a ≤ b) :
    (∫ x : ℝ, (Ioc a b).indicator Real.exp x) = Real.exp b-Real.exp a := by
  rw [integral_indicator measurableSet_Ioc,← intervalIntegral.integral_of_le hab,integral_exp]

private theorem exp_integrable (a b : ℝ) : Integrable ((Ioc a b).indicator Real.exp) :=
  (Real.continuous_exp.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc

theorem shell_mass {a b h : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hab : a+h ≤ b) :
    Real.exp b - Real.exp (a+h) ≤ mass (shell a b h) ∧
    mass (shell a b h) ≤ Real.exp (b+h) - Real.exp a := by
  have hab' : a ≤ b := by linarith
  have hI : Integrable (fun x => Real.exp x * shell a b h x) :=
    (Real.continuous_exp.mul (shell_smooth a b h).continuous).integrable_of_hasCompactSupport
      (shell_compact hab' hh).mul_left
  unfold mass
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    simp [shell_left hab' hh (show x ≤ a by have := not_lt.mp (show ¬0 < x from hx); linarith)])]
  constructor
  · rw [← exp_integral hab]
    apply integral_mono (exp_integrable _ _) hI
    intro x
    by_cases hx : x ∈ Ioc (a+h) b
    · simp [indicator_of_mem hx,shell_one hh hx.1.le hx.2]
    · simp [indicator_of_notMem hx,mul_nonneg (Real.exp_pos _).le (shell_range hab' hh x).1]
  · rw [← exp_integral (show a ≤ b+h by linarith)]
    apply integral_mono hI (exp_integrable _ _)
    intro x
    by_cases hx : x ∈ Ioc a (b+h)
    · rw [indicator_of_mem hx]
      exact (mul_le_mul_of_nonneg_left (shell_range hab' hh x).2 (Real.exp_pos x).le).trans_eq (mul_one _)
    · rw [indicator_of_notMem hx]
      by_cases hxa : x ≤ a
      · simp [shell_left hab' hh hxa]
      · have he : b+h ≤ x := by by_contra! hj; exact hx ⟨lt_of_not_ge hxa,hj.le⟩
        simp [shell_right hab' hh he]
private def primeCut (X : ℝ) (n : ℕ) : ℝ :=
  if n ∈ Finset.Icc 1 ⌊X⌋₊ then vonMangoldt n else 0

private theorem primeCut_sum (X : ℝ) : ∑' n : ℕ, primeCut X n = Chebyshev.psi X := by
  rw [Chebyshev.psi_eq_sum_Icc,tsum_eq_sum (s := Finset.Icc 1 ⌊X⌋₊)]
  · calc
      _ = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, vonMangoldt n :=
        Finset.sum_congr rfl (fun n hn => ite_eq_left hn)
      _ = _ := Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr
          ⟨Nat.zero_le n,(Finset.mem_Icc.mp hn).2⟩) (fun n hnI h => by
          have hn : n = 0 := by
            by_contra h0
            apply h
            exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h0, (Finset.mem_Icc.mp hnI).2⟩
          simp [hn])
  · exact fun n hn => ite_eq_right hn

private theorem primeCut_summable (X : ℝ) : Summable (primeCut X) :=
  summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊X⌋₊) fun _ hn => ite_eq_right hn

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

def sharpShell (T : ℝ) : ℝ := Real.exp (-T) * (Chebyshev.psi (Real.exp (T+2)) - Chebyshev.psi (Real.exp (T+1)))

theorem sharp_shell_sandwich {h : ℝ} (hh : 0 < h) (ht : h ≤ 1/4) (T : ℝ) :
    realPrimeTest (shell 1 (2-h) h) T ≤ sharpShell T ∧
    sharpShell T ≤ realPrimeTest (shell (1-h) 2 h) T := by
  let L := Real.exp (T+1)
  let U := Real.exp (T+2)
  have he (n : ℕ) :
      primeCut U n - primeCut L n =
      vonMangoldt n * (Ioc (1:ℝ) 2).indicator (fun _ => (1:ℝ)) (Real.log n-T) := by
    by_cases hn : n = 0
    · simp [hn,primeCut]
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hL : n ≤ ⌊L⌋₊ ↔ Real.log n-T ≤ 1 := by
      rw [← log_le_iff_nat_floor (Real.exp_pos _) hn1]
      simp [Real.log_exp]; constructor <;> intro h <;> linarith
    have hU : n ≤ ⌊U⌋₊ ↔ Real.log n-T ≤ 2 := by
      rw [← log_le_iff_nat_floor (Real.exp_pos _) hn1]
      simp [Real.log_exp]; constructor <;> intro h <;> linarith
    simp only [primeCut,Finset.mem_Icc,hn1,true_and,hU,hL]
    by_cases hl : Real.log n-T ≤ 1
    · have hu : Real.log n-T ≤ 2 := by linarith
      simp [hl,hu,Set.indicator,Set.mem_Ioc,not_lt.mpr hl]
    · by_cases hu : Real.log n-T ≤ 2 <;> simp [hl,hu,Set.indicator,Set.mem_Ioc,lt_of_not_ge hl]
  have hsm := (primeCut_summable U).sub (primeCut_summable L)
  have hcut : sharpShell T = Real.exp (-T) * ∑' n : ℕ, (primeCut U n-primeCut L n) := by
    rw [(primeCut_summable U).tsum_sub (primeCut_summable L),primeCut_sum,primeCut_sum]
    rfl
  rw [hcut,realPrimeTest,realPrimeTest]
  constructor
  · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply (primeTest_summable (shell_compact (by linarith) hh) T).tsum_le_tsum _ hsm
    intro n
    rw [he]
    exact mul_le_mul_of_nonneg_left (sandwich hh ht _).1 vonMangoldt_nonneg
  · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply hsm.tsum_le_tsum _ (primeTest_summable (shell_compact (by linarith) hh) T)
    intro n
    change primeCut U n - primeCut L n ≤ _
    rw [he]
    exact mul_le_mul_of_nonneg_left (sandwich hh ht _).2 vonMangoldt_nonneg

theorem sharp_shell_width :
    ∃ d C B : ℝ, 0 < d ∧ 0 ≤ C ∧ 0 ≤ B ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1/4 →
    ∀ T : ℝ, 1 ≤ T → |sharpShell T - (Real.exp 2 - Real.exp 1)| ≤
      B*h + C/h * Real.exp (-d*Real.sqrt T) := by
  obtain ⟨d,C,hd,hC,hE⟩ := smooth_shell_error
  let B := 2*(Real.exp 2+Real.exp 1)
  refine ⟨d,C,B,hd,hC,by dsimp [B]; positivity,?_⟩
  intro h hh ht T hT
  have e1 := abs_le.mp (hE (by linarith : 1 ≤ 2-h) (by norm_num) (by linarith) hh (by linarith) T hT)
  have e2 := abs_le.mp (hE (by linarith : 1-h ≤ 2) (by linarith) (by linarith) hh (by linarith) T hT)
  have m1 := (shell_mass hh (by norm_num : (0:ℝ) ≤ 1) (by linarith : 1+h ≤ 2-h)).1
  have m2 := (shell_mass hh (by linarith : 0 ≤ 1-h) (by linarith : 1-h+h ≤ 2)).2
  obtain ⟨l,u⟩ := sharp_shell_sandwich hh ht T
  have ep : Real.exp h-1 ≤ 2*h := (le_abs_self _).trans
    (by simpa [abs_of_pos hh] using Real.abs_exp_sub_one_le (x := h) (by rw [abs_of_pos hh]; linarith))
  have em := Real.add_one_le_exp (-h)
  rw [sub_eq_add_neg (2:ℝ) h,Real.exp_add,Real.exp_add] at m1
  rw [sub_eq_add_neg (1:ℝ) h,Real.exp_add,Real.exp_add] at m2
  have h₁ := mul_le_mul_of_nonneg_left ep (Real.exp_pos 1).le
  have h₂ := mul_le_mul_of_nonneg_left ep (Real.exp_pos 2).le
  have h₃ := mul_le_mul_of_nonneg_left em (Real.exp_pos 1).le
  have h₄ := mul_le_mul_of_nonneg_left em (Real.exp_pos 2).le
  have h₅ := mul_nonneg hh.le (Real.exp_pos 1).le
  have h₆ := mul_nonneg hh.le (Real.exp_pos 2).le
  rw [← sub_eq_add_neg] at m1 m2
  dsimp [B]
  exact abs_le.mpr ⟨by linarith [e1.1,e1.2],by linarith [e2.1,e2.2]⟩

theorem sharp_shell_exp_error :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ T : ℝ, 1 ≤ T →
    |sharpShell T - (Real.exp 2 - Real.exp 1)| ≤ K * Real.exp (-c*Real.sqrt T) := by
  obtain ⟨d,C,B,hd,hC,hB,hE⟩ := sharp_shell_width
  refine ⟨d/2,B/4+4*C,by positivity,by positivity,?_⟩
  intro T hT
  let u := Real.exp (-(d/2)*Real.sqrt T)
  have hu : 0 < u := Real.exp_pos _
  have hu1 : u ≤ 1 := Real.exp_le_one_iff.mpr (by exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _))
  have he := hE (show 0 < u/4 by positivity) (by linarith : u/4 ≤ 1/4) T hT
  have hsq : Real.exp (-d*Real.sqrt T) = u*u := by
    dsimp [u]; rw [← Real.exp_add]; congr 1; ring
  rw [hsq] at he
  refine he.trans_eq ?_
  change B*(u/4)+C/(u/4)*(u*u) = (B/4+4*C)*u
  field_simp

def psiError (T : ℝ) := Chebyshev.psi (Real.exp T) - Real.exp T

private theorem shell_increment {c K : ℝ} (hS : ∀ T : ℝ, 1 ≤ T →
    |sharpShell T - (Real.exp 2 - Real.exp 1)| ≤ K * Real.exp (-c*Real.sqrt T))
    {T : ℝ} (hT : 3 ≤ T) :
    |psiError T - psiError (T-1)| ≤ K*Real.exp ((T-2)-c*Real.sqrt (T-2)) := by
  have he := hS (T-2) (by linarith)
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (T-2)).le
  rw [← abs_of_pos (Real.exp_pos (T-2)),← abs_mul] at hm
  have hid : Real.exp (T-2)*(sharpShell (T-2)-(Real.exp 2-Real.exp 1)) =
      psiError T-psiError (T-1) := by
    unfold sharpShell psiError
    rw [show T-2+2=T by ring,show T-2+1=T-1 by ring, mul_sub]
    rw [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul,mul_sub,
      ← Real.exp_add,← Real.exp_add,show T-2+2=T by ring,show T-2+1=T-1 by ring]
    ring
  rw [hid,abs_of_pos (Real.exp_pos (T-2))] at hm
  refine hm.trans_eq ?_
  rw [sub_eq_add_neg (T-2) (c*Real.sqrt (T-2)),Real.exp_add]
  ring_nf

theorem chebyshev_log_error :
    ∃ a D : ℝ, 0 < a ∧ 0 ≤ D ∧ ∀ T : ℝ, 2 ≤ T →
      |psiError T| ≤ D*Real.exp (T-a*Real.sqrt T) := by
  obtain ⟨c,K,hc,hK,hS⟩ := sharp_shell_exp_error
  let a := min (c/2) (1/2)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have hac : a ≤ c/2 := min_le_left _ _
  have ha2 : a ≤ 1/2 := min_le_right _ _
  let q := Real.exp (-(1/2:ℝ))
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  let D₀ := (Real.log 4+5)*Real.exp 3
  have hD₀ : 0 ≤ D₀ := mul_nonneg (by linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]) (Real.exp_pos _).le
  let D := max D₀ (K/(1-q))
  have hD : 0 ≤ D := hD₀.trans (le_max_left _ _)
  have hbudget : D*q+K ≤ D := by
    have hh := (div_le_iff₀ (sub_pos.mpr hq)).mp (show K/(1-q) ≤ D from le_max_right _ _)
    linarith
  let G := fun t : ℝ => Real.exp (t-a*Real.sqrt t)
  have hbase (T : ℝ) (h2 : 2 ≤ T) (h3 : T ≤ 3) : |psiError T| ≤ D*G T := by
    have hE := Real.exp_le_exp.mpr h3
    have hpsi := Chebyshev.psi_le_const_mul_self (Real.exp_pos T).le
    have hnon := Chebyshev.psi_nonneg (x := Real.exp T)
    have hlog := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    have hb : |psiError T| ≤ D₀ := by
      unfold psiError D₀
      have hh := mul_le_mul_of_nonneg_left hE (show 0 ≤ Real.log 4+5 by linarith)
      apply abs_le.mpr
      constructor <;> nlinarith [Real.exp_pos T]
    have hs : Real.sqrt T ≤ T := by
      have hh : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt (show 1 ≤ T by linarith)
      nlinarith [Real.sq_sqrt (show 0 ≤ T by linarith)]
    have hG : 1 ≤ G T := Real.one_le_exp_iff.mpr (by nlinarith [mul_le_mul_of_nonneg_right ha2 (Real.sqrt_nonneg T)])
    exact hb.trans ((le_max_left _ _).trans (le_mul_of_one_le_right hD hG))
  have hrec (T : ℝ) (h3 : 3 ≤ T) (hprev : |psiError (T-1)| ≤ D*G (T-1)) :
      |psiError T| ≤ D*G T := by
    have hs : Real.sqrt T ≤ Real.sqrt (T-1)+1 := by
      apply (Real.sqrt_le_iff).2
      exact ⟨by positivity,by nlinarith [Real.sq_sqrt (show 0 ≤ T-1 by linarith),Real.sqrt_nonneg (T-1)]⟩
    have hg : G (T-1) ≤ q*G T := by
      unfold G q
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hs ha.le]
    have hs2 : Real.sqrt T ≤ 2*Real.sqrt (T-2) := by
      apply (Real.sqrt_le_iff).2
      exact ⟨by positivity,by nlinarith [Real.sq_sqrt (show 0 ≤ T-2 by linarith)]⟩
    have hge : Real.exp ((T-2)-c*Real.sqrt (T-2)) ≤ G T := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hs2 ha.le,
        mul_le_mul_of_nonneg_right hac (Real.sqrt_nonneg (T-2))]
    have hInc := (shell_increment hS h3).trans (mul_le_mul_of_nonneg_left hge hK)
    calc
      _ = |(psiError T-psiError (T-1))+psiError (T-1)| := by ring_nf
      _ ≤ |psiError T-psiError (T-1)| + |psiError (T-1)| := abs_add_le _ _
      _ ≤ K*G T + D*(q*G T) := add_le_add hInc (hprev.trans (mul_le_mul_of_nonneg_left hg hD))
      _ = (D*q+K)*G T := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Real.exp_pos _).le
  refine ⟨a,D,ha,hD,?_⟩
  have hall (n : ℕ) : ∀ T : ℝ, 2 ≤ T → T ≤ 3+n → |psiError T| ≤ D*G T := by
    induction n with
    | zero => intro T h2 h3; apply hbase T h2; simpa using h3
    | succ n ih =>
      intro T h2 h3
      by_cases ht : T ≤ 3
      · exact hbase T h2 ht
      · apply hrec T (le_of_not_ge ht)
        apply ih _ (by linarith)
        push_cast at h3
        linarith
  intro T hT
  obtain ⟨n,hn⟩ := exists_nat_gt T
  exact hall n T hT (by linarith)

theorem chebyshev_quantitative_error :
    ∃ a D : ℝ, 0 < a ∧ 0 ≤ D ∧ ∀ X : ℝ, Real.exp 2 ≤ X →
      |Chebyshev.psi X-X| ≤ D*X*Real.exp (-a*Real.sqrt (Real.log X)) := by
  obtain ⟨a,D,ha,hD,h⟩ := chebyshev_log_error
  refine ⟨a,D,ha,hD,?_⟩
  intro X hX
  have hx : 0 < X := (Real.exp_pos 2).trans_le hX
  have hl := Real.log_le_log (Real.exp_pos 2) hX
  rw [Real.log_exp] at hl
  have he := h (Real.log X) hl
  unfold psiError at he
  rw [Real.exp_log hx,sub_eq_add_neg (Real.log X) _,Real.exp_add,Real.exp_log hx] at he
  exact he.trans_eq (by rw [neg_mul]; ring)

end RHConnections.SharpChebyshevError
