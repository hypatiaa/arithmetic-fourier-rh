import Verified

open MeasureTheory Set
open scoped ContDiff
noncomputable section
namespace RHConnections.PrimeRightCut
open SpectralTail ChebyshevCriterion SmoothedPrimeLimit

abbrev w2 (r : NontrivialZetaZero) : ℝ :=
  (analyticOrderNatAt riemannZeta r.val : ℝ)/‖r.val‖^2
abbrev w32 (r : NontrivialZetaZero) : ℝ :=
  (analyticOrderNatAt riemannZeta r.val : ℝ)/(‖r.val‖*Real.sqrt ‖r.val‖)

def W : ℝ := ∑' r : NontrivialZetaZero, (w2 r + w32 r)

def rightSet (T : ℝ) : Set NontrivialZetaZero := {r | 5/6 < r.val.re ∧ ‖r.val‖ ≤ Real.exp (T/3)}

def rightSum (T : ℝ) (f : ℝ → ℂ) : ℂ := ∑' r, (rightSet T).indicator
  (fun r : NontrivialZetaZero => compactZeroTerm (scaleTest T f) r) r

theorem zero_sum_minus_right {f : ℝ → ℂ} (hf0 : ∀ x ≤ 0, f x = 0) {K T : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hB : ∀ r : NontrivialZetaZero, ‖compactZeroTerm (scaleTest 0 f) r‖ ≤ w2 r*K) :
    ‖(∑' r : NontrivialZetaZero, compactZeroTerm (scaleTest T f) r) - rightSum T f‖ ≤
      K*W*Real.exp (-(T/6)) := by
  classical
  let F := fun r : NontrivialZetaZero => compactZeroTerm (scaleTest T f) r
  let E := Real.exp (-(T/6))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hsum : Summable (fun r : NontrivialZetaZero => w2 r+w32 r) :=
    zeta_inverse_square_with_multiplicity.add zeta_inverse_three_halves_with_multiplicity
  have heq (r : NontrivialZetaZero) :
      ‖F r‖ = Real.exp ((r.val.re-1)*T)*‖compactZeroTerm (scaleTest 0 f) r‖ := by
    simp only [F,scaled_zero_term_eq hf0 hT,norm_mul,Complex.norm_exp,Complex.mul_re,
      Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have hsmall (r : NontrivialZetaZero) : ‖F r‖ ≤ w2 r*K := by
    rw [heq]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr r.property.1.2.le) hT))).trans (hB r)
  have hsF : Summable F := Summable.of_norm <|
    (zeta_inverse_square_with_multiplicity.mul_right K).of_nonneg_of_le (fun _ => norm_nonneg _) hsmall
  let G := (rightSet T).indicator F
  have hsG : Summable G := hsF.indicator _
  have hmaj (r : NontrivialZetaZero) : ‖F r-G r‖ ≤ (K*E)*(w2 r+w32 r) := by
    have hnR := zeta_zero_norm_lower
    obtain ⟨d,hd,hr⟩ := hnR
    have hn : 0 < ‖r.val‖ := hd.trans_le (hr r)
    have h2 : 0 ≤ w2 r := by dsimp [w2]; positivity
    have h32 : 0 ≤ w32 r := by dsimp [w32]; positivity
    by_cases hg : r ∈ rightSet T
    · simp only [G,indicator_of_mem hg,sub_self,norm_zero]
      exact mul_nonneg (mul_nonneg hK hE) (add_nonneg h2 h32)
    rw [show G r = 0 from indicator_of_notMem hg _, sub_zero]
    by_cases hb : r.val.re ≤ 5/6
    · have he : Real.exp ((r.val.re-1)*T) ≤ E := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hb hT]
      rw [heq]
      calc
        _ ≤ E*(w2 r*K) := mul_le_mul he (hB r) (norm_nonneg _) hE
        _ = K*E*w2 r := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h32) (mul_nonneg hK hE)
    · have hheight : Real.exp (T/3) < ‖r.val‖ := by
        by_contra! e
        exact hg ⟨lt_of_not_ge hb,e⟩
      have hroot : Real.exp (T/6) ≤ Real.sqrt ‖r.val‖ := by
        rw [Real.le_sqrt (Real.exp_pos _).le hn.le, sq, ← Real.exp_add]
        exact (show T/6+T/6 = T/3 by ring) ▸ hheight.le
      have hinv : (Real.sqrt ‖r.val‖)⁻¹ ≤ E :=
        (inv_anti₀ (Real.exp_pos _) hroot).trans_eq (Real.exp_neg _).symm
      have hdcp : w2 r = w32 r*(Real.sqrt ‖r.val‖)⁻¹ := by
        dsimp only [w2,w32]
        have hne := (Real.sqrt_pos_of_pos hn).ne'
        field_simp [hn.ne',hne]
        nlinarith [Real.sq_sqrt hn.le]
      calc
        _ ≤ w2 r*K := hsmall r
        _ ≤ (w32 r*E)*K := mul_le_mul_of_nonneg_right
          (hdcp.trans_le (mul_le_mul_of_nonneg_left hinv h32)) hK
        _ = K*E*w32 r := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h2) (mul_nonneg hK hE)
  have habs := (hsum.mul_left (K*E)).of_nonneg_of_le (fun _ => norm_nonneg _) hmaj
  change ‖(∑' r, F r) - (∑' r, G r)‖ ≤ _
  rw [← hsF.tsum_sub hsG]
  calc
    _ ≤ ∑' r, ‖F r-G r‖ := norm_tsum_le_tsum_norm habs
    _ ≤ _ := (habs.tsum_le_tsum hmaj (hsum.mul_left _)).trans_eq (by rw [tsum_mul_left]; dsimp [W,E]; ring)

theorem prime_minus_main_plus_right {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hf0 : ∀ x ≤ 0, f x = 0) {K T : ℝ}
    (hK : 0 ≤ K) (hT : 1 ≤ T)
    (hB : ∀ r : NontrivialZetaZero, ‖compactZeroTerm (scaleTest 0 f) r‖ ≤ w2 r*K) :
    ‖Complex.exp (-(T:ℂ))*(∑' n : ℕ, mangoldtCoeff n * f (Real.log n-T)) -
      (∫ x in Ioi (0:ℝ), Complex.exp (x:ℂ)*f x) + rightSum T f‖ ≤
      ((2*∫ x : ℝ, ‖f x‖) + ‖∫ x in Ioi (0:ℝ), f x‖)*Real.exp (-T)
        + K*W*Real.exp (-(T/6)) := by
  have hT0 : 0 ≤ T := by linarith
  rw [smoothed_prime_explicit_identity hf hc hf0 hT0]
  let P := Complex.exp (-(T:ℂ)) * (∫ x in Ioi (0:ℝ), f x)
  let A := ∫ x in Ioi (0:ℝ), (ArchimedeanLimit.realPlaceKernel x:ℂ)*scaleTest T f x
  let Z := ∑' r : NontrivialZetaZero, compactZeroTerm (scaleTest T f) r
  have hP : ‖P‖ = ‖∫ x in Ioi (0:ℝ), f x‖*Real.exp (-T) := by
    simp only [P,norm_mul,Complex.norm_exp,Complex.neg_re,Complex.ofReal_re,mul_comm]
  have hA := scaled_real_place_bound hf hc hf0 hT
  have hZ := zero_sum_minus_right hf0 hK hT0 hB
  have h := (norm_sub_le (P-A) (Z-rightSum T f)).trans
    (add_le_add ((norm_sub_le P A).trans (add_le_add hP.le hA)) hZ)
  convert h using 1
  · congr 1
    dsimp only [P,A,Z]
    ring
  · ring

open SharpChebyshevError SmoothedPrimeSandwichUniform ArithmeticFunction Filter

def shellRight (T a b h : ℝ) : ℂ := rightSum T (fun x => (shell a b h x : ℂ))

theorem shell_right_error {a b h T : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b+h < 3)
    (hh : 0 < h) (hT : 1 ≤ T) :
    |realPrimeTest (shell a b h) T - mass (shell a b h)| ≤ ‖shellRight T a b h‖ +
      9*Real.exp (-T) + ((Real.exp 3*(2*curvatureMass)/h)*W)*Real.exp (-(T/6)) := by
  let B := Real.exp 3*(2*curvatureMass)
  have hB : 0 ≤ B := by unfold B curvatureMass; positivity
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
  have hshell := prime_minus_main_plus_right hs hc hz (div_nonneg hB hh.le) hT
    (spectral_majorant hab hh ha hb)
  let D := Complex.exp (-(T:ℂ))*(∑' n : ℕ, mangoldtCoeff n * g (Real.log n-T)) -
    (∫ x in Ioi (0:ℝ), Complex.exp (x:ℂ)*g x)
  have hd : ‖D‖ = |realPrimeTest f T - mass f| := by
    dsimp only [D,realPrimeTest,mass,g,mangoldtCoeff]
    simp only [← Complex.ofReal_neg,← Complex.ofReal_exp,← Complex.ofReal_mul,← Complex.ofReal_tsum,
      integral_complex_ofReal,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have ht := norm_sub_le (D+rightSum T g) (rightSum T g)
  rw [add_sub_cancel_right] at ht
  rw [← hd]
  have hbound : (2*∫ x : ℝ, ‖g x‖) + ‖∫ x in Ioi (0:ℝ), g x‖ ≤ 9 := by linarith
  apply (ht.trans (add_le_add hshell (le_refl _))).trans
  change _ ≤ ‖rightSum T g‖ + 9*Real.exp (-T) + (B/h*W)*Real.exp (-(T/6))
  linarith [mul_le_mul_of_nonneg_right hbound (Real.exp_pos (-T)).le]

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

private theorem general_sandwich {p q h : ℝ} (hh : 0 < h) (hpq : p+h ≤ q-h) (x : ℝ) :
    shell p (q-h) h x ≤ (Ioc p q).indicator (fun _ => (1:ℝ)) x ∧
    (Ioc p q).indicator (fun _ => (1:ℝ)) x ≤ shell (p-h) q h x := by
  by_cases hx : x ∈ Ioc p q
  · rw [Set.indicator_of_mem hx,shell_one hh (by linarith [hx.1]) hx.2]
    exact ⟨(shell_range (by linarith : p ≤ q-h) hh x).2,le_rfl⟩
  · rw [Set.indicator_of_notMem hx]
    refine ⟨?_,(shell_range (by linarith : p-h ≤ q) hh x).1⟩
    by_cases h1 : x ≤ p
    · rw [shell_left (by linarith) hh h1]
    · rw [shell_right (by linarith) hh (by by_contra! e; exact hx ⟨lt_of_not_ge h1,by linarith⟩)]

def intervalShell (p q T : ℝ) := Real.exp (-T)*(Chebyshev.psi (Real.exp (T+q))-Chebyshev.psi (Real.exp (T+p)))

theorem interval_sandwich {p q h : ℝ} (hh : 0 < h) (hpq : p+h ≤ q-h) (T : ℝ) :
    realPrimeTest (shell p (q-h) h) T ≤ intervalShell p q T ∧
    intervalShell p q T ≤ realPrimeTest (shell (p-h) q h) T := by
  let L := Real.exp (T+p)
  let U := Real.exp (T+q)
  have he (n : ℕ) :
      primeCut U n - primeCut L n =
      vonMangoldt n * (Ioc p q).indicator (fun _ => (1:ℝ)) (Real.log n-T) := by
    by_cases hn : n = 0
    · simp [hn,primeCut]
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hL : n ≤ ⌊L⌋₊ ↔ Real.log n-T ≤ p := by
      rw [← log_le_iff_nat_floor (Real.exp_pos _) hn1]
      simp [Real.log_exp]; constructor <;> intro h <;> linarith
    have hU : n ≤ ⌊U⌋₊ ↔ Real.log n-T ≤ q := by
      rw [← log_le_iff_nat_floor (Real.exp_pos _) hn1]
      simp [Real.log_exp]; constructor <;> intro h <;> linarith
    simp only [primeCut,Finset.mem_Icc,hn1,true_and,hU,hL]
    by_cases hl : Real.log n-T ≤ p
    · have hu : Real.log n-T ≤ q := by linarith
      simp [hl,hu,Set.indicator,Set.mem_Ioc,not_lt.mpr hl]
    · by_cases hu : Real.log n-T ≤ q <;> simp [hl,hu,Set.indicator,Set.mem_Ioc,lt_of_not_ge hl]
  have hsm := (primeCut_summable U).sub (primeCut_summable L)
  have hcut : intervalShell p q T = Real.exp (-T) * ∑' n : ℕ, (primeCut U n-primeCut L n) := by
    rw [(primeCut_summable U).tsum_sub (primeCut_summable L),primeCut_sum,primeCut_sum]
    rfl
  rw [hcut,realPrimeTest,realPrimeTest]
  constructor
  · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply (primeTest_summable (shell_compact (by linarith) hh) T).tsum_le_tsum _ hsm
    intro n
    rw [he]
    exact mul_le_mul_of_nonneg_left (general_sandwich hh hpq _).1 vonMangoldt_nonneg
  · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply hsm.tsum_le_tsum _ (primeTest_summable (shell_compact (by linarith) hh) T)
    intro n
    change primeCut U n - primeCut L n ≤ _
    rw [he]
    exact mul_le_mul_of_nonneg_left (general_sandwich hh hpq _).2 vonMangoldt_nonneg

def dyadicWidth (T : ℝ) := Real.exp (-(T/12))/8

def dyadicRight (T : ℝ) : ℝ :=
  max ‖shellRight T 1 (1+Real.log 2-dyadicWidth T) (dyadicWidth T)‖
    ‖shellRight T (1-dyadicWidth T) (1+Real.log 2) (dyadicWidth T)‖

theorem dyadic_endpoint_reduction :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      |(Chebyshev.psi (2*Real.exp (T+1))-Chebyshev.psi (Real.exp (T+1))) -
        Real.exp (T+1)| ≤ Real.exp T*(dyadicRight T + C*Real.exp (-(T/12))) := by
  let q := 1+Real.log 2
  let B := Real.exp 3*(2*curvatureMass)
  let M := 2*(Real.exp q + Real.exp 1)
  have hW : 0 ≤ W := tsum_nonneg fun r => by dsimp only [w2,w32]; positivity
  have hB : 0 ≤ B := by dsimp [B,curvatureMass]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M/8+9+8*B*W,by positivity,?_⟩
  intro T hT
  let u := Real.exp (-(T/12))
  let h := dyadicWidth T
  have hu : 0 < u := Real.exp_pos _
  have hu1 : u ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hh : 0 < h := by dsimp [h,dyadicWidth]; positivity
  have hh' : h = u/8 := rfl
  have hh1 : h ≤ 1/8 := by rw [hh']; linarith
  have hl : (1/2 : ℝ) ≤ Real.log 2 := by
    have e := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    rw [Real.log_inv] at e
    norm_num at e
    linarith
  have hl' := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hq : 1+h ≤ q-h := by dsimp [q]; linarith
  have hq' : q+h < 3 := by dsimp [q]; linarith
  have eqU : Real.exp (T+q) = 2*Real.exp (T+1) := by
    rw [show T+q=T+1+Real.log 2 by dsimp [q]; ring, Real.exp_add,
      Real.exp_log (by norm_num : (0:ℝ)<2),mul_comm]
  have eqQ : Real.exp q = 2*Real.exp 1 := by
    rw [show q=1+Real.log 2 from rfl,Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2),mul_comm]
  have le1 := abs_le.mp (shell_right_error (by linarith : 1 ≤ q-h) (by norm_num)
    (by linarith) hh hT)
  have le2 := abs_le.mp (shell_right_error (by linarith : 1-h ≤ q) (by linarith)
    hq' hh hT)
  obtain ⟨ls,us⟩ := interval_sandwich hh hq T
  have m1 := (shell_mass hh (by norm_num : (0:ℝ)≤1) hq).1
  have m2 := (shell_mass hh (by linarith : 0 ≤ 1-h) (by linarith : 1-h+h≤q)).2
  have ep : Real.exp h-1 ≤ 2*h := (le_abs_self _).trans
    (by simpa [abs_of_pos hh] using Real.abs_exp_sub_one_le (x := h) (by rw [abs_of_pos hh]; linarith))
  have em := Real.add_one_le_exp (-h)
  rw [sub_eq_add_neg q h,Real.exp_add q (-h),Real.exp_add 1 h] at m1
  rw [sub_eq_add_neg (1:ℝ) h,Real.exp_add 1 (-h),Real.exp_add q h] at m2
  have h₁ := mul_le_mul_of_nonneg_left ep (Real.exp_pos 1).le
  have h₂ := mul_le_mul_of_nonneg_left ep (Real.exp_pos q).le
  have h₃ := mul_le_mul_of_nonneg_left em (Real.exp_pos 1).le
  have h₄ := mul_le_mul_of_nonneg_left em (Real.exp_pos q).le
  have h₅ := mul_nonneg hh.le (Real.exp_pos 1).le
  have h₆ := mul_nonneg hh.le (Real.exp_pos q).le
  have hr1 : ‖shellRight T 1 (q-h) h‖ ≤ dyadicRight T := le_max_left _ _
  have hr2 : ‖shellRight T (1-h) q h‖ ≤ dyadicRight T := le_max_right _ _
  have hcut : |intervalShell 1 q T - (Real.exp q-Real.exp 1)| ≤
    dyadicRight T + M*h + 9*Real.exp (-T) + B/h*W*Real.exp (-(T/6)) := by
    dsimp only [M,B]
    rw [← sub_eq_add_neg] at m1 m2
    exact abs_le.mpr ⟨by linarith [le1.1], by linarith [le2.2]⟩
  have hsqu : Real.exp (-(T/6)) = u*u := by
    dsimp only [u]
    rw [← Real.exp_add]
    congr 1
    ring
  have het : Real.exp (-T) ≤ u := Real.exp_le_exp.mpr (by linarith)
  have hprod : B/h*W*(u*u) = 8*B*W*u := by rw [hh']; field_simp
  rw [hsqu, hprod, hh'] at hcut
  have hc' : |intervalShell 1 q T - (Real.exp q-Real.exp 1)| ≤
      dyadicRight T + (M/8+9+8*B*W)*u := hcut.trans (by nlinarith)
  have hid : Real.exp T*(intervalShell 1 q T-(Real.exp q-Real.exp 1)) =
      Chebyshev.psi (2*Real.exp (T+1)) - Chebyshev.psi (Real.exp (T+1)) - Real.exp (T+1) := by
    rw [intervalShell,eqU,eqQ,mul_sub,← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul,
      Real.exp_add T 1]
    ring
  rw [← hid,abs_mul,abs_of_pos (Real.exp_pos T)]
  exact mul_le_mul_of_nonneg_left hc' (Real.exp_pos _).le

#print axioms dyadic_endpoint_reduction
#print axioms shell_right_error
#print axioms interval_sandwich
#print axioms zero_sum_minus_right
#print axioms prime_minus_main_plus_right
end RHConnections.PrimeRightCut
