import Verified

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace RHConnections.SmoothedPrimeUniform
open SpectralTail ZetaZeroFreeRegion ChebyshevCriterion SmoothedPrimeLimit

private abbrev squareWeight (r : NontrivialZetaZero) : ℝ :=
  (analyticOrderNatAt riemannZeta r.val : ℝ)/‖r.val‖^2

private abbrev threeHalvesWeight (r : NontrivialZetaZero) : ℝ :=
  (analyticOrderNatAt riemannZeta r.val : ℝ)/(‖r.val‖*Real.sqrt ‖r.val‖)

theorem uniform_zero_sum :
    ∃ d W : ℝ, 0 < d ∧ d ≤ 1/2 ∧ 0 ≤ W ∧
    ∀ {f : ℝ → ℂ}, (∀ x ≤ 0, f x = 0) → ∀ {K : ℝ}, 0 ≤ K →
    (∀ r : NontrivialZetaZero, ‖compactZeroTerm (scaleTest 0 f) r‖ ≤
        ((analyticOrderNatAt riemannZeta r.val : ℝ)/‖r.val‖^2)*K) →
    ∀ T : ℝ, 1 ≤ T → ‖∑' r : NontrivialZetaZero, compactZeroTerm (scaleTest T f) r‖ ≤
      (K*W)*Real.exp (-d*Real.sqrt T) := by
  obtain ⟨c,hc0,_,hZeroFree⟩ := all_height_logarithmic_exclusion
  let d : ℝ := min (c/6) (1/2)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hdc : d ≤ c/6 := min_le_left _ _
  have hd2 : d ≤ 1/2 := min_le_right _ _
  refine ⟨d,∑' r : NontrivialZetaZero, (squareWeight r+threeHalvesWeight r),hd,hd2,
    tsum_nonneg (fun r => by dsimp only [squareWeight,threeHalvesWeight]; positivity),?_⟩
  intro f hf0 K hK hB
  have hSum : Summable (fun r : NontrivialZetaZero => squareWeight r+threeHalvesWeight r) :=
    zeta_inverse_square_with_multiplicity.add zeta_inverse_three_halves_with_multiplicity
  have hNonneg (r : NontrivialZetaZero) : 0 ≤ squareWeight r+threeHalvesWeight r := by
    dsimp [squareWeight,threeHalvesWeight]
    positivity
  let C := K * ∑' r : NontrivialZetaZero, (squareWeight r+threeHalvesWeight r)
  change ∀ T : ℝ, 1 ≤ T → _ ≤ C * Real.exp (-d*Real.sqrt T)
  intro T hT
  let L := Real.sqrt T
  let E := Real.exp (-d*L)
  have hT0 : 0 ≤ T := by linarith
  have hL1 : 1 ≤ L := by
    simpa only [L,Real.sqrt_one] using Real.sqrt_le_sqrt hT
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hLsq : L^2 = T := Real.sq_sqrt hT0
  have hE : 0 < E := Real.exp_pos _
  have hMajor (r : NontrivialZetaZero) :
      ‖compactZeroTerm (scaleTest T f) r‖ ≤ K*E*(squareWeight r+threeHalvesWeight r) := by
    have hBeta : r.val.re < 1 := r.property.1.2
    have hsq : 0 ≤ squareWeight r := by dsimp [squareWeight]; positivity
    have hthree : 0 ≤ threeHalvesWeight r := by dsimp [threeHalvesWeight]; positivity
    obtain ⟨δ,hδ,hδr⟩ := zeta_zero_norm_lower
    have hn : 0 < ‖r.val‖ := hδ.trans_le (hδr r)
    rw [scaled_zero_term_eq hf0 hT0,norm_mul,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    by_cases hlow : ‖r.val‖ ≤ Real.exp L
    · have hArg : 3+2*|r.val.im| ≤ 5*Real.exp L := by
        have h := (Complex.abs_im_le_norm r.val).trans hlow
        linarith [Real.one_le_exp_iff.mpr hL.le]
      have hlog : Real.log (3+2*|r.val.im|) ≤ Real.log 5+L := by
        have h := Real.log_le_log (by linarith [abs_nonneg r.val.im] : 0 < 3+2*|r.val.im|) hArg
        rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp] at h
        exact h
      have hHeight : heightFactor r.val.im ≤ 6*L := by
        unfold heightFactor
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5)]
      have hH0 : 0 < heightFactor r.val.im := zero_lt_one.trans_le (heightFactor_one_le _)
      have hgap : c/heightFactor r.val.im ≤ 1-r.val.re := by linarith [(hZeroFree r).2]
      have hpos := (div_le_iff₀ hH0).mp hgap
      have hmul := mul_le_mul_of_nonneg_right
        (hpos.trans (mul_le_mul_of_nonneg_left hHeight (sub_nonneg.mpr hBeta.le))) hL.le
      have hsmall : (r.val.re-1)*T ≤ -d*L := by
        nlinarith [mul_le_mul_of_nonneg_right hdc hL.le,
          show (1-r.val.re)*(6*L)*L = 6*(1-r.val.re)*T by rw [← hLsq]; ring]
      have hExp : Real.exp ((r.val.re-1)*T) ≤ E := Real.exp_le_exp.mpr hsmall
      calc
        _ ≤ E*(squareWeight r*K) := mul_le_mul hExp (hB r) (norm_nonneg _) hE.le
        _ ≤ E*((squareWeight r+threeHalvesWeight r)*K) := by
          have h : squareWeight r ≤ squareWeight r+threeHalvesWeight r := le_add_of_nonneg_right hthree
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hK) hE.le
        _ = _ := by ring
    · have hnorm1 : Real.exp L ≤ ‖r.val‖ := (lt_of_not_ge hlow).le
      have hsqrt : Real.exp (L/2) ≤ Real.sqrt ‖r.val‖ := by
        apply (Real.le_sqrt (Real.exp_pos _).le hn.le).mpr
        rw [pow_two,← Real.exp_add,show L/2+L/2=L by ring]
        exact hnorm1
      have hExp : Real.exp ((r.val.re-1)*T) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hBeta.le) hT0)
      have hInv : (Real.sqrt ‖r.val‖)⁻¹ ≤ E := by
        calc
          _ ≤ (Real.exp (L/2))⁻¹ := inv_anti₀ (Real.exp_pos _) hsqrt
          _ = Real.exp (-(L/2)) := (Real.exp_neg _).symm
          _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hd2 hL.le])
      have hdecomp : squareWeight r = threeHalvesWeight r*(Real.sqrt ‖r.val‖)⁻¹ := by
        dsimp only [squareWeight,threeHalvesWeight]
        have hs0 := (Real.sqrt_pos_of_pos hn).ne'
        field_simp [hn.ne',hs0]
        nlinarith [Real.sq_sqrt hn.le]
      calc
        _ ≤ 1*(squareWeight r*K) := mul_le_mul hExp (hB r) (norm_nonneg _) zero_le_one
        _ ≤ K*E*(squareWeight r+threeHalvesWeight r) := by
          rw [one_mul]
          have h : squareWeight r ≤ threeHalvesWeight r*E :=
            hdecomp.trans_le (mul_le_mul_of_nonneg_left hInv hthree)
          calc
            _ ≤ (threeHalvesWeight r*E)*K := mul_le_mul_of_nonneg_right h hK
            _ = (K*E)*threeHalvesWeight r := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hsq)
              (mul_nonneg hK hE.le)
  have hs : Summable (fun r : NontrivialZetaZero => ‖compactZeroTerm (scaleTest T f) r‖) :=
    (hSum.mul_left (K*E)).of_nonneg_of_le (fun _ => norm_nonneg _) hMajor
  calc
    _ ≤ ∑' r : NontrivialZetaZero, ‖compactZeroTerm (scaleTest T f) r‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' r : NontrivialZetaZero, K*E*(squareWeight r+threeHalvesWeight r) :=
      hs.tsum_le_tsum hMajor (hSum.mul_left _)
    _ = _ := by rw [tsum_mul_left]; dsimp [C,E]; ring

theorem uniform_prime_error :
    ∃ d W : ℝ, 0 < d ∧ d ≤ 1/2 ∧ 0 ≤ W ∧
    ∀ {f : ℝ → ℂ}, (ContDiff ℝ ∞ f) → HasCompactSupport f →
    (∀ x ≤ 0, f x = 0) → ∀ {K : ℝ}, 0 ≤ K →
    (∀ r : NontrivialZetaZero, ‖compactZeroTerm (scaleTest 0 f) r‖ ≤
        ((analyticOrderNatAt riemannZeta r.val : ℝ)/‖r.val‖^2)*K) →
    ∀ T : ℝ, 1 ≤ T →
      ‖Complex.exp (-(T:ℂ)) * (∑' n : ℕ, mangoldtCoeff n*f (Real.log n-T)) -
        (∫ x in Set.Ioi (0:ℝ), Complex.exp (x:ℂ)*f x)‖ ≤
      (K*W + 2*(∫ x : ℝ, ‖f x‖) + ‖∫ x in Set.Ioi (0:ℝ), f x‖) *
        Real.exp (-d*Real.sqrt T) := by
  obtain ⟨d,W,hd,hd2,hW,hZ⟩ := uniform_zero_sum
  refine ⟨d,W,hd,hd2,hW,?_⟩
  intro f hf hc hf0 K hK hB
  have hS := hZ hf0 hK hB
  let P := ∫ x in Set.Ioi (0:ℝ), f x
  let A := 2*∫ x : ℝ, ‖f x‖
  have hA : 0 ≤ A := mul_nonneg (by norm_num) (integral_nonneg fun _ => norm_nonneg _)
  change ∀ T : ℝ, 1 ≤ T → _ ≤ (K*W+A+‖P‖)*Real.exp (-d*Real.sqrt T)
  intro T hT
  have hTL : Real.sqrt T ≤ T := by
    have h1 : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt hT
    nlinarith [Real.sq_sqrt (show 0 ≤ T by linarith)]
  have hd' : d*Real.sqrt T ≤ T := (mul_le_mul_of_nonneg_right
    (show d ≤ 1 by linarith) (Real.sqrt_nonneg T)).trans (by simpa only [one_mul] using hTL)
  have he : Real.exp (-T) ≤ Real.exp (-d*Real.sqrt T) := Real.exp_le_exp.mpr (by linarith)
  rw [smoothed_prime_explicit_identity hf hc hf0 (by linarith : 0 ≤ T)]
  have h := norm_sub_le
    (Complex.exp (-(T:ℂ))*P - ∫ x in Set.Ioi (0:ℝ), (ArchimedeanLimit.realPlaceKernel x:ℂ)*scaleTest T f x)
    (∑' r : NontrivialZetaZero, compactZeroTerm (scaleTest T f) r)
  have hh := (norm_sub_le
    (Complex.exp (-(T:ℂ))*P)
    (∫ x in Set.Ioi (0:ℝ), (ArchimedeanLimit.realPlaceKernel x:ℂ)*scaleTest T f x)).trans
    (add_le_add (show ‖Complex.exp (-(T:ℂ))*P‖ ≤ Real.exp (-d*Real.sqrt T)*‖P‖ by
      simpa only [norm_mul,Complex.norm_exp,Complex.neg_re,Complex.ofReal_re] using
        mul_le_mul_of_nonneg_right he (norm_nonneg P))
      ((scaled_real_place_bound hf hc hf0 hT).trans (mul_le_mul_of_nonneg_left he hA)))
  have hb := add_le_add hh (hS T hT)
  have hRearr : (∫ x in Set.Ioi (0:ℝ), Complex.exp (x:ℂ)*f x) + Complex.exp (-(T:ℂ))*P -
      (∫ x in Set.Ioi (0:ℝ), (ArchimedeanLimit.realPlaceKernel x:ℂ)*scaleTest T f x) -
      (∑' r : NontrivialZetaZero, compactZeroTerm (scaleTest T f) r) -
      (∫ x in Set.Ioi (0:ℝ), Complex.exp (x:ℂ)*f x) =
        (Complex.exp (-(T:ℂ))*P - ∫ x in Set.Ioi (0:ℝ), (ArchimedeanLimit.realPlaceKernel x:ℂ)*scaleTest T f x) -
        (∑' r : NontrivialZetaZero, compactZeroTerm (scaleTest T f) r) := by ring
  rw [hRearr]
  exact (h.trans hb).trans_eq (by unfold A; ring)

end RHConnections.SmoothedPrimeUniform
