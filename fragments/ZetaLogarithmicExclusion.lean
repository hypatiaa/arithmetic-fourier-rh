import Verified

noncomputable section
namespace RHConnections.ZetaZeroFreeRegion
open PoleCompensation PerronRampBounds SpectralTail

private theorem vertical_im (σ t : ℝ) : (vertical σ t).im = t := by
  simp [vertical,Complex.add_im,Complex.mul_im]

theorem combined_slope_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      (zetaSlope s).re + (logDeriv entireXi s).re ≤
        ((s-1)⁻¹).re + C + 8*Real.log (3+|s.im|) := by
  let c := logDeriv Complex.Gammaℝ (3/2)
  refine ⟨37+‖c‖,by positivity,?_⟩
  intro s hs h2
  let z := s-1/2
  have hz : 0 ≤ z.re := by
    dsimp [z]
    norm_num [Complex.sub_re,Complex.div_re]
    linarith
  have hzLog := realPlaceRelative_log_bound hz
  have hzn : ‖z‖+1 ≤ 3+|s.im| := by
    have hre : z.re = s.re-1/2 := by norm_num [z,Complex.sub_re,Complex.div_re]
    have him : z.im = s.im := by norm_num [z,Complex.sub_im,Complex.div_im]
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg hz, hre,him] at h
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < ‖z‖+1) hzn
  have hΓ := realPlaceRelative_eq_gammaDifference hz (by norm_num : 0 ≤ (1:ℂ).re)
  rw [show (z+(1/2:ℂ)) = s by dsimp [z]; ring,
    show (1:ℂ)+1/2=3/2 by ring] at hΓ
  have hΓ' : (logDeriv Complex.Gammaℝ s).re ≤ ‖c‖ + ‖realPlaceRelative z 1‖ := by
    have hreal := congrArg Complex.re hΓ
    rw [Complex.sub_re] at hreal
    change (realPlaceRelative z 1).re = c.re - (logDeriv Complex.Gammaℝ s).re at hreal
    have hn := Complex.re_le_norm (-(realPlaceRelative z 1))
    rw [Complex.neg_re,norm_neg] at hn
    linarith [Complex.re_le_norm c]
  have hsInv : ‖s⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (hs.le.trans (Complex.re_le_norm s))
  have he := entireXi_logDerivative_euler hs
  simp only [one_div] at he
  have hζ : zetaSlope s = -logDeriv riemannZeta s := by rw [zetaSlope,logDeriv_apply,neg_div]
  rw [hζ,Complex.neg_re,he]
  simp only [Complex.add_re]
  linarith [Complex.re_le_norm s⁻¹]

theorem slope_upper_with_zero_contribution :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
        (zetaSlope s).re ≤ ((s-1)⁻¹).re + C + 8*Real.log (3+|s.im|)) ∧
      (∀ (s : ℂ) (rho : NontrivialZetaZero), 1 < s.re → s.re ≤ 2 →
        (zetaSlope s).re + ((s-rho.val)⁻¹).re ≤ ((s-1)⁻¹).re + C + 8*Real.log (3+|s.im|)) := by
  obtain ⟨C,hC,hUp⟩ := combined_slope_log_bound
  obtain ⟨A,hA,hLo,hLoZero⟩ := completed_logDerivative_real_lower
  refine ⟨C+A+1,by linarith,?_ ,?_⟩
  · intro s hs h2
    linarith [hUp s hs h2,hLo s hs]
  · intro s rho hs h2
    linarith [hUp s hs h2,hLoZero s rho hs]

private theorem inv_vertical_sub_one_re_le_one {σ t : ℝ} (ht : 1 ≤ |t|) :
    (((vertical σ t)-1)⁻¹).re ≤ 1 := by
  have hnorm : 1 ≤ ‖(vertical σ t)-1‖ := by
    have him := Complex.abs_im_le_norm ((vertical σ t)-1)
    rw [Complex.sub_im, Complex.one_im, sub_zero,vertical_im] at him
    exact ht.trans him
  exact (Complex.re_le_norm _).trans (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hnorm)

theorem nontrivial_zero_logarithmic_exclusion :
    ∃ c : ℝ, 0 < c ∧ ∀ rho : NontrivialZetaZero, 1 ≤ |rho.val.im| →
      rho.val.re ≤ 1-c/(1+Real.log (3+2*|rho.val.im|)) := by
  obtain ⟨C,hC,hUp,hUpZero⟩ := slope_upper_with_zero_contribution
  let D := C+9
  have hD : 1 ≤ D := by dsimp [D]; linarith
  refine ⟨(112*D)⁻¹,by positivity,?_⟩
  intro rho ht
  let t := rho.val.im
  let Q := 1+Real.log (3+2*|t|)
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    linarith [Real.log_nonneg (show 1 ≤ 3+2*|t| by linarith [abs_nonneg t])]
  let A := D*Q
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le hD hQ
  let e := (16*A)⁻¹
  let σ := 1+e
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ2 : σ ≤ 2 := by dsimp [σ]; linarith
  have hstrip (u : ℝ) : 1 < (vertical σ u).re ∧ (vertical σ u).re ≤ 2 := by
    rw [vertical_re]
    exact ⟨hσ,hσ2⟩
  have hb (u : ℝ) (hu : |u| ≤ 2*|t|) :
      C+1+8*Real.log (3+|u|) ≤ A := by
    have hl := Real.log_le_log (by positivity : 0 < 3+|u|) (by linarith : 3+|u| ≤ 3+2*|t|)
    have hlog : 0 ≤ Real.log (3+2*|t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    dsimp [A,D,Q]
    nlinarith [mul_nonneg (show 0 ≤ C+1 by linarith) hlog]
  have h0Inv : (((vertical σ 0)-1)⁻¹).re = e⁻¹ := by
    have heq : vertical σ 0-1 = (e:ℂ) := by
      apply Complex.ext
      · simp [vertical_re,Complex.sub_re,σ]
      · simp [vertical_im,Complex.sub_im]
    rw [heq,← Complex.ofReal_inv,Complex.ofReal_re]
  have hδ : 0 < σ-rho.val.re := by linarith [rho.property.1.2]
  have hρInv : (((vertical σ t)-rho.val)⁻¹).re = (σ-rho.val.re)⁻¹ := by
    have heq : vertical σ t-rho.val = ((σ-rho.val.re:ℝ):ℂ) := by
      apply Complex.ext
      · simp [vertical_re,Complex.sub_re]
      · simp [vertical_im,Complex.sub_im,t]
    rw [heq,← Complex.ofReal_inv,Complex.ofReal_re]
  have h0 := hUp (vertical σ 0) (hstrip 0).1 (hstrip 0).2
  rw [h0Inv,vertical_im] at h0
  have h0' : (zetaSlope (vertical σ 0)).re ≤ e⁻¹ + A := by
    have hbase := hb (0:ℝ) (by simp)
    simp only [abs_zero,add_zero] at h0 hbase
    linarith only [h0,hbase]
  have htU := hUpZero (vertical σ t) rho (hstrip t).1 (hstrip t).2
  rw [hρInv,vertical_im] at htU
  have ht' : (zetaSlope (vertical σ t)).re + (σ-rho.val.re)⁻¹ ≤ A := by
    linarith [hb t (by linarith [abs_nonneg t]),inv_vertical_sub_one_re_le_one (σ := σ) ht]
  have h2U := hUp (vertical σ (2*t)) (hstrip (2*t)).1 (hstrip (2*t)).2
  rw [vertical_im] at h2U
  have h2t : |2*t| = 2*|t| := by rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h2' : (zetaSlope (vertical σ (2*t))).re ≤ A := by
    have h := inv_vertical_sub_one_re_le_one (σ := σ) (t := 2*t) (by rw [h2t]; linarith : 1 ≤ |2*t|)
    linarith [hb (2*t) h2t.le]
  have heInv : e⁻¹ = 16*A := inv_inv _
  have hDeriv := zeta_three_point_positivity σ t hσ
  have hB : 4/(σ-rho.val.re) ≤ 56*A := by
    rw [div_eq_mul_inv]
    linarith [hDeriv,h0',ht',h2',heInv]
  have hB' : 4/(56*A) ≤ σ-rho.val.re := (div_le_iff₀ (by positivity)).mpr
    (by rw [mul_comm]; exact (div_le_iff₀ hδ).mp hB)
  have hcalc : 4/(56*A)-e = (112*D)⁻¹/Q := by
    dsimp [e,A]
    have hd0 : D ≠ 0 := by positivity
    have hq0 : Q ≠ 0 := by positivity
    field_simp [hd0,hq0] <;> ring
  change rho.val.re ≤ 1-(112*D)⁻¹/Q
  linarith only [hB',hcalc,show σ = 1+e from rfl]

end RHConnections.ZetaZeroFreeRegion
