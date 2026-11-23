import Verified
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set
noncomputable section
namespace RHConnections.ZetaZeroFreeRegion
open PoleCompensation RelativeResolvent ArchimedeanLimit

theorem realPlaceRelative_log_bound {z : ℂ} (hz : 0 ≤ z.re) :
    ‖realPlaceRelative z 1‖ ≤ 36+8*Real.log (‖z‖+1) := by
  let M := ‖z‖+1
  let δ := M⁻¹
  have hM : 0 < M := by dsimp [M]; positivity
  have hδ : 0 < δ := inv_pos.mpr hM
  have hδ₁ : δ ≤ 1 := inv_le_one_of_one_le₀ (by dsimp [M]; linarith [norm_nonneg z])
  let F : ℝ → ℂ := fun x => (realPlaceKernel x:ℂ)*logTest z 1 x
  let K : ℝ → ℝ := fun x => ‖F x‖
  let E : ℝ → ℝ := fun x => Real.exp (-(1/4:ℝ)*x)
  have hE : IntegrableOn E (Ioi (0:ℝ)) :=
    integrableOn_exp_mul_Ioi (by norm_num : -(1/4:ℝ) < 0) 0
  have hnorm (x : ℝ) (hx : 0 < x) : K x = realPlaceKernel x * ‖logTest z 1 x‖ := by
    dsimp only [K,F]
    rw [norm_mul,Complex.norm_of_nonneg (realPlaceKernel_nonneg hx)]
  have hLin (x : ℝ) (hx : 0 < x) : K x ≤ 4*M*E x := by
    have hl : ‖logTest z 1 x‖ ≤ M*x := by
      simpa only [M,norm_one] using logTest_linear hz (by norm_num : (0:ℝ) ≤ (1:ℂ).re) hx.le
    calc
      _ = realPlaceKernel x * ‖logTest z 1 x‖ := hnorm x hx
      _ ≤ realPlaceKernel x*(M*x) := mul_le_mul_of_nonneg_left hl (realPlaceKernel_nonneg hx)
      _ = (realPlaceKernel x*x)*M := by ring
      _ ≤ 4*M*E x := by
        simpa only [E] using (mul_le_mul_of_nonneg_right (realPlaceKernel_mul_x_bound hx) hM.le).trans_eq
          (by ring)
  have hExp (x : ℝ) (hx : 0 < x) : ‖logTest z 1 x‖ ≤ 2 := by
    rw [logTest, if_pos hx]
    apply (norm_sub_le _ _).trans
    have hC (w : ℂ) (hw : 0 ≤ w.re) : ‖Complex.exp (-w*(x:ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp,Real.exp_le_one_iff]
      simpa only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,sub_zero] using mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hw) hx.le
    linarith [hC z hz, hC 1 (by norm_num)]
  have hRat (x : ℝ) (hx : 0 < x) : K x ≤ 8*(E x*x⁻¹) := by
    rw [hnorm x hx]
    have hk : realPlaceKernel x ≤ 4*E x*x⁻¹ := by
      calc
        _ = (realPlaceKernel x*x)*x⁻¹ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (realPlaceKernel_mul_x_bound hx) (inv_nonneg.mpr hx.le)
    calc
      _ ≤ realPlaceKernel x*2 := mul_le_mul_of_nonneg_left (hExp x hx) (realPlaceKernel_nonneg hx)
      _ ≤ (4*E x*x⁻¹)*2 := mul_le_mul_of_nonneg_right hk (by norm_num)
      _ = _ := by ring
  have hEle (x : ℝ) (hx : 0 < x) : E x ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hFi : IntegrableOn F (Ioi (0:ℝ)) := by
    apply (hE.const_mul (4*M)).mono'
    · have hk : Measurable (fun x => (realPlaceKernel x:ℂ)) := by
        apply Complex.continuous_ofReal.measurable.comp
        unfold realPlaceKernel
        fun_prop
      exact hk.aestronglyMeasurable.mul (logTest_continuous z 1).aestronglyMeasurable
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => hLin x hx))
  have hK : IntegrableOn K (Ioi (0:ℝ)) := Integrable.norm hFi
  have hE8 : IntegrableOn (fun x => 8*E x) (Ioi (0:ℝ)) := hE.const_mul 8
  let A := Ioc (0:ℝ) δ
  let B := Ioc δ 1
  let D := Ioi (1:ℝ)
  have hA : A ⊆ Ioi (0:ℝ) := fun _ hx => hx.1
  have hB : B ⊆ Ioi (0:ℝ) := fun _ hx => hδ.trans hx.1
  have hD : D ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi (by norm_num)
  have hAB : Disjoint A B := Set.disjoint_left.mpr fun _ ha hb => (not_lt_of_ge ha.2) hb.1
  have hABD : Disjoint (A ∪ B) D := Set.disjoint_left.mpr fun _ ha hd =>
    ha.elim (fun h => (not_lt_of_ge (h.2.trans hδ₁)) hd) (fun h => (not_lt_of_ge h.2) hd)
  have hUnion : A ∪ B ∪ D = Ioi (0:ℝ) := by
    ext x
    constructor
    · exact fun h => h.elim (fun h' => h'.elim (fun ha => hA ha) (fun hb => hB hb)) (fun hd => hD hd)
    · intro h
      by_cases h1 : x ≤ 1
      · by_cases h2 : x ≤ δ
        · exact Or.inl (Or.inl ⟨h,h2⟩)
        · exact Or.inl (Or.inr ⟨lt_of_not_ge h2,h1⟩)
      · exact Or.inr (lt_of_not_ge h1)
  have hIntA : (∫ x in A, K x) ≤ 4 := by
    have hma : (volume : Measure ℝ).real A = δ := by
      simp [A,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hδ.le]
    calc
      _ ≤ ∫ _ in A, 4*M := setIntegral_mono_on (hK.mono_set hA)
        (integrableOn_const (measure_Ioc_lt_top.ne)) measurableSet_Ioc
        (fun x hx => (hLin x hx.1).trans
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hEle x hx.1) (by positivity : 0 ≤ 4*M)))
      _ = 4 := by rw [setIntegral_const,hma,smul_eq_mul]; dsimp [δ]; field_simp
  have hIntB : (∫ x in B, K x) ≤ 8*Real.log M := by
    have hInv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume δ 1 := by
      apply ContinuousOn.intervalIntegrable
      have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Icc δ 1) :=
        continuousOn_id.inv₀ fun x hx => (hδ.trans_le hx.1).ne'
      simpa only [uIcc_of_le hδ₁] using hc
    have hi : IntegrableOn (fun x : ℝ => 8*x⁻¹) B := hInv.1.const_mul 8
    calc
      _ ≤ ∫ x in B, 8*x⁻¹ := setIntegral_mono_on (hK.mono_set hB) hi measurableSet_Ioc
        (fun x hx => (hRat x (hB hx)).trans
          (by
          have he := mul_le_mul_of_nonneg_right (hEle x (hB hx)) (inv_nonneg.mpr (hB hx).le)
          simpa only [one_mul] using mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 8)))
      _ = 8*Real.log M := by
        rw [integral_const_mul,← intervalIntegral.integral_of_le hδ₁,integral_inv_of_pos hδ (by norm_num)]
        simp [δ]
  have hIntD : (∫ x in D, K x) ≤ 32 := by
    calc
      _ ≤ ∫ x in D, 8*E x := setIntegral_mono_on (hK.mono_set hD)
        (hE8.mono_set hD) measurableSet_Ioi
        (fun x hx => (hRat x (hD hx)).trans (by
          have hi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (show 1 ≤ x from hx.le)
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le) (by norm_num : (0:ℝ) ≤ 8)))
      _ ≤ 32 := by
        simp only [D,E,integral_const_mul]
        rw [integral_exp_mul_Ioi (by norm_num : -(1/4:ℝ) < 0) 1]
        nlinarith [Real.exp_le_one_iff.mpr (by norm_num : -(1/4 : ℝ)*1 ≤ 0)]
  change ‖∫ x in Ioi (0:ℝ), F x‖ ≤ _
  apply (norm_integral_le_integral_norm _).trans
  change (∫ x in Ioi (0:ℝ), K x) ≤ _
  rw [← hUnion, setIntegral_union hABD measurableSet_Ioi
    (hK.mono_set (union_subset hA hB)) (hK.mono_set hD),
    setIntegral_union hAB measurableSet_Ioc (hK.mono_set hA) (hK.mono_set hB)]
  change _ ≤ 36+8*Real.log M
  linarith

end RHConnections.ZetaZeroFreeRegion
