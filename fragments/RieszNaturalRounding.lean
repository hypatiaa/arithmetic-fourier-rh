import Verified

noncomputable section
open MeasureTheory Set Filter
namespace RHConnections.RieszPrimeMellin
open PrimeErrorLaplace

private theorem prime_error_integral_linear {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    IntegrableOn realPrimeError (Set.Ioc u v) ∧
      |∫ t in Set.Ioc u v, realPrimeError t|≤(Real.log 4+5)*v*(v-u) := by
  let D := Real.log 4+5
  have hD : 0≤D := by dsimp [D]; linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
  have hI : IntegrableOn (fun _ : ℝ => D*v) (Set.Ioc u v) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hbound (t : ℝ) (ht : t∈Set.Ioc u v) : ‖realPrimeError t‖≤D*v := by
    rw [Real.norm_eq_abs]
    exact (real_prime_error_linear (hu.trans ht.1.le)).trans (mul_le_mul_of_nonneg_left ht.2 hD)
  have he : IntegrableOn realPrimeError (Set.Ioc u v) :=
    hI.mono' real_prime_error_measurable.aestronglyMeasurable ((ae_restrict_mem measurableSet_Ioc).mono hbound)
  refine ⟨he,?_⟩
  rw [←Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  have h := integral_mono_ae he.norm hI ((ae_restrict_mem measurableSet_Ioc).mono hbound)
  simpa [integral_const,max_eq_left (sub_nonneg.mpr huv),mul_comm] using h

theorem riesz_floor_error {x : ℝ} (hx : 1≤x) :
    |rieszError x-rieszError (⌊x⌋₊:ℝ)|≤2*(Real.log 4+5) := by
  let n : ℝ := (⌊x⌋₊:ℕ)
  let D := Real.log 4+5
  have hx0 := zero_lt_one.trans_le hx
  have hN : (1:ℕ)≤⌊x⌋₊ := (Nat.le_floor_iff hx0.le).mpr (by simpa using hx)
  have hn1 : 1≤n := by dsimp [n]; exact_mod_cast hN
  have hn0 := zero_lt_one.trans_le hn1
  have hnx : n≤x := Nat.floor_le hx0.le
  have hdiff : x-n≤1 := by linarith only [Nat.lt_floor_add_one x]
  have hD : 0≤D := by dsimp [D]; linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
  let A := ∫ t in Set.Ioc 1 n, realPrimeError t
  let B := ∫ t in Set.Ioc n x, realPrimeError t
  obtain ⟨hiA,hA⟩ := prime_error_integral_linear (show (0:ℝ)≤1 by norm_num) hn1
  obtain ⟨hiB,hB⟩ := prime_error_integral_linear hn0.le hnx
  have he : (∫ t in Set.Ioc (1:ℝ) x, realPrimeError t)=A+B := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hn1 |>.mpr hiA)
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hnx |>.mpr hiB)
    simpa only [intervalIntegral.integral_of_le hn1,intervalIntegral.integral_of_le hnx,
      intervalIntegral.integral_of_le hx,A,B] using h.symm
  have hEq : rieszError x-rieszError n = x⁻¹*B-(x-n)/(x*n)*A := by
    rw [rieszError,rieszError,he]
    field_simp [hx0.ne',hn0.ne']
    ring
  have hxB : |x⁻¹*B|≤D := by
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hx0.le)]
    change x⁻¹*|B|≤D
    calc
      _ ≤ x⁻¹*(D*x*(x-n)) := mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr hx0.le)
      _ = D*(x-n) := by field_simp
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hdiff hD
  have hfrac : 0≤(x-n)/(x*n) := by positivity
  have hxA : |(x-n)/(x*n)*A|≤D := by
    rw [abs_mul,abs_of_nonneg hfrac]
    calc
      _ ≤ ((x-n)/(x*n))*(D*n*(n-1)) := mul_le_mul_of_nonneg_left hA hfrac
      _ = D*(x-n)*((n-1)/x) := by field_simp [hn0.ne']
      _ ≤ D*(x-n)*1 := mul_le_mul_of_nonneg_left
        ((div_le_one hx0).mpr (by linarith)) (mul_nonneg hD (sub_nonneg.mpr hnx))
      _ ≤ D := by rw [mul_one]; simpa using mul_le_mul_of_nonneg_left hdiff hD
  rw [hEq]
  exact (abs_sub _ _).trans ((add_le_add hxB hxA).trans_eq (by dsimp [D]; ring))

theorem zero_free_of_one_sided_natural_riesz_power {a σ C : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hσ : σ=1 ∨ σ= -1) (hC : 0≤C)
    (h : ∀ᶠ n : ℕ in atTop, -(C*(n:ℝ)^a)≤σ*rieszError (n:ℝ)) :
    ∀ s : ℂ, a<s.re → riemannZeta s≠0 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  let D := Real.log 4+5
  let Y := (N:ℝ)+1
  let K := C+2*D+D*Y
  have hσ' : |σ|=1 := by rcases hσ with rfl|rfl <;> norm_num
  have hD : 0≤D := by dsimp [D]; linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
  have hY : 0≤Y := by dsimp [Y]; positivity
  apply zero_free_of_one_sided_riesz_power ha ha1 hσ (C := K)
  intro x hx
  have hx0 : 0<x := by linarith
  have hp : 0<x^a := Real.rpow_pos_of_pos hx0 a
  have hp1 := Real.one_le_rpow hx.le ha
  have hBound : -K*x^a≤σ*rieszError x := by
    by_cases hLarge : Y≤x
    · let n := ⌊x⌋₊
      have hNat : N≤n := (Nat.le_floor_iff hx0.le).mpr (by dsimp [Y] at hLarge; linarith)
      have hFreq := hN n hNat
      have hRound := riesz_floor_error hx.le
      have hSign := neg_abs_le (σ*(rieszError x-rieszError (n:ℝ)))
      rw [abs_mul,hσ',one_mul,mul_sub] at hSign
      have hp' := Real.rpow_le_rpow (Nat.cast_nonneg n) (Nat.floor_le hx0.le) ha
      have hTwo := le_mul_of_one_le_right (show 0≤2*D by positivity) hp1
      change |rieszError x-rieszError (n:ℝ)|≤2*D at hRound
      dsimp only [K]
      linarith only [hSign,hRound,hFreq,hTwo,mul_le_mul_of_nonneg_left hp' hC,
        mul_nonneg (mul_nonneg hD hY) hp.le,
        show (C+2*D+D*Y)*x^a=C*x^a+(2*D)*x^a+(D*Y)*x^a by ring]
    · have hI := (prime_error_integral_linear (show (0:ℝ)≤1 by norm_num) hx.le).2
      have hL : |rieszError x|≤D*(x-1) := by
        rw [rieszError,abs_mul,abs_of_nonneg (inv_nonneg.mpr hx0.le)]
        exact (mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hx0.le)).trans_eq (by
          change x⁻¹*(D*x*(x-1))=D*(x-1)
          field_simp)
      have hSign := neg_abs_le (σ*rieszError x)
      rw [abs_mul,hσ',one_mul] at hSign
      have hCeil := mul_le_mul_of_nonneg_left (show x-1≤Y by linarith [lt_of_not_ge hLarge]) hD
      have hK : D*Y≤K := by dsimp [K]; linarith
      have hK0 : 0≤K := (mul_nonneg hD hY).trans hK
      linarith only [hSign,hL,hCeil,hK,le_mul_of_one_le_right hK0 hp1]
  rw [Real.rpow_neg hx0.le,←div_eq_mul_inv]
  linarith [(le_div_iff₀ hp).mpr hBound]

theorem rh_iff_one_sided_natural_riesz_power {σ : ℝ} (hσ : σ=1 ∨ σ= -1) :
    RiemannHypothesis ↔
      (∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0≤C ∧
        ∀ᶠ n : ℕ in atTop, -(C*(n:ℝ)^(1/2+ε))≤σ*rieszError (n:ℝ)) := by
  constructor
  · intro h ε hε
    obtain ⟨C,hC⟩ := (rh_iff_one_sided_riesz_bounds hσ).mp h ε hε
    refine ⟨max C 0,le_max_right _ _,?_⟩
    filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    have h1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hn0 : (0:ℝ)<n := by linarith
    have hPos : 0<(n:ℝ)^(1/2+ε) := Real.rpow_pos_of_pos hn0 _
    have h := hC n h1
    rw [Real.rpow_neg hn0.le,←div_eq_mul_inv] at h
    have hl : -C≤σ*rieszError (n:ℝ)/(n:ℝ)^(1/2+ε) := by linarith
    have he := (le_div_iff₀ hPos).mp hl
    have hCeil := mul_le_mul_of_nonneg_right (le_max_left C 0) hPos.le
    linarith only [he,hCeil]
  · intro h
    apply PoleCompensation.riemannHypothesis_of_right_zero_free
    intro s hs
    let ε := min ((s.re-1/2)/2) (1/4)
    have hε : 0<ε := lt_min (by linarith) (by norm_num)
    have hε1 : (1/2:ℝ)+ε<1 := by linarith [min_le_right ((s.re-1/2)/2) (1/4:ℝ)]
    have hs' : (1/2:ℝ)+ε<s.re := by linarith [min_le_left ((s.re-1/2)/2) (1/4:ℝ)]
    obtain ⟨C,hC,hN⟩ := h ε hε
    exact zero_free_of_one_sided_natural_riesz_power (by linarith) hε1 hσ hC hN s hs'

end RHConnections.RieszPrimeMellin
