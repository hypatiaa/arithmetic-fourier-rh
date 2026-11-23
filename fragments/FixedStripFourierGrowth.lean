import Verified
import FixedStripReciprocal

noncomputable section
open Filter Asymptotics
namespace RHConnections.MertensCriterion
open PerronRamp ArithmeticFourierInversion ZetaDiskLog PerronGrowthTransfer

theorem smoothed_mertens_bound_of_strip {a b u : ℝ}
    (hStrip : ∀ s : ℂ, a<s.re → riemannZeta s≠0)
    (ha : 1/2≤a) (hb : a<b) (hb1 : b<1) (hu : 0<u) (hu1 : u<1) :
    ∃ C : ℝ, 0≤C ∧ ∀ (X h : ℝ), 1≤X → 0<h → h≤1 →
      ‖smoothedMertens h X‖≤C*X^b*h^(-u) := by
  obtain ⟨C,hC,hRecip⟩ := zetaReciprocal_subpower_of_strip hStrip ha hb hb1 hu
  let D := C*(10:ℝ)^u
  have hD : 0≤D := by dsimp [D]; positivity
  have hAnalytic : AnalyticOnNhd ℂ zetaReciprocal {s : ℂ | s.re∈Set.Icc b 2} :=
    fun s hs => zetaReciprocal_analytic_of_strip hStrip s (hb.trans_le hs.1)
  have hGrowth (s : ℂ) (hs : s.re∈Set.Icc b 2) : ‖zetaReciprocal s‖≤D*(1+|s.im|)^u := by
    have hP := hRecip s hs.1 (hs.2.trans (by norm_num))
    have hSize : (|s.im|+10)^u≤(10:ℝ)^u*(1+|s.im|)^u := by
      rw [←Real.mul_rpow (by norm_num : (0:ℝ)≤10) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) hu.le
    exact (hP.trans (mul_le_mul_of_nonneg_left hSize hC)).trans_eq (by dsimp [D]; ring)
  obtain ⟨A,hA,h⟩ := euler_integral_bound_of_strip_growth (by linarith : 0<b)
    (by linarith : b≤2) hu hu1 hD hAnalytic hGrowth
  refine ⟨A,hA,?_⟩
  intro X h' hX hh hh1
  rw [smoothedMertens_eq_euler_integral hh (by norm_num : (1:ℝ)<2) (by linarith : 0<X)]
  exact h X h' hX hh hh1

theorem mertens_power_bound_of_strip {a ε : ℝ}
    (hStrip : ∀ s : ℂ, a<s.re → riemannZeta s≠0)
    (ha : 1/2≤a) (ha1 : a<1) (hε : 0<ε) :
    ∃ C : ℝ, 0≤C ∧ ∀ X : ℝ, 1≤X → ‖mertens X‖≤C*X^(a+ε) := by
  let d := min (ε/2) ((1-a)/2)
  let b := a+d
  have hd : 0<d := lt_min (by positivity) (by linarith)
  have hdε : d≤ε/2 := min_le_left _ _
  have hd1 : d≤(1-a)/2 := min_le_right _ _
  have hb : a<b := by dsimp [b]; linarith
  have hb1 : b<1 := by dsimp [b]; linarith
  obtain ⟨C,hC,hSmooth⟩ := smoothed_mertens_bound_of_strip hStrip ha hb hb1 hd (by linarith)
  refine ⟨C+6,by positivity,?_⟩
  intro X hX
  have hX0 := zero_lt_one.trans_le hX
  let h := X⁻¹
  have hp : 0<h := inv_pos.mpr hX0
  have h1 : h≤1 := by dsimp [h]; exact inv_le_one_of_one_le₀ hX
  have hS := hSmooth X h hX hp h1
  have hdexp : h^(-d)=X^d := by
    dsimp [h]
    rw [Real.inv_rpow hX0.le,Real.rpow_neg hX0.le,inv_inv]
  rw [hdexp,mul_assoc,←Real.rpow_add hX0] at hS
  have hS' := hS.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX (show b+d≤a+ε by dsimp [b]; linarith)) hC)
  have hE := smoothedMertens_error hX hp h1
  rw [show X*h=1 from mul_inv_cancel₀ hX0.ne'] at hE
  have hPow : 1≤X^(a+ε) := Real.one_le_rpow hX (by linarith)
  calc
    _ = ‖smoothedMertens h X-(smoothedMertens h X-mertens X)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖smoothedMertens h X‖+‖smoothedMertens h X-mertens X‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

theorem natural_mertens_bounds_of_strip {a : ℝ}
    (hStrip : ∀ s : ℂ, a<s.re → riemannZeta s≠0) (ha : 1/2≤a) (ha1 : a<1) :
    ∀ ε : ℝ, 0<ε → NaturalPowerBound M (a+ε) := by
  intro ε hε
  obtain ⟨C,hC,h⟩ := mertens_power_bound_of_strip hStrip ha ha1 hε
  refine ⟨C,hC,fun n hn => ?_⟩
  simpa [mertens_eq_natural_M,Complex.norm_real,Real.norm_eq_abs] using
    h (n:ℝ) (by exact_mod_cast hn)

theorem zero_free_of_natural_mertens_power {b : ℝ} (hb : 0≤b) (hb1 : b<1)
    (hM : NaturalPowerBound M b) :
    ∀ s : ℂ, b<s.re → riemannZeta s≠0 := by
  obtain ⟨C,hC,hM⟩ := hM
  apply zero_free_of_mertens_fixed_power hb1
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have h0 : 0≤x := zero_le_one.trans hx
  have hfloor : 1≤⌊x⌋₊ := (Nat.le_floor_iff h0).mpr (by simpa using hx)
  rw [mertens_eq_natural_M,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg h0 _)]
  exact (hM _ hfloor).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le h0) hb) hC)

end RHConnections.MertensCriterion

namespace RHConnections.ArithmeticFourierInversion
open MertensCriterion

theorem fixed_strip_iff_fourier_scalar_power (B : ℕ) {a : ℝ} (ha : 1/2≤a) (ha1 : a<1) :
    (∀ s : ℂ, a<s.re → riemannZeta s≠0) ↔
      (∀ ε : ℝ, 0<ε → NaturalPowerBound (S B) (a+ε)) := by
  constructor
  · intro h ε hε
    exact (M_power_bound_iff_S B (by linarith : 0<a+ε)).mp (natural_mertens_bounds_of_strip h ha ha1 ε hε)
  · intro h s hs
    let ε := min ((s.re-a)/2) ((1-a)/2)
    have hε : 0<ε := lt_min (by linarith) (by linarith)
    have hb0 : 0≤a+ε := by linarith
    have hb1 : a+ε<1 := by linarith [min_le_right ((s.re-a)/2) ((1-a)/2)]
    have hbs : a+ε<s.re := by linarith [min_le_left ((s.re-a)/2) ((1-a)/2)]
    exact zero_free_of_natural_mertens_power hb0 hb1
      ((M_power_bound_iff_S B (by linarith : 0<a+ε)).mpr (h ε hε)) s hbs

theorem fixed_strip_iff_fourier_energy_power (B : ℕ) {a : ℝ} (ha : 1/2≤a) (ha1 : a<1) :
    (∀ s : ℂ, a<s.re → riemannZeta s≠0) ↔
      (∀ ε : ℝ, 0<ε → NaturalPowerBound (CoherentEnergyBounds.energy (S B) B) (2*a+ε)) := by
  rw [fixed_strip_iff_fourier_scalar_power B ha ha1]
  constructor
  · intro h ε hε
    obtain ⟨A,hA,hA'⟩ := h (ε/2) (by linarith)
    refine ⟨A^2*CoherentEnergyBounds.pSeries (2*(a+ε/2)),by
      exact mul_nonneg (sq_nonneg _) (show 0≤CoherentEnergyBounds.pSeries _ from
        tsum_nonneg (fun n => by positivity)),?_⟩
    intro n hn
    have hBound := CoherentEnergyBounds.energy_upper (S B) B n hA (by linarith : 1/2<a+ε/2) hA'
    have hNonneg := (sq_nonneg _).trans (CoherentEnergyBounds.scalar_sq_le_energy (S B) B n hn)
    rwa [abs_of_nonneg hNonneg,show 2*a+ε=2*(a+ε/2) by ring]
  · intro h ε hε
    obtain ⟨A,hA,hA'⟩ := h (2*ε) (by linarith)
    refine ⟨Real.sqrt A,Real.sqrt_nonneg _,?_⟩
    intro n hn
    have h := (CoherentEnergyBounds.scalar_sq_le_energy (S B) B n hn).trans
      ((le_abs_self _).trans (hA' n hn))
    have he : (Real.sqrt A*(n:ℝ)^(a+ε))^2 = A*(n:ℝ)^(2*a+2*ε) := by
      rw [mul_pow,Real.sq_sqrt hA]
      congr 1
      calc
        _ = ((n:ℝ)^(a+ε))^(2:ℝ) := by norm_num
        _ = _ := by rw [←Real.rpow_mul (Nat.cast_nonneg n)]; congr 1; ring
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs,he]
    exact h

end RHConnections.ArithmeticFourierInversion
