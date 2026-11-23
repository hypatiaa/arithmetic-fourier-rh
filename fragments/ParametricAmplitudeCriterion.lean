import Verified
import ParametricSharpDyadic
import RetainedAmplitudeCriterion
import FixedStripChebyshev

noncomputable section
open Filter Asymptotics Set
namespace RHConnections.ParametricSharpRightEndpoint
open RHConnections.SharpRadialTail (paramRightSet paramRightSum)
open RHConnections.SpectralTail RHConnections.DyadicEndpoint RHConnections.RankContrast

def retainedDyadicAmplitude (a X : ℝ) : ℝ :=
  (X/Real.exp 1)*retained a (Real.log X-1)

theorem paramRightSum_eq_zero_of_strip {a : ℝ} (h : ∀ s : ℂ, a<s.re → riemannZeta s≠0)
    (T : ℝ) (f : ℝ → ℂ) : paramRightSum a T f=0 := by
  have he : paramRightSet a T=∅ := by
    ext r
    constructor
    · intro hr
      exact (h r.val hr.1 r.property.2).elim
    · intro hr
      exact hr.elim
  simp [paramRightSum,he]

theorem retained_eq_zero_of_strip {a : ℝ} (h : ∀ s : ℂ, a<s.re → riemannZeta s≠0)
    (T : ℝ) : retained a T=0 := by
  simp only [retained,parametricShellRight,paramRightSum_eq_zero_of_strip h,norm_zero,max_self]

theorem sharp_dyadic_bound_of_strip {a : ℝ}
    (ha : 1/2≤a) (ha1 : a<1) (h : ∀ s : ℂ, a<s.re → riemannZeta s≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ X : ℝ, Real.exp 2≤X →
      ‖dyadicChebyshevError X‖≤C*X^a*(1+Real.log X)^2 := by
  obtain ⟨C,hC,hX⟩ := parametric_sharp_dyadic_X ha ha1
  refine ⟨C,hC,?_⟩
  intro X hx
  have h' := hX X hx
  rwa [retained_eq_zero_of_strip h,mul_zero,zero_add,←SharpRightEndpoint.norm_dyadic_chebyshev_error] at h'

theorem parametric_dyadic_remainder_order (a : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℝ in atTop, X^a*(1+Real.log X)^2≤4*X^(a+ε) := by
  filter_upwards [eventually_log_rpow_absorbed 2 hε,
    eventually_ge_atTop (Real.exp 1)] with X hx h1
  have hXp := (Real.exp_pos 1).trans_le h1
  have hlog : 1≤Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h
  have hp : (Real.log X)^(2:ℕ)≤X^ε := by
    change (Real.log X)^(2:ℝ)≤X^ε at hx
    simpa only [Real.rpow_two] using hx
  have hd : (1+Real.log X)^2≤4*X^ε := by
    calc
      _ ≤ (2*Real.log X)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      _ = 4*(Real.log X)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)
  exact (mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hXp.le _)).trans_eq (by
    rw [Real.rpow_add hXp]; ring)

theorem fixed_strip_iff_parametric_amplitude {a : ℝ} (ha : 1/2≤a) (ha1 : a<1) :
    (∀ s : ℂ, a<s.re → riemannZeta s≠0) ↔
      (∀ ε : ℝ, 0<ε → retainedDyadicAmplitude a =O[atTop] (fun X : ℝ => X^(a+ε))) := by
  constructor
  · intro h ε hε
    apply IsBigO.of_bound 0
    exact Eventually.of_forall (fun X => by simp [retainedDyadicAmplitude,retained_eq_zero_of_strip h])
  · intro h
    apply (fixed_strip_iff_dyadic_chebyshev_power ha ha1).mpr
    intro ε hε
    obtain ⟨C,hC,hC'⟩ := (h ε hε).exists_nonneg
    obtain ⟨D,hD,hR⟩ := parametric_sharp_dyadic_X ha ha1
    apply IsBigO.of_bound (C+4*D)
    filter_upwards [parametric_dyadic_remainder_order a hε, eventually_ge_atTop (Real.exp 2),hC'.bound] with
      X hErr hX hAmpX
    have hX0 := (Real.exp_pos 2).trans_le hX
    rw [SharpRightEndpoint.norm_dyadic_chebyshev_error]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)] at hAmpX ⊢
    refine (hR X hX).trans ?_
    have h' : retainedDyadicAmplitude a X≤C*X^(a+ε) :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hAmpX)
    have hRem := mul_le_mul_of_nonneg_left hErr hD
    change retainedDyadicAmplitude a X+D*X^a*(1+Real.log X)^2≤_
    nlinarith only [h',hRem]

theorem rh_iff_critical_retained_amplitude :
    RiemannHypothesis ↔
      (∀ ε : ℝ, 0<ε → retainedDyadicAmplitude (1/2) =O[atTop] (fun X : ℝ => X^(1/2+ε))) := by
  exact ⟨fun h => (fixed_strip_iff_parametric_amplitude le_rfl (by norm_num)).mp
    (ZetaDiskLog.right_zero_free_of_RH h),
    fun h => PoleCompensation.riemannHypothesis_of_right_zero_free
      ((fixed_strip_iff_parametric_amplitude le_rfl (by norm_num)).mpr h)⟩

end RHConnections.ParametricSharpRightEndpoint
