import Verified
import FrozenWindowObstruction

noncomputable section
open Set
namespace RHConnections.PhaseWindow
open SpectralTail PrimeRightCut

abbrev RightZero := {r : NontrivialZetaZero // 7/8<r.val.re}

def rightValue (r : RightZero) : ℂ := r.val.val

def ZetaDensityPremise : Prop :=
  ∃ C : ℝ, 0≤C ∧ ∀ (T u : ℝ) (s : Finset NontrivialZetaZero),
    2≤T → 0≤u → u≤1/2 →
    (∀ r∈s, 1-u≤r.val.re ∧ |r.val.im|≤T) →
    (∑ r∈s,(analyticOrderNatAt riemannZeta r.val:ℝ))≤
      C*T^(3*u/(1+u))*(Real.log T)^5

theorem log_fifth_third_le_sqrt {T : ℝ} (hT : 1≤T) :
    T^(1/3:ℝ)*(Real.log T)^5 ≤ (120*6^5:ℝ)*Real.sqrt T := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hlog : 0≤Real.log T := Real.log_nonneg hT
  have hp := Real.pow_div_factorial_le_exp (Real.log T/6) (by positivity) 5
  have hpow : (Real.log T)^5 ≤ (120*6^5:ℝ)*T^(1/6:ℝ) := by
    rw [Real.rpow_def_of_pos hTp]
    norm_num at hp ⊢
    have hEq : (Real.log T/6)^5/(120:ℝ) = (Real.log T)^5/(120*6^5:ℝ) := by ring
    have he : Real.exp (Real.log T/6) = Real.exp (Real.log T*(1/6)) := by congr 1; ring
    rw [hEq,he] at hp
    linarith only [((div_le_iff₀ (by norm_num : (0:ℝ)<120*6^5)).mp hp)]
  calc
    _ ≤ T^(1/3:ℝ)*((120*6^5:ℝ)*T^(1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hTp.le _)
    _ = _ := by
      rw [mul_left_comm,←Real.rpow_add hTp,show (1/3:ℝ)+1/6=1/2 by norm_num,←Real.sqrt_eq_rpow]

theorem finite_right_zeros_of_bounded_height (T : ℝ) :
    {r : RightZero | |(rightValue r).im|≤T}.Finite := by
  have hH : 0<(max T 0)+2 := by linarith [le_max_right T (0:ℝ)]
  let v := 3*Real.log (max T 0+2)
  have hfinite := rightSet_finite v
  apply (hfinite.preimage (Set.injOn_of_injective Subtype.val_injective)).subset
  intro r hr
  have hri : |r.val.val.im|≤T := hr
  have hrre : 0<r.val.val.re := r.val.property.1.1
  have hrr : r.val.val.re<1 := r.val.property.1.2
  have hnorm := Complex.norm_le_abs_re_add_abs_im r.val.val
  rw [abs_of_pos hrre] at hnorm
  change 5/6<r.val.val.re ∧ ‖r.val.val‖≤Real.exp (v/3)
  refine ⟨by linarith [r.property],?_⟩
  rw [show v/3=Real.log (max T 0+2) by dsimp [v]; ring,Real.exp_log hH]
  linarith only [hnorm,hri,hrr,le_max_left T (0:ℝ)]

theorem shifted_right_zero_sqrt_count (hIngham : ZetaDensityPremise)
    (rho₀ : ℂ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (T : ℝ) (s : Finset RightZero), 1≤T →
      (∀ r∈s, |(rightValue r-rho₀).im|≤T) → (s.card:ℝ)≤C*Real.sqrt T := by
  classical
  obtain ⟨C,hC,hcount⟩ := hIngham
  let A := 2+|rho₀.im|
  have hA : 2≤A := by dsimp [A]; linarith [abs_nonneg rho₀.im]
  refine ⟨C*(120*6^5)*Real.sqrt A,by positivity,?_⟩
  intro T s hT hs
  let e : RightZero ↪ NontrivialZetaZero := ⟨Subtype.val,Subtype.val_injective⟩
  have hbig : 2≤A*T := hA.trans (le_mul_of_one_le_right (by linarith) hT)
  have hdom := hcount (A*T) (1/8) (s.map e) hbig (by norm_num) (by norm_num) (by
    intro r hr
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hr
    have hrB : 1-(1/8:ℝ)≤(rightValue w).re := by
      change 1-(1/8:ℝ)≤w.val.val.re
      linarith [w.property]
    refine ⟨hrB,?_⟩
    have h := hs w hw
    rw [Complex.sub_im] at h
    have htri := abs_add_le ((rightValue w).im-rho₀.im) rho₀.im
    rw [sub_add_cancel] at htri
    change |(rightValue w).im|≤A*T
    dsimp [A]
    nlinarith only [htri,h,mul_le_mul_of_nonneg_right hT (abs_nonneg rho₀.im),hT])
  simp only [Finset.sum_map,e,Function.Embedding.coeFn_mk] at hdom
  have hm (r : RightZero) : (1:ℝ) ≤ analyticOrderNatAt riemannZeta r.val.val := by
    obtain ⟨ha,hord⟩ := zeta_nontrivial_zero_finite_order r.val
    exact_mod_cast (Nat.succ_le_of_lt (zero_order_positive r.val.property.2 ha hord))
  have hcard : (s.card:ℝ)≤∑ r∈s,(analyticOrderNatAt riemannZeta r.val.val:ℝ) := by
    have hh : (s.card:ℝ)=∑ _r∈s,(1:ℝ) := by simp
    rw [hh]
    exact Finset.sum_le_sum (fun r _ => hm r)
  have hex : 3*(1/8:ℝ)/(1+1/8)=1/3 := by norm_num
  rw [hex] at hdom
  calc
    _ ≤ _ := hcard.trans hdom
    _ = C*((A*T)^(1/3:ℝ)*(Real.log (A*T))^5) := by ring
    _ ≤ C*((120*6^5)*Real.sqrt (A*T)) :=
      mul_le_mul_of_nonneg_left (log_fifth_third_le_sqrt (by linarith)) hC
    _ = _ := by rw [Real.sqrt_mul (by linarith : 0≤A)]; ring

end RHConnections.PhaseWindow
