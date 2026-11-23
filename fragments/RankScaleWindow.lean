import Verified

noncomputable section
namespace RHConnections.RankContrast

def nominalX (eta t : ℝ) : ℝ := (3*t/2)^((1-eta)⁻¹)

def nominalQ (eta t : ℝ) : ℝ := (nominalX eta t)^eta

def scaleX (eta t z : ℝ) : ℝ := nominalX eta t*Real.exp z

def scaleQ (eta t z : ℝ) : ℝ := (scaleX eta t z)^eta

theorem central_scale_relation {eta t : ℝ} (he : 0<eta) (he1 : eta<1) (ht : 0<t) :
    t = (2/3)*nominalQ eta t^((1-eta)/eta) := by
  have hb : 0<3*t/2 := by positivity
  have hx : 0<nominalX eta t := Real.rpow_pos_of_pos hb _
  rw [nominalQ,←Real.rpow_mul hx.le]
  have heq : eta*((1-eta)/eta)=1-eta := by field_simp
  rw [heq,nominalX,←Real.rpow_mul hb.le,inv_mul_cancel₀ (sub_ne_zero.mpr he1.ne'),
    Real.rpow_one]
  ring

theorem scaled_ratio_identity {eta t : ℝ} (he1 : eta<1) (ht : 0<t) (z : ℝ) :
    scaleX eta t z/scaleQ eta t z = (3*t/2)*Real.exp ((1-eta)*z) := by
  have hb : 0<3*t/2 := by positivity
  have hNom : 0<nominalX eta t := Real.rpow_pos_of_pos hb _
  have hx : 0<scaleX eta t z := by unfold scaleX; positivity
  unfold scaleQ
  have step : scaleX eta t z/(scaleX eta t z)^eta = (scaleX eta t z)^(1-eta) := by
    rw [Real.rpow_sub hx,Real.rpow_one]
  rw [step,scaleX,Real.mul_rpow hNom.le (Real.exp_pos _).le,nominalX,
    ←Real.rpow_mul hb.le,inv_mul_cancel₀ (sub_ne_zero.mpr he1.ne'),Real.rpow_one,
    Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  ring

theorem scaleQ_window {eta t z : ℝ} (he : 0<eta) (he1 : eta<1) (ht : 0<t)
    (hz : 0≤z) (hz1 : z≤Real.log (7/6)) :
    nominalQ eta t≤scaleQ eta t z ∧ scaleQ eta t z≤(7/6)*nominalQ eta t := by
  have hNom : 0<nominalX eta t := Real.rpow_pos_of_pos (by positivity) _
  unfold scaleQ scaleX
  rw [Real.mul_rpow hNom.le (Real.exp_pos _).le,
    Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  change nominalQ eta t≤nominalQ eta t*Real.exp (z*eta) ∧ _
  have hQ0 : 0≤nominalQ eta t := Real.rpow_nonneg hNom.le _
  constructor
  · exact le_mul_of_one_le_right hQ0 (Real.one_le_exp_iff.mpr (mul_nonneg hz he.le))
  · have h := Real.exp_le_exp.mpr
      (show z*eta≤Real.log (7/6) by nlinarith [mul_le_mul_of_nonneg_left he1.le hz])
    rw [Real.exp_log (by norm_num)] at h
    exact (mul_le_mul_of_nonneg_left h hQ0).trans_eq (by ring)

theorem scaleN_window {eta z : ℝ} {t : ℕ} (he : 0<eta) (he1 : eta<1)
    (ht : 4≤t) (hz : 0≤z) (hz1 : z≤Real.log (7/6)) :
    let n := scaleX eta (t:ℝ) z/scaleQ eta (t:ℝ) z
    let N := ⌊n⌋₊
    5*t≤4*N ∧ n∈Set.Icc (3*(t:ℝ)/2) (7*(t:ℝ)/4) := by
  have htR : (4:ℝ)≤t := by exact_mod_cast ht
  have htP : (0:ℝ)<t := by linarith
  rw [scaled_ratio_identity he1 htP]
  let n := (3*(t:ℝ)/2)*Real.exp ((1-eta)*z)
  have hnL : 3*(t:ℝ)/2≤n :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_exp_iff.mpr (by positivity))
  have hnU : n≤7*(t:ℝ)/4 := by
    have hx : (1-eta)*z≤Real.log (7/6) := by
      nlinarith [mul_nonneg he.le hz]
    have h := Real.exp_le_exp.mpr hx
    rw [Real.exp_log (by norm_num)] at h
    exact (mul_le_mul_of_nonneg_left h (by positivity : 0≤3*(t:ℝ)/2)).trans_eq (by ring)
  change 5*t≤4*⌊n⌋₊ ∧ _
  refine ⟨?_,hnL,hnU⟩
  have hfloor := Nat.lt_floor_add_one n
  have hNatR : 5*(t:ℝ)≤4*(⌊n⌋₊:ℝ) := by linarith only [hnL,hfloor,htR]
  exact_mod_cast hNatR

end RHConnections.RankContrast
