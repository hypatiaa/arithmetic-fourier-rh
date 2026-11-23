import Verified

noncomputable section
open Filter
namespace RHConnections.RankContrast

theorem choose_strip_obstruction_parameters {lambda beta delta : ℝ}
    (hlambda : 0<lambda) (hbeta : 0<beta) (hbeta1 : beta<1)
    (_hdelta : 0<delta) (hdelta1 : delta≤1/8)
    (hz : 1-delta/(1+(5/2)*lambda)<beta) :
    ∃ delta' eta : ℝ, 0<delta' ∧ delta'<delta ∧ delta'<1/8 ∧
      0<eta ∧ eta<beta ∧ lambda*(1-beta+eta)<1/8 ∧
      1-delta'<beta-(5/2)*lambda*(1-beta+eta) := by
  let a := (1-beta)*(1+(5/2)*lambda)
  have ha : 0<a := by dsimp [a]; positivity
  have hal : a<delta := by
    apply (lt_div_iff₀ (by positivity : 0<1+(5/2)*lambda)).mp
    linarith
  let d := (a+delta)/2
  let e := min (beta/2) ((d-a)/(5*lambda+1))
  have hd : a<d := by dsimp [d]; linarith
  have hdL : d<delta := by dsimp [d]; linarith
  have hdU : d<1/8 := hdL.trans_le hdelta1
  have he : 0<e := lt_min (by positivity) (div_pos (sub_pos.mpr hd) (by positivity))
  have heB : e<beta := (min_le_left _ _).trans_lt (by linarith)
  have heL : (5*lambda+1)*e≤d-a := by
    have h := (le_div_iff₀ (by positivity : 0<5*lambda+1)).mp
      (show e≤(d-a)/(5*lambda+1) from min_le_right _ _)
    nlinarith only [h]
  have hm : (5/2)*lambda*e<d-a := by nlinarith only [heL,he,mul_pos hlambda he]
  have hgap : (1-beta)+(5/2)*lambda*(1-beta+e)<d := by dsimp [a] at hm; nlinarith only [hm]
  have hsmall : lambda*(1-beta+e)<1/8 := by
    nlinarith only [hgap,hdU,hbeta1,mul_pos hlambda (show 0<1-beta+e by linarith)]
  exact ⟨d,e,ha.trans hd,hdL,hdU,he,heB,hsmall,by linarith only [hgap]⟩

theorem not_frequently_domination_of_larger_power {a b C D : ℝ}
    (hab : b<a) (hC : 0<C) :
    ¬ ∃ᶠ q : ℝ in atTop, C*q^a ≤ D*q^b := by
  intro hfreq
  let K := max 1 (D/C)+1
  have hK : 0<K := by dsimp [K]; linarith [le_max_left (1:ℝ) (D/C)]
  have h₁ : ∀ᶠ q : ℝ in atTop, D/C<q^(a-b) := by
    filter_upwards [eventually_ge_atTop (K^(a-b)⁻¹)] with q hq
    have hh : (K^(a-b)⁻¹)^(a-b)=K := by
      rw [←Real.rpow_mul hK.le,inv_mul_cancel₀ (sub_ne_zero.mpr hab.ne'),Real.rpow_one]
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hK.le _) hq (sub_nonneg.mpr hab.le)
    rw [hh] at h
    exact (show D/C<K by dsimp [K]; linarith [le_max_right (1:ℝ) (D/C)]).trans_le h
  have h₂ : ∀ᶠ q : ℝ in atTop, ¬C*q^a≤D*q^b := by
    filter_upwards [h₁,eventually_gt_atTop (0:ℝ)] with q hq hq0
    intro hbad
    have hr : 0<q^b := Real.rpow_pos_of_pos hq0 _
    rw [Real.rpow_sub hq0,lt_div_iff₀ hr] at hq
    have hL := mul_lt_mul_of_pos_left hq hC
    have he : C*(D/C*q^b)=D*q^b := by field_simp
    rw [he] at hL
    exact (not_lt_of_ge hbad) hL
  exact hfreq h₂

end RHConnections.RankContrast
