import Verified

noncomputable section
open Set
namespace RHConnections.RankContrast

theorem ceil_exp_phase_sample {A z : ℝ} (hA : 0<A) :
    let x := A*Real.exp z
    let n := ⌈x⌉₊
    ∃ z' : ℝ, x≤(n:ℝ) ∧ (n:ℝ)<x+1 ∧ A*Real.exp z'=(n:ℝ) ∧
      z≤z' ∧ z'≤z+1/x ∧
      ∀ eta : ℝ, 0≤eta → eta≤1 →
      1≤((n:ℝ)/x)^eta ∧ ((n:ℝ)/x)^eta≤1+1/x := by
  let x := A*Real.exp z
  let n := ⌈x⌉₊
  have hx : 0<x := mul_pos hA (Real.exp_pos _)
  have hn : x≤(n:ℝ) := Nat.le_ceil _
  have hn' : (n:ℝ)<x+1 := Nat.ceil_lt_add_one hx.le
  let r := (n:ℝ)/x
  have hr : 1≤r := (one_le_div hx).mpr hn
  have hr' : r≤1+1/x := by
    apply (div_le_iff₀ hx).mpr
    rw [add_mul,one_mul,div_mul_cancel₀ _ hx.ne']
    exact hn'.le
  have hp := zero_lt_one.trans_le hr
  refine ⟨z+Real.log r,hn,hn',?_,?_,?_,?_⟩
  · rw [Real.exp_add,←mul_assoc,Real.exp_log hp]
    change x*((n:ℝ)/x)=_
    field_simp
    rfl
  · linarith [Real.log_nonneg hr]
  · linarith [Real.log_le_sub_one_of_pos hp]
  · intro eta he he1
    refine ⟨Real.one_le_rpow hr he,?_⟩
    exact (Real.rpow_le_rpow_of_exponent_le hr he1).trans
      (by simpa using hr' : r^(1:ℝ)≤1+1/x)

theorem actual_window_integer_sample {eta t z W : ℝ} (ht : 0<t)
    (he : 0≤eta) (he1 : eta≤1) (hz : 0≤z)
    (hmargin : z+1/scaleX eta t z≤W) :
    ∃ n : ℕ, ∃ z'∈Icc 0 W, scaleX eta t z'=(n:ℝ) ∧
      scaleX eta t z≤(n:ℝ) ∧ (n:ℝ)<scaleX eta t z+1 ∧
      z≤z' ∧ z'-z≤1/scaleX eta t z ∧
      1≤scaleQ eta t z'/scaleQ eta t z ∧
      scaleQ eta t z'/scaleQ eta t z≤1+1/scaleX eta t z := by
  have hA : 0<nominalX eta t := by dsimp [nominalX]; positivity
  obtain ⟨z',hn,hn',heq,hz',hbound,hpow⟩ := ceil_exp_phase_sample (z := z) hA
  have hX : scaleX eta t z'= (⌈scaleX eta t z⌉₊:ℝ) := heq
  have hp : 0<scaleX eta t z := mul_pos hA (Real.exp_pos _)
  have hpp : 0<scaleX eta t z' := mul_pos hA (Real.exp_pos _)
  have hquot : scaleQ eta t z'/scaleQ eta t z =
      ((⌈scaleX eta t z⌉₊:ℝ)/scaleX eta t z)^eta := by
    dsimp only [scaleQ]
    rw [←Real.div_rpow hpp.le hp.le,hX]
  refine ⟨_,z',⟨hz.trans hz',hbound.trans hmargin⟩,hX,hn,hn',hz',?_,?_⟩
  · change z'≤z+1/scaleX eta t z at hbound
    linarith
  · rw [hquot]
    exact hpow eta he he1

end RHConnections.RankContrast
