import Verified

noncomputable section
namespace RHConnections.RankContrast

theorem bounded_complex_center {ι : Type*} [Fintype ι] (w len : ι → ℝ) (v : ι → ℂ)
    (hw : ∀ i,0≤w i) (hl : ∀ i,0≤len i) {D : ℝ} (hD : 0≤D)
    (hv : ∀ i, ‖v i‖≤D*len i) (c : ℂ) :
    ∃ c' : ℂ, ‖c'‖≤2*D ∧
      (∑ i,w i*‖v i-c'*(len i:ℂ)‖^2)≤∑ i,w i*‖v i-c*(len i:ℂ)‖^2 := by
  let A := ∑ i,w i*(len i)^2
  have hA : 0≤A := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  by_cases ha : A=0
  · refine ⟨0,by simpa using (show 0≤2*D by linarith),?_⟩
    have hw0 (i : ι) : w i*(len i)^2=0 := by
      have h := Finset.single_le_sum (f := fun i => w i*(len i)^2)
        (fun j _ => mul_nonneg (hw j) (sq_nonneg _)) (Finset.mem_univ i)
      exact le_antisymm (h.trans ha.le) (mul_nonneg (hw i) (sq_nonneg _))
    apply Finset.sum_le_sum
    intro i _
    rcases mul_eq_zero.mp (hw0 i) with hz | hz
    · simp [hz]
    · have hzero : len i=0 := by
        by_contra hn
        exact pow_ne_zero _ hn hz
      simp [hzero]
  · have hApos : 0<A := lt_of_le_of_ne hA (Ne.symm ha)
    let vr (i : ι) := (v i).re
    let vi (i : ι) := (v i).im
    let cr := fittedConstant w len vr
    let ci := fittedConstant w len vi
    let c' : ℂ := ⟨cr,ci⟩
    have hr : |cr|≤D := fitted_constant_bound w len vr hw hl hApos
      (fun i => (Complex.abs_re_le_norm _).trans (hv i))
    have hi : |ci|≤D := fitted_constant_bound w len vi hw hl hApos
      (fun i => (Complex.abs_im_le_norm _).trans (hv i))
    refine ⟨c',(Complex.norm_le_abs_re_add_abs_im _).trans (by change |cr|+|ci|≤_; linarith),?_⟩
    have he (u : ℂ) : (∑ i,w i*‖v i-u*(len i:ℂ)‖^2) =
        centeredEnergy w len vr u.re+centeredEnergy w len vi u.im := by
      unfold centeredEnergy
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,zero_add,
        vr,vi]
      ring
    rw [he c',he c]
    exact add_le_add (fitted_constant_minimizes w len vr c.re hApos)
      (fitted_constant_minimizes w len vi c.im hApos)

theorem bounded_complex_center_finset {ι : Type*} (s : Finset ι) (w len : ι → ℝ)
    (v : ι → ℂ) (hw : ∀ i∈s,0≤w i) (hl : ∀ i∈s,0≤len i) {D : ℝ} (hD : 0≤D)
    (hv : ∀ i∈s, ‖v i‖≤D*len i) (c : ℂ) :
    ∃ c' : ℂ, ‖c'‖≤2*D ∧
      (∑ i∈s,w i*‖v i-c'*(len i:ℂ)‖^2)≤∑ i∈s,w i*‖v i-c*(len i:ℂ)‖^2 := by
  classical
  obtain ⟨c',hc',h⟩ := bounded_complex_center
    (fun i : s => w i) (fun i : s => len i) (fun i : s => v i)
    (fun i => hw i i.property) (fun i => hl i i.property) hD (fun i => hv i i.property) c
  refine ⟨c',hc',?_⟩
  rw [Finset.sum_subtype s (fun _ => Iff.rfl) (fun i => w i*‖v i-c'*(len i:ℂ)‖^2),
    Finset.sum_subtype s (fun _ => Iff.rfl) (fun i => w i*‖v i-c*(len i:ℂ)‖^2)]
  exact h

end RHConnections.RankContrast
