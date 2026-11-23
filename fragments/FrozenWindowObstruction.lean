import Verified
import ContinuumModeExpansion
import PhaseDensityTransfer
import RankContrastTransfer

noncomputable section
open Set
namespace RHConnections.RankContrast
open LocalModeContrast PhaseWindow

variable {ι κ : Type*}

theorem frozen_window_isolates_zero_contrast
    (rho₀ : ℂ) (hrho₀ : rho₀≠0) (hrho₁ : rho₀≠1) (rho : κ → ℂ)
    (hsep : ∀ j,rho j≠rho₀)
    (hfinite : {j | |(rho j-rho₀).im|<2}.Finite)
    {C W : ℝ} (hC : 0≤C) (hW : 0<W)
    (hcount : ∀ (T : ℝ) (s : Finset κ), 1≤T →
      (∀ j∈s, |(rho j-rho₀).im|≤T) → (s.card:ℝ)≤C*Real.sqrt T) :
    ∃ R D : ℝ, 0<R ∧ 0≤D ∧ ∀ (A B : Finset ι) (hA : A.Nonempty) (hB : B.Nonempty)
      (a b : ι → ℝ) (gap L₀ m₀ : ℝ) (hg : 0<gap) (hL : 0<L₀) (hm : 0≤m₀)
      (roots : Finset κ) (mult : κ → ℂ) (hr : ∀ j∈roots, rho j≠0) (E : ℝ),
      (∀ i, i∈A ∨ i∈B →
        (0<a i ∧ a i<b i) ∧ a i∈Ioo (1-R) (1+R) ∧ b i∈Ioo (1-R) (1+R)) →
      (∀ i∈A,∀ j∈B,gap≤a i-a j ∧ gap≤b i-b j) →
      (∀ z∈Icc 0 W,
        let L := L₀*Real.exp z
        let row (i : ι) := (m₀:ℂ)*
            (zeroPrimitive rho₀ (L*b i)-zeroPrimitive rho₀ (L*a i))+
          ∑ j∈roots,mult j*(zeroPrimitive (rho j) (L*b i)-zeroPrimitive (rho j) (L*a i))
        ‖contrast A B (fun i => b i-a i) row‖≤E) →
      m₀*L₀^rho₀.re*gap*‖rho₀-1‖/2 ≤ D*E := by
  obtain ⟨R,hR,hlower⟩ := mode_contrast_lower_near_one (ι := ι) rho₀ hrho₁
  obtain ⟨K,hK,hIso⟩ := uniform_window_isolation_of_sqrt_count
    (fun j => rho j-rho₀) (fun j => sub_ne_zero.mpr (hsep j)) hfinite C hC hcount hW
  let D := K*Real.exp (|rho₀.re| * W)
  refine ⟨R,D,hR,by dsimp [D]; positivity,?_⟩
  intro A B hA hB a b gap L₀ m₀ hg hL hm roots mult hr E hab hgap hRow
  let s (j : κ) := mult j*Complex.exp (rho j*(Real.log L₀:ℂ))*modeContrast A B a b (rho j)
  let base : ℂ := (m₀:ℂ)*Complex.exp (rho₀*(Real.log L₀:ℂ))*modeContrast A B a b rho₀
  have hExp (z : ℝ) : contrast A B (fun i => b i-a i) (fun i =>
      (m₀:ℂ)*(zeroPrimitive rho₀ (L₀*Real.exp z*b i)-zeroPrimitive rho₀ (L₀*Real.exp z*a i))+
      ∑ j∈roots,mult j*(zeroPrimitive (rho j) (L₀*Real.exp z*b i)-zeroPrimitive (rho j) (L₀*Real.exp z*a i))) =
      base*Complex.exp (rho₀*(z:ℂ)) + ∑ j∈roots,s j*Complex.exp (rho j*(z:ℂ)) := by
    rw [contrast_add]
    have ht := continuum_zero_mode_expansion A B ({()} : Finset Unit) a b
      (fun i hi => (hab i hi).1) (fun _ => rho₀) (fun _ => (m₀:ℂ)) (fun _ _ => hrho₀) hL z
    have ho := continuum_zero_mode_expansion A B roots a b
      (fun i hi => (hab i hi).1) rho mult hr hL z
    dsimp only at ht ho
    simp only [Finset.sum_singleton] at ht
    exact congrArg₂ (·+·) ht ho
  have he (z : ℝ) :
      base+∑ j∈roots,s j*Complex.exp ((rho j-rho₀)*(z:ℂ)) =
      Complex.exp (-(rho₀*(z:ℂ)))*
        (base*Complex.exp (rho₀*(z:ℂ))+∑ j∈roots,s j*Complex.exp (rho j*(z:ℂ))) := by
    rw [mul_add,Finset.mul_sum]
    congr 1
    · rw [mul_left_comm,←Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one]
    · apply Finset.sum_congr rfl
      intro j _
      rw [sub_mul,sub_eq_add_neg,mul_left_comm,←Complex.exp_add]
      congr 2
      ring
  have hNormalized (z : ℝ) (hz : z∈Icc 0 W) :
      ‖base+∑ j∈roots,s j*Complex.exp ((rho j-rho₀)*(z:ℂ))‖≤Real.exp (|rho₀.re| * W)*E := by
    rw [he,norm_mul,Complex.norm_exp,Complex.neg_re,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    have hExpLe : Real.exp (-(rho₀.re*z))≤Real.exp (|rho₀.re| * W) := by
      apply Real.exp_le_exp.mpr
      rw [←neg_mul]
      exact (mul_le_mul_of_nonneg_right (neg_le_abs _) hz.1).trans
        (mul_le_mul_of_nonneg_left hz.2 (abs_nonneg _))
    have h := hRow z hz
    dsimp only at h
    rw [hExp z] at h
    exact mul_le_mul hExpLe h (norm_nonneg _) (Real.exp_pos _).le
  have hBase := hIso roots s base _ hNormalized
  have hMode := hlower A B hA hB a b hg (fun i hi => (hab i hi).2) hgap
  have hNorm : ‖base‖=m₀*L₀^rho₀.re*‖modeContrast A B a b rho₀‖ := by
    dsimp only [base]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm,Complex.norm_exp,
      Real.rpow_def_of_pos hL]
    simp [Complex.mul_re,mul_comm,mul_assoc]
  rw [hNorm] at hBase
  calc
    _ = (m₀*L₀^rho₀.re)*(gap*‖rho₀-1‖/2) := by ring
    _ ≤ (m₀*L₀^rho₀.re)*‖modeContrast A B a b rho₀‖ :=
      mul_le_mul_of_nonneg_left hMode (by positivity)
    _ ≤ _ := hBase.trans_eq (by dsimp [D]; ring)

end RHConnections.RankContrast
