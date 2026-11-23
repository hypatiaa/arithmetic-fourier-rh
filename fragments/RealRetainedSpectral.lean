import Verified
import ZetaConjugateMultiplicity

noncomputable section
open MeasureTheory
namespace RHConnections.SharpRadialTail
open SpectralTail SmoothedPrimeLimit
open ParametricSharpRightEndpoint (width parametricShellRight)
open SmoothedPrimeSandwichUniform

theorem compact_zero_term_conjugate {f : ℝ → ℂ}
    (hf : ∀ x, (starRingEnd ℂ) (f x)=f x) (r : NontrivialZetaZero) :
    (starRingEnd ℂ) (compactZeroTerm f r)=compactZeroTerm f (conjugateZeroEquiv r) := by
  unfold compactZeroTerm
  rw [map_mul,map_natCast,conjugateZeroEquiv_order,←integral_conj]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,map_mul,←Complex.exp_conj,map_sub,
      Complex.conj_ofReal,conjugateZeroEquiv_val,hf])

theorem scaled_real_test_conjugate {f : ℝ → ℂ}
    (hf : ∀ x, (starRingEnd ℂ) (f x)=f x) (T x : ℝ) :
    (starRingEnd ℂ) (scaleTest T f x)=scaleTest T f x := by
  simp only [scaleTest,show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,map_mul,map_sub,
    ←Complex.exp_conj,Complex.conj_ofReal,hf]

theorem paramRightSet_conjugate_mem_iff (a T : ℝ) (r : NontrivialZetaZero) :
    conjugateZeroEquiv r∈paramRightSet a T ↔ r∈paramRightSet a T := by
  change (a<(conjugateZeroEquiv r).val.re ∧ ‖(conjugateZeroEquiv r).val‖≤Real.exp _) ↔
    a<r.val.re ∧ ‖r.val‖≤Real.exp _
  simp only [conjugateZeroEquiv_val,Complex.conj_re,Complex.norm_conj]

theorem paramRightSum_conjugate (a T : ℝ) {f : ℝ → ℂ}
    (hf : ∀ x, (starRingEnd ℂ) (f x)=f x) :
    (starRingEnd ℂ) (paramRightSum a T f)=paramRightSum a T f := by
  let F := fun r : NontrivialZetaZero => compactZeroTerm (scaleTest T f) r
  let S := paramRightSet a T
  let G := S.indicator F
  change (starRingEnd ℂ) (∑' r,G r)=∑' r,G r
  rw [Complex.conj_tsum]
  calc
    _ = ∑' r,G (conjugateZeroEquiv r) := by
      apply tsum_congr
      intro r
      have hv := paramRightSet_conjugate_mem_iff a T r
      by_cases hr : r∈S
      · have hr' : conjugateZeroEquiv r∈S := hv.mpr hr
        dsimp [G]
        rw [Set.indicator_of_mem hr,Set.indicator_of_mem hr']
        exact compact_zero_term_conjugate (scaled_real_test_conjugate hf T) r
      · have hr' : conjugateZeroEquiv r∉S := fun h => hr (hv.mp h)
        dsimp [G]
        rw [Set.indicator_of_notMem hr,Set.indicator_of_notMem hr',_root_.map_zero]
    _ = _ := conjugateZeroEquiv.tsum_eq G

theorem parametric_shell_right_real (a T p q h : ℝ) :
    (parametricShellRight a T p q h).im=0 :=
  Complex.conj_eq_iff_im.mp (paramRightSum_conjugate a T (fun _ => Complex.conj_ofReal _))

end RHConnections.SharpRadialTail
