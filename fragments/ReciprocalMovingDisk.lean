import ReciprocalEulerDisk
import ReciprocalLocalComparison
open Metric Set
noncomputable section
namespace RHConnections.ReciprocalLocalComparison
open SpectralTail ZetaZeroFreeRegion ZetaDiskLog ZetaAbelGrowth PoleCompensation
theorem exists_nonzero_log_region :
    ∃ C : ℝ, 0 < C ∧ C ≤ 1/2 ∧ ∀ s : ℂ, 1-C/heightFactor s.im < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨C,hC,hCa,hb⟩ := all_height_logarithmic_exclusion
  refine ⟨C,hC,hCa,?_⟩
  intro s hs hz
  have hs1 : s.re < 1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hz)
  have hh := (div_le_self hC.le (heightFactor_one_le s.im)).trans hCa
  let rho : NontrivialZetaZero := ⟨s,⟨by linarith,hs1⟩,hz⟩
  exact (not_le_of_gt hs) (hb rho).2

theorem height_near {t u : ℝ} (h : |u-t| ≤ 1) : heightFactor u ≤ 2*heightFactor t := by
  have hU : |u| ≤ |t|+1 := by
    calc
      |u| = |u-t+t| := by ring_nf
      _ ≤ |u-t|+|t| := abs_add_le _ _
      _ ≤ _ := by linarith
  have h1 : 0 < 3+2*|u| := by positivity
  have h2 : 0 < 3+2*|t| := by positivity
  have hcmp : 3+2*|u| ≤ 2*(3+2*|t|) := by linarith [abs_nonneg t]
  have hh := Real.log_le_log h1 hcmp
  rw [Real.log_mul (by norm_num) h2.ne'] at hh
  have hh' := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  unfold heightFactor
  linarith [Real.log_nonneg (show 1 ≤ 3+2*|t| by linarith [abs_nonneg t])]

theorem disk_data {C a t : ℝ} (hC : 0<C) (hCa : C≤1/2) (ha : 0<a) (haC : a≤C)
    (hn : ∀ s : ℂ, 1-C/heightFactor s.im < s.re → riemannZeta s ≠ 0) (ht : 5≤|t|) :
    let H := heightFactor t
    let c : ℂ := ⟨1+a/H,t⟩
    let R := C/(4*H)
    ∀ w ∈ ball c R, riemannZeta w ≠ 0 ∧ w ≠ 1 ∧ ‖riemannZeta w‖ ≤ Real.exp (2*H) := by
  dsimp only
  intro w hw
  let H := heightFactor t
  let c : ℂ := ⟨1+a/H,t⟩
  let R := C/(4*H)
  have hH : 1≤H := heightFactor_one_le _
  have hHp : 0<H := by linarith
  have hR : 0<R := by positivity
  have hRsmall : R≤1/2 := by
    apply (div_le_iff₀ (by positivity : 0<4*H)).mpr
    linarith
  have hA : a/H≤1/2 := (div_le_self ha.le hH).trans (haC.trans hCa)
  have hD : ‖w-c‖ < R := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hw
  have hI : |w.im-t| < R := (Complex.abs_im_le_norm (w-c)).trans_lt hD
  have hX : |w.re-(1+a/H)| < R := (Complex.abs_re_le_norm (w-c)).trans_lt hD
  have hJ : heightFactor w.im ≤ 2*H := height_near (by linarith)
  have hpJ : 0 < heightFactor w.im := zero_lt_one.trans_le (heightFactor_one_le _)
  have hx := (abs_lt.mp hX)
  have hi := (abs_lt.mp hI)
  have hratio : R ≤ C/heightFactor w.im := by
    exact div_le_div_of_nonneg_left hC.le hpJ (by linarith)
  have hwz := hn w (by linarith [div_pos ha hHp])
  have him : |t| ≤ 1+|w.im| := by
    calc
      |t| = |-(w.im-t)+w.im| := by ring_nf
      _ ≤ |-(w.im-t)|+|w.im| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg]; linarith
  have him' : |w.im| ≤ 1+|t| := by
    calc
      |w.im| = |w.im-t+t| := by ring_nf
      _ ≤ |w.im-t|+|t| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hw1 : w≠1 := by intro he; simp [he] at him; linarith
  refine ⟨hwz,hw1,?_⟩
  have hwp : 1/2 ≤ w.re := by linarith [div_pos ha hHp]
  have hwn : ‖w‖ ≤ 3+|t| := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_nonneg (by linarith : 0 ≤ w.re)]
    linarith
  have hden : 1≤‖w-1‖ := by
    have h := Complex.abs_im_le_norm (w-1)
    simp at h
    linarith
  have hb := zeta_vertical_bound (by linarith : 0<w.re) hw1
  rw [norm_div] at hb
  have hB : ‖riemannZeta w‖ ≤ 3*(3+|t|) := by
    have h₁ := div_le_self (norm_nonneg w) hden
    have h₂ : ‖w‖/w.re ≤ 2*‖w‖ := by
      apply (div_le_iff₀ (by linarith : 0<w.re)).mpr
      nlinarith [mul_nonneg (norm_nonneg w) (sub_nonneg.mpr hwp)]
    linarith
  refine hB.trans ?_
  have he : Real.exp H = Real.exp 1*(3+2*|t|) := by
    dsimp [H,heightFactor]
    rw [Real.exp_add,Real.exp_log (by positivity)]
  rw [two_mul,Real.exp_add,he]
  have hh := Real.one_le_exp (by norm_num : (0:ℝ)≤1)
  have hm : 3+2*|t| ≤ Real.exp 1*(3+2*|t|) := by nlinarith [mul_nonneg (sub_nonneg.mpr hh) (show 0≤3+2*|t| by positivity)]
  nlinarith [mul_self_le_mul_self (by positivity : 0≤3+2*|t|) hm,sq_nonneg |t|]
end RHConnections.ReciprocalLocalComparison
