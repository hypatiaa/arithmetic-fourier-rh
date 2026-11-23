import Verified
import RieszPrimeMellin

noncomputable section
open MeasureTheory Set ArithmeticFunction
namespace RHConnections.RieszPrimeMellin

private theorem integrate_prime_atom {x : ℝ} (hx : 1≤x) {n : ℕ} (hn : (n:ℝ)≤x) :
    (∫ t in Set.Ioc (1:ℝ) x, (Set.Ici (n:ℝ)).indicator (fun _ => vonMangoldt n) t) =
      vonMangoldt n*(x-n) := by
  by_cases h : n≤1
  · have he : n=0 ∨ n=1 := by omega
    rcases he with rfl|rfl <;> simp
  have hn1 : (1:ℝ)<n := by exact_mod_cast (lt_of_not_ge h)
  rw [setIntegral_indicator measurableSet_Ici]
  have he : Set.Ioc (1:ℝ) x ∩ Set.Ici (n:ℝ)=Set.Icc (n:ℝ) x := by
    ext t
    simp only [Set.mem_inter_iff,Set.mem_Ioc,Set.mem_Ici,Set.mem_Icc]
    constructor
    · rintro ⟨⟨ht,hx'⟩,hn'⟩
      exact ⟨hn',hx'⟩
    · intro ht
      exact ⟨⟨hn1.trans_le ht.1,ht.2⟩,ht.1⟩
  rw [he]
  simp [integral_const,max_eq_left (sub_nonneg.mpr hn),mul_comm]

theorem riesz_error_finite_ramp {x : ℝ} (hx : 1≤x) :
    rieszError x =
      x⁻¹*((∑ n∈Finset.Icc 0 ⌊x⌋₊,vonMangoldt n*(x-n))-(x^2-1)/2) := by
  let s := Finset.Icc 0 ⌊x⌋₊
  let f (n : ℕ) := (Set.Ici (n:ℝ)).indicator (fun _ => vonMangoldt n)
  have hsum (t : ℝ) (ht : t∈Set.Ioc (1:ℝ) x) : Chebyshev.psi t=∑ n∈s,f n t := by
    rw [Chebyshev.psi_eq_sum_Icc]
    have hl : ∀ n∈Finset.Icc 0 ⌊t⌋₊, f n t=vonMangoldt n := by
      intro n hn
      have h := (Nat.le_floor_iff (show 0≤t by linarith [ht.1])).mp (Finset.mem_Icc.mp hn).2
      exact Set.indicator_of_mem h _
    rw [←Finset.sum_congr rfl hl]
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Icc.mp hn).2.trans (Nat.floor_mono ht.2)⟩
    · intro n hn hnt
      exact Set.indicator_of_notMem (fun hh => hnt
        (Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Nat.le_floor_iff (show 0≤t by linarith [ht.1])).mpr hh⟩)) _
  have hfi (n : ℕ) (_ : n∈s) : IntegrableOn (f n) (Set.Ioc (1:ℝ) x) := by
    exact (integrableOn_const measure_Ioc_lt_top.ne).indicator measurableSet_Ici
  have hpsi : IntegrableOn Chebyshev.psi (Set.Ioc (1:ℝ) x) := by
    have hi := integrable_finsetSum s hfi
    exact hi.congr ((ae_restrict_mem measurableSet_Ioc).mono (fun t ht => (hsum t ht).symm))
  have hid : IntegrableOn (fun t : ℝ => t) (Set.Ioc (1:ℝ) x) :=
    (continuous_id.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  unfold rieszError PrimeErrorLaplace.realPrimeError
  rw [integral_sub hpsi hid,setIntegral_congr_fun measurableSet_Ioc hsum,
    integral_finsetSum _ hfi,←intervalIntegral.integral_of_le hx]
  have hI : (∫ t : ℝ in 1..x,t) = (x^2-1)/2 := by
    simpa using (integral_pow (a := (1:ℝ)) (b := x) (n := 1))
  rw [hI]
  congr 2
  apply Finset.sum_congr rfl
  intro n hn
  exact integrate_prime_atom hx ((Nat.le_floor_iff (zero_le_one.trans hx)).mp (Finset.mem_Icc.mp hn).2)

end RHConnections.RieszPrimeMellin
