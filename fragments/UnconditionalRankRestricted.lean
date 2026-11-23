import Verified
import UnconditionalMertens

noncomputable section
namespace RHConnections.RankPairing
open ArithmeticFourierInversion ArithmeticFourierMertensKernel ArithmeticFourierDyadic
  FinitePerron

theorem quantitative_mertens_at_dyadic_cutoffs :
    ∃ a C : ℝ, 0<a ∧ 0≤C ∧ ∀ X Q u : ℕ, 0<Q → Q≤u → u≤2*Q →
      max (16:ℝ) (4*Real.exp 1) ≤ ((X/Q:ℕ):ℝ) →
      Real.sqrt |M (X/u)| ≤
        C*Real.sqrt ((X/Q:ℕ):ℝ)*Real.exp (-a*Real.sqrt (Real.log ((X/Q:ℕ):ℝ))) := by
  obtain ⟨α,C,hα,hC,hM⟩ := quantitative_natural_mertens
  refine ⟨α/4,Real.sqrt C,by positivity,Real.sqrt_nonneg _,?_⟩
  intro X Q u hQ hQu huQ hN
  let N := X/Q
  let n := X/u
  change Real.sqrt |M n| ≤ Real.sqrt C*Real.sqrt (N:ℝ)*
    Real.exp (-(α/4)*Real.sqrt (Real.log (N:ℝ)))
  have hu : 0<u := hQ.trans_le hQu
  have huR : (0:ℝ)<u := by exact_mod_cast hu
  have hQR : (0:ℝ)<Q := by exact_mod_cast hQ
  have hN16 : 16≤(N:ℝ) := (le_max_left _ _).trans hN
  have hNexp : 4*Real.exp 1≤(N:ℝ) := (le_max_right _ _).trans hN
  have hNP : (0:ℝ)<N := by linarith
  have hnN : (n:ℝ)≤N := by exact_mod_cast Nat.div_le_div_left hQu hQ
  have hn4 : (N:ℝ)/4≤n := by
    have hNQ : (N:ℝ)*(Q:ℝ)≤X := by
      exact_mod_cast Nat.div_mul_le_self X Q
    have hmod : ((X%u:ℕ):ℝ)≤u := by exact_mod_cast (Nat.mod_lt X hu).le
    have hdiv : (u:ℝ)*(n:ℝ)+((X%u:ℕ):ℝ)=X := by exact_mod_cast Nat.div_add_mod X u
    have h2Q : (u:ℝ)≤2*(Q:ℝ) := by exact_mod_cast huQ
    have he : (N:ℝ)*(Q:ℝ)≤((n:ℝ)+1)*(2*(Q:ℝ)) := by
      have h₁ := mul_le_mul_of_nonneg_left h2Q (show 0≤(n:ℝ)+1 by positivity)
      nlinarith only [h₁,hNQ,hmod,hdiv]
    have he' : (N:ℝ)≤2*((n:ℝ)+1) := by
      apply le_of_mul_le_mul_right _ hQR
      convert he using 1
      ring
    linarith
  have hnexp : Real.exp 1≤(n:ℝ) := by linarith
  have hnP : (0:ℝ)<n := (Real.exp_pos 1).trans_le hnexp
  have hnlog : 0≤Real.log (n:ℝ) := Real.log_nonneg ((Real.one_le_exp_iff.mpr zero_le_one).trans hnexp)
  have hNlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by linarith)
  have hlogs : Real.log (N:ℝ) ≤ 2*Real.log (n:ℝ) := by
    have h1 := Real.log_le_log hNP (by linarith only [hn4] : (N:ℝ)≤4*(n:ℝ))
    rw [Real.log_mul (by norm_num) hnP.ne'] at h1
    have h2 := Real.log_le_log (by norm_num : (0:ℝ)<4) (by linarith only [hn4,hN16] : (4:ℝ)≤n)
    linarith
  have hroot : Real.sqrt (Real.log (N:ℝ))/2≤Real.sqrt (Real.log (n:ℝ)) := by
    apply (Real.le_sqrt (by positivity) hnlog).mpr
    rw [div_pow,Real.sq_sqrt hNlog]
    linarith
  have hpw : Real.exp (-α*Real.sqrt (Real.log (n:ℝ))) ≤
      Real.exp (-(α/2)*Real.sqrt (Real.log (N:ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hroot hα.le]
  have hB : |M n| ≤ C*(N:ℝ)*Real.exp (-(α/2)*Real.sqrt (Real.log (N:ℝ))) :=
    (hM n hnexp).trans (mul_le_mul (mul_le_mul_of_nonneg_left hnN hC) hpw (by positivity) (by positivity))
  refine (Real.sqrt_le_sqrt hB).trans_eq ?_
  have hex : Real.exp (-(α/2)*Real.sqrt (Real.log (N:ℝ))) =
      (Real.exp (-(α/4)*Real.sqrt (Real.log (N:ℝ))))^2 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rw [Real.sqrt_mul (by positivity : 0≤C*(N:ℝ)),Real.sqrt_mul hC,hex,
    Real.sqrt_sq (Real.exp_pos _).le]

theorem unconditional_rank_cost_restricted_power :
    ∃ a C : ℝ, 0<a ∧ 0≤C ∧
    ∀ {X Q r : ℕ}, 0<Q → max (16:ℝ) (4*Real.exp 1) ≤ ((X/Q:ℕ):ℝ) →
      ∀ (u : ℕ → ℕ), Monotone u → u 0=Q → u r=2*Q →
      ∀ A : ℝ, 0<A → Real.log (Q:ℝ) ≤ A*Real.sqrt (Real.log ((X/Q:ℕ):ℝ)) →
      let N := X/Q
      let K := blockKernel (Finset.range r) u (blockVM u) X
      Real.sqrt (sqNorm N (fun n => K n-averageCorrection N K n)) ≤
        (2*(Real.log 4+4)+1)*C*Real.sqrt (N:ℝ)*(Q:ℝ)^(1-a/A) := by
  obtain ⟨a,C,ha,hC,hB⟩ := quantitative_mertens_at_dyadic_cutoffs
  refine ⟨a,C,ha,hC,?_⟩
  intro X Q r hQ hN u hu h0 hr A hA hRange
  apply rank_cost_restricted_power hQ u hu h0 hr A a C hA ha hC hRange
  intro j hj
  exact hB X Q (u j) hQ (h0 ▸ hu (Nat.zero_le j)) (hr ▸ hu (Finset.mem_range.mp hj).le) hN

end RHConnections.RankPairing
