import AstraSharpDyadicX

noncomputable section
namespace RHConnections.SharpRightEndpoint

def blockRight (Y : ℝ) := (Y/Real.exp 1)*retained (Real.log Y-1)

theorem sharp_individual_endpoint :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ X : ℝ, Real.exp 2 ≤ X →
      ∃ (n : ℕ) (Y : ℝ), Real.exp 2 ≤ Y ∧ Y < 2*Real.exp 2 ∧ X = 2^n*Y ∧
        |Chebyshev.psi X-X| ≤
          (∑ j ∈ Finset.range n, blockRight (2^j*Y)) + D*X^(5/6 : ℝ)*(1+Real.log X)^2 := by
  obtain ⟨C,hC,hblock⟩ := sharp_dyadic_X
  let p : ℝ := 5/6
  have hp : 0 < p := by norm_num [p]
  let q := (2:ℝ)^p
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) hp
  let A := (Real.log 4+5)*(2*Real.exp 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let D := max A (C/(q-1))
  have hD : 0 ≤ D := hA.trans (le_max_left _ _)
  have hbudget : C+D ≤ D*q := by
    have hh := (div_le_iff₀ (sub_pos.mpr hq)).mp
      (show C/(q-1) ≤ D from le_max_right _ _)
    linarith
  refine ⟨D,hD,?_⟩
  intro X hX
  have he := Real.exp_pos 2
  have hx : 1 ≤ X/Real.exp 2 := (one_le_div he).mpr hX
  obtain ⟨n,hnL,hnU⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  let Y := X/(2:ℝ)^n
  have hn : (0:ℝ)<2^n := by positivity
  have hY : Real.exp 2 ≤ Y := (le_div_iff₀ hn).mpr <| by
    have hh := (le_div_iff₀ he).mp hnL
    linarith
  have hY' : Y < 2*Real.exp 2 := (div_lt_iff₀ hn).mpr <| by
    have hh := (div_lt_iff₀ he).mp hnU
    rw [pow_succ] at hh
    linarith
  have hid : X = 2^n*Y := by dsimp [Y]; field_simp
  have hY0 := he.trans_le hY
  have hOne : 1 ≤ Y := (Real.one_le_exp (by norm_num : (0:ℝ)≤2)).trans hY
  let Z (k : ℕ) := (2:ℝ)^k*Y
  have hZ (k : ℕ) : Real.exp 2 ≤ Z k := hY.trans <| le_mul_of_one_le_left hY0.le
    (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hZs (k : ℕ) : Z (k+1) = 2*Z k := by dsimp [Z]; rw [pow_succ]; ring
  let L (x : ℝ) := (1+Real.log x)^2
  have hLog (k : ℕ) : 1 ≤ L (Z k) := by
    have h1 : (1:ℝ) ≤ Z k := (Real.one_le_exp (by norm_num : (0:ℝ)≤2)).trans (hZ k)
    have ha := Real.log_nonneg h1
    dsimp [L]; nlinarith [sq_nonneg (Real.log (Z k))]
  have hLmono (k : ℕ) : L (Z k) ≤ L (2*Z k) := by
    have hx := he.trans_le (hZ k)
    have hl := Real.log_le_log hx (by linarith : Z k ≤ 2*Z k)
    have h0 := Real.log_nonneg ((Real.one_le_exp (by norm_num : (0:ℝ)≤2)).trans (hZ k))
    exact pow_le_pow_left₀ (by linarith) (add_le_add (le_refl (1:ℝ)) hl) 2
  have hsum (k : ℕ) : |Chebyshev.psi (Z k)-Z k| ≤
      (∑ j ∈ Finset.range k, blockRight (Z j)) + D*(Z k)^p*L (Z k) := by
    induction k with
    | zero =>
      simp only [Z,pow_zero,one_mul,Finset.range_zero,Finset.sum_empty,zero_add]
      have hb := PrimeErrorLaplace.real_prime_error_linear hY0.le
      change |Chebyshev.psi Y-Y| ≤ (Real.log 4+5)*Y at hb
      calc
        _ ≤ (Real.log 4+5)*Y := hb
        _ ≤ A := mul_le_mul_of_nonneg_left hY'.le (by positivity)
        _ ≤ D := le_max_left _ _
        _ ≤ D*Y^p := le_mul_of_one_le_right hD (Real.one_le_rpow hOne hp.le)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (by simpa only [Z,pow_zero,one_mul] using hLog 0)
    | succ k ih =>
      rw [hZs,Finset.sum_range_succ]
      have hb := hblock (Z k) (hZ k)
      change |(Chebyshev.psi (2*Z k)-Chebyshev.psi (Z k))-Z k| ≤ blockRight (Z k)+C*(Z k)^p*L (Z k) at hb
      have hpow : (2*Z k)^p = (2:ℝ)^p*(Z k)^p :=
        Real.mul_rpow (by norm_num) (he.trans_le (hZ k)).le
      have herr := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (he.trans_le (hZ k)).le p)
      change (2*Z k)^p = q*(Z k)^p at hpow
      have hLn : 0 ≤ L (Z k) := zero_le_one.trans (hLog k)
      have herr2 := mul_le_mul_of_nonneg_right herr hLn
      have hmono := mul_le_mul_of_nonneg_left (hLmono k) (show 0 ≤ D*q*(Z k)^p by positivity)
      rw [hpow]
      calc
        _ = |((Chebyshev.psi (2*Z k)-Chebyshev.psi (Z k))-Z k) + (Chebyshev.psi (Z k)-Z k)| := by congr 1; ring
        _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hb ih).trans (by linarith))
  refine ⟨n,Y,hY,hY',hid,?_⟩
  change |Chebyshev.psi X-X| ≤ (∑ j ∈ Finset.range n, blockRight (Z j)) + D*X^p*L X
  have hsame : X = Z n := hid
  rw [hsame]
  exact hsum n

#print axioms sharp_individual_endpoint
end RHConnections.SharpRightEndpoint
