import Verified
import FreezeActualSpectralRows

noncomputable section
open Set
namespace RHConnections.LongRankPhase
open RHConnections.BlockFourier RHConnections.RankPairing

theorem row_grid_connection (X Q Q₀ a b : ℝ) (r : RankRow)
    (hQ₀ : 1≤Q₀) (hQ : Q₀≤Q) (ha : a∈Icc Q (2*Q)) (hb : b∈Icc Q (2*Q))
    (hab : a≤b)
    (he₁ : X/((rowEndpoints ⌊X/Q⌋₊ r).2:ℝ)=a)
    (he₂ : X/((rowEndpoints ⌊X/Q⌋₊ r).1:ℝ)=b)
    (hLong : 12*Q*(Q₀^(-(1/8:ℝ))) < b-a) :
    let len := (rowStartLength X Q r).2
    |(len:ℝ)-(b-a)/realDyadicMeshWidth Q|≤4 ∧
      longRowValue X Q r=shellSpectrumRow Q a b := by
  have hQ1 := hQ₀.trans hQ
  have hQp : 0<Q := zero_lt_one.trans_le hQ1
  have hQ₀p : 0<Q₀ := zero_lt_one.trans_le hQ₀
  let J := realDyadicMeshCount Q
  let R := realDyadicMeshRadius Q
  let u := realDyadicMeshPoint Q
  let H := realDyadicMeshWidth Q
  let ka := realActiveLength J u a
  let kb := realActiveLength J u b
  obtain ⟨hu,hu0h,huJh,hw,hm,hR,hRJ,hHJ⟩ := real_dyadic_mesh Q hQ1
  have hu0 : u 0=Q := hu0h
  have huJ : u J=2*Q := huJh
  have hH : 0<H := Real.sqrt_pos_of_pos hQp
  have hHJp : 0<J := hR.trans_le hRJ
  have hJp : (0:ℝ)<J := by exact_mod_cast hHJp
  letI : NeZero J := ⟨hHJp.ne'⟩
  have hka : ka≤kb := real_active_length_monotone u hab
  have hlen := real_grid_interval_length_rounding J u hu hH.le
    (show a∈Icc (u 0) (u J) by rwa [hu0,huJ]) (show b∈Icc (u 0) (u J) by rwa [hu0,huJ])
    (fun j _ => hw j) (by simpa only [hu0] using hm)
  have hk : rowStartLength X Q r=(ka,kb-ka) := by
    unfold rowStartLength
    dsimp only
    rw [he₁,he₂]
  rw [hk]
  dsimp only
  have hL : |((kb-ka:ℕ):ℝ)-(b-a)/H|≤4 := by
    change |(b-a)-((kb:ℝ)-(ka:ℝ))*H|≤4*H at hlen
    apply (le_of_mul_le_mul_right _ hH)
    rw [Nat.cast_sub hka]
    rw [← show |(((kb:ℝ)-(ka:ℝ))-(b-a)/H)*H| =
        |((kb:ℝ)-(ka:ℝ))-(b-a)/H| * H by rw [abs_mul,abs_of_pos hH] ]
    have he : (((kb:ℝ)-(ka:ℝ))-(b-a)/H)*H = -((b-a)-((kb:ℝ)-(ka:ℝ))*H) := by
      field_simp
      <;> ring
    rw [he,abs_neg]
    exact hlen
  refine ⟨hL,?_⟩
  have hQneg : Q^(-(1/8:ℝ))≤Q₀^(-(1/8:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hQ₀p hQ (by norm_num)
  have hh : Q₀^(1/8:ℝ)≤H := by
    change _ ≤ Real.sqrt Q
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_of_exponent_le hQ₀ (by norm_num : (1/8:ℝ)≤1/2)).trans
      (Real.rpow_le_rpow hQ₀p.le hQ (by norm_num))
  have hunit : 1≤H*Q₀^(-(1/8:ℝ)) := by
    rw [Real.rpow_neg hQ₀p.le,←div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hQ₀p _)).mpr (by simpa using hh)
  have hh2 : (b-a)≤(((kb-ka:ℕ):ℝ)+4)*H := by
    have he := (abs_le.mp hL).1
    have he' : (b-a)/H ≤ ((kb-ka:ℕ):ℝ)+4 := by linarith
    exact (div_le_iff₀ hH).mp he'
  have hHsq : H*H=Q := by
    simpa [H,realDyadicMeshWidth,pow_two] using Real.sq_sqrt hQp.le
  have hLongLen : Q^(-(1/8:ℝ)) < ((kb-ka:ℕ):ℝ)/(J:ℝ) := by
    apply (lt_div_iff₀ hJp).mpr
    have hHJ' : H*(J:ℝ)≤2*Q := hHJ
    have h₁ := mul_le_mul_of_nonneg_left hHJ' (by positivity : 0≤Q₀^(-(1/8:ℝ)))
    have h₂ := mul_le_mul_of_nonneg_right hQneg (Nat.cast_nonneg J)
    have hu1 : 4*H≤4*Q*Q₀^(-(1/8:ℝ)) := by
      have he' := mul_le_mul_of_nonneg_left hunit hH.le
      rw [mul_one,←mul_assoc,hHsq] at he'
      linarith
    apply lt_of_mul_lt_mul_right _ hH.le
    nlinarith only [hLong,hh2,h₁,mul_le_mul_of_nonneg_right h₂ hH.le,hu1, mul_nonneg hQp.le (Real.rpow_nonneg hQ₀p.le (-(1/8:ℝ)))]
  simp only [longRowValue,shellSpectrumRow,hk,J,ka,kb]
  rw [dite_eq_left hHJp,dite_eq_left hHJp,ite_eq_left hLongLen]

end RHConnections.LongRankPhase
