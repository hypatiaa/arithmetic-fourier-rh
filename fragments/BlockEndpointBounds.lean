import Verified
import BlockIntervalShift

namespace RHConnections.BlockFourier

open RHConnections.RankPairing
variable {J : ℕ} [NeZero J]

theorem cyclic_interval_endpoint_bound
    (d : ZMod J → ℝ) (F : ℕ → ℝ)
    (hstep : ∀ j < J, d (j : ZMod J) = F (j+1)-F j)
    (B B0 : ℝ) (hB0 : 0 ≤ B0)
    (hF : ∀ j ≤ J, |F j|≤B) (hF0 : |F 0|≤B0)
    (a : ZMod J) (length : ℕ) (hlen : length≤J) :
    |blockIntervalSum d a length| ≤ B0+3*B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hF 0 (Nat.zero_le _))
  have ordinary (b m : ℕ) (hb : b+m≤J) :
      blockIntervalSum d (b:ZMod J) m = F (b+m)-F b := by
    induction m with
    | zero => simp [blockIntervalSum]
    | succ m ih =>
      rw [blockIntervalSum,Finset.sum_range_succ,←blockIntervalSum]
      rw [ih (by omega),←Nat.cast_add,hstep _ (by omega)]
      rw [show b+(m+1)=b+m+1 by omega]
      ring
  have ha := ZMod.val_lt a
  have hac : (a.val : ZMod J) = a := ZMod.natCast_zmod_val a
  by_cases h : a.val+length≤J
  · rw [←hac,ordinary _ _ h]
    exact (abs_sub _ _).trans (by linarith only [hF _ h,hF _ ha.le,hB,hB0])
  · let m := J-a.val
    let n := length-m
    have hmn : m+n=length := by dsimp [m,n]; omega
    have hm : a.val+m=J := by dsimp [m]; omega
    have hn : n≤J := by dsimp [n]; omega
    have hsplit :
        blockIntervalSum d a (m+n) = blockIntervalSum d a m + blockIntervalSum d 0 n := by
      simp only [blockIntervalSum,Finset.sum_range_add,Nat.cast_add,← add_assoc]
      have hwrap : a+(m:ZMod J)=0 := by
        rw [←hac,←Nat.cast_add,hm,ZMod.natCast_self]
      simp [hwrap]
    rw [←hmn,hsplit,←hac,ordinary _ _ hm.le,hm]
    rw [show (0:ZMod J) = ((0:ℕ):ZMod J) by simp,ordinary 0 n (by simpa using hn)]
    simp only [Nat.zero_add]
    exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) (abs_sub _ _))
      |>.trans (by linarith only [hF J le_rfl,hF _ ha.le,hF _ hn,hF0])

theorem cyclic_interval_bound_preserved (d L : ZMod J → ℝ)
    (hL : ∀ h, 0 ≤ L h) (hmass : ∑ h, L h = 1)
    (B : ℝ) (hB : ∀ a length, length ≤ J → |blockIntervalSum d a length| ≤ B)
    (a : ZMod J) (length : ℕ) (hlen : length ≤ J) :
    |blockIntervalSum (fun x => ∑ h, L h*d (x+h)) a length| ≤ B := by
  have heq : blockIntervalSum (fun x => ∑ h, L h*d (x+h)) a length =
      ∑ h, L h*blockIntervalSum d (a+h) length := by
    simp only [blockIntervalSum,Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.range length)]
    simp only [add_right_comm a]
  rw [heq]
  calc
    _ ≤ ∑ h, |L h * blockIntervalSum d (a+h) length| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h, L h*B := by
      apply Finset.sum_le_sum
      intro h _
      rw [abs_mul,abs_of_nonneg (hL h)]
      exact mul_le_mul_of_nonneg_left (hB _ _ hlen) (hL h)
    _ = B := by rw [←Finset.sum_mul,hmass,one_mul]

theorem buthe_endpoint_interval_bound
    (d : ZMod J → ℝ) (F : ℕ → ℝ) (u : ℕ → ℝ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hstep : ∀ j < J, d (j : ZMod J) = F (j+1)-F j)
    (hu0 : u 0 = Q) (hu : ∀ j ≤ J, u j ≤ 2*Q)
    (hf : ∀ j ≤ J, |F j| ≤ (94/100:ℝ)*Real.sqrt (u j))
    (a : ZMod J) (length : ℕ) (hlen : length ≤ J) :
    |blockIntervalSum d a length| ≤ 5*Real.sqrt Q := by
  let B := (94/100:ℝ)*Real.sqrt (2*Q)
  let B0 := (94/100:ℝ)*Real.sqrt Q
  have hF : ∀ j ≤ J, |F j|≤B := by
    intro j hj
    exact (hf j hj).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hu j hj)) (by norm_num))
  have hF0 : |F 0|≤B0 := by simpa [B0,hu0] using hf 0 (Nat.zero_le J)
  have hb0 : 0≤B0 := by dsimp [B0]; positivity
  have hsqrt : Real.sqrt 2 ≤ (142/100:ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Real.sqrt_nonneg 2]
  refine (cyclic_interval_endpoint_bound d F hstep B B0 hb0 hF hF0 a length hlen).trans ?_
  dsimp [B0,B]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  nlinarith only [Real.sqrt_nonneg Q,mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg Q)]

end RHConnections.BlockFourier
