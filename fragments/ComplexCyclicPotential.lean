import Verified
import BlockComplexTransfer

noncomputable section
namespace RHConnections.BlockFourier
variable {J : ℕ} [NeZero J]

theorem complex_cyclic_potential_bound (d : ZMod J → ℂ) (F : ℕ → ℂ)
    (hstep : ∀ j<J,d (j:ZMod J)=F (j+1)-F j)
    {B : ℝ} (hB : 0≤B)
    (hdiff : ∀ j≤J, ∀ k≤J, ‖F j-F k‖≤B)
    (a : ZMod J) (len : ℕ) (hlen : len≤J) :
    ‖complexIntervalSum d a len‖≤2*B := by
  have ordinary (b m : ℕ) (hb : b+m≤J) :
      complexIntervalSum d (b:ZMod J) m = F (b+m)-F b := by
    induction m with
    | zero => simp [complexIntervalSum]
    | succ m ih =>
      rw [complexIntervalSum,Finset.sum_range_succ,←complexIntervalSum]
      rw [ih (by omega),←Nat.cast_add,hstep _ (by omega)]
      rw [show b+(m+1)=b+m+1 by omega]
      ring
  have ha := ZMod.val_lt a
  have hac : (a.val:ZMod J)=a := ZMod.natCast_zmod_val a
  by_cases h : a.val+len≤J
  · rw [←hac,ordinary _ _ h]
    exact (hdiff _ h _ ha.le).trans (by linarith)
  · let m := J-a.val
    let n := len-m
    have hmn : m+n=len := by dsimp [m,n]; omega
    have hm : a.val+m=J := by dsimp [m]; omega
    have hn : n≤J := by dsimp [n]; omega
    have hsplit :
        complexIntervalSum d a (m+n) = complexIntervalSum d a m + complexIntervalSum d 0 n := by
      simp only [complexIntervalSum,Finset.sum_range_add,Nat.cast_add,←add_assoc]
      have hwrap : a+(m:ZMod J)=0 := by rw [←hac,←Nat.cast_add,hm,ZMod.natCast_self]
      simp [hwrap]
    rw [←hmn,hsplit,←hac,ordinary _ _ hm.le,hm]
    rw [show (0:ZMod J)=((0:ℕ):ZMod J) by simp,ordinary 0 n (by simpa using hn)]
    simp only [Nat.zero_add]
    exact ((norm_add_le _ _).trans (add_le_add (hdiff _ le_rfl _ ha.le)
      (hdiff _ hn _ (Nat.zero_le J)))).trans_eq (by ring)

theorem complex_cyclic_bound_preserved (d : ZMod J → ℂ) (L : ZMod J → ℝ)
    (hL : ∀ h,0≤L h) (hmass : ∑ h,L h=1) {B : ℝ}
    (hd : ∀ a len, len≤J → ‖complexIntervalSum d a len‖≤B)
    (a : ZMod J) (len : ℕ) (hlen : len≤J) :
    ‖complexIntervalSum (smoothComplexPositive L d) a len‖≤B := by
  have he : complexIntervalSum (smoothComplexPositive L d) a len =
      ∑ h : ZMod J,(L h:ℂ)*complexIntervalSum d (a+h) len := by
    simp only [complexIntervalSum,smoothComplexPositive,Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.range len)]
    simp only [add_right_comm a]
  rw [he]
  calc
    _ ≤ ∑ h : ZMod J, ‖(L h:ℂ)*complexIntervalSum d (a+h) len‖ := norm_sum_le _ _
    _ ≤ ∑ h : ZMod J, L h*B := by
      apply Finset.sum_le_sum
      intro h _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hL h)]
      exact mul_le_mul_of_nonneg_left (hd _ _ hlen) (hL h)
    _ = _ := by rw [←Finset.sum_mul,hmass,one_mul]

end RHConnections.BlockFourier
