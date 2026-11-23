import Verified

open Finset ArithmeticFunction Filter
noncomputable section
namespace RHConnections.ArithmeticFourierShell
open ArithmeticFourierInversion

def primeCofactors : Finset ℕ := {3,5,7,13,17,19,23,29,31,37,41,43}

theorem prime_cofactor_properties {r : ℕ} (hr : r ∈ primeCofactors) :
    r.Prime ∧ Odd r ∧ r ≤ 43 ∧ r ≠ 11 := by
  simp only [primeCofactors,Finset.mem_insert,Finset.mem_singleton] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem prime_cofactor_reciprocals_gt_one :
    1 < ∑ r ∈ primeCofactors, (1:ℝ)/(r:ℝ) := by
  norm_num [primeCofactors]

def cofactorPartners (X r : ℕ) : Finset ℕ :=
  ((primeHalfShell ((X:ℝ)/r)).filter (fun q => 43 < q)).image (fun q => r*q)

def semiprimePartners (X : ℕ) : Finset ℕ := primeCofactors.biUnion (cofactorPartners X)

def shellPrimes (X : ℕ) : Finset ℕ := (upperOddShell X).filter Nat.Prime

private theorem cofactor_partner_mem {X r n : ℕ} (hr : 0 < r) :
    n ∈ cofactorPartners X r ↔
      ∃ q : ℕ, q.Prime ∧ 43 < q ∧ X < 2*(r*q) ∧ r*q ≤ X ∧ r*q = n := by
  have hrp : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hX : 0 ≤ (X:ℝ)/(r:ℝ) := by positivity
  simp only [cofactorPartners,Finset.mem_image,Finset.mem_filter,prime_half_shell_mem hX]
  constructor
  · rintro ⟨q,⟨⟨hq,hlo,hhi⟩,hq43⟩,rfl⟩
    refine ⟨q,hq,hq43,?_,?_,rfl⟩
    · rw [_root_.div_div,div_lt_iff₀ (by positivity : 0<(r:ℝ)*2)] at hlo
      exact_mod_cast (show (X:ℝ) < 2*((r:ℝ)*(q:ℝ)) by nlinarith)
    · rw [le_div_iff₀ hrp] at hhi
      exact_mod_cast (show ((r:ℝ)*(q:ℝ)) ≤ X by simpa only [mul_comm (q:ℝ) (r:ℝ)] using hhi)
  · rintro ⟨q,hq,hq43,hlo,hhi,rfl⟩
    refine ⟨q,⟨⟨hq,?_,?_⟩,hq43⟩,rfl⟩
    · rw [_root_.div_div,div_lt_iff₀ (by positivity : 0<(r:ℝ)*2)]
      have h : (X:ℝ) < 2*((r:ℝ)*(q:ℝ)) := by exact_mod_cast hlo
      nlinarith
    · rw [le_div_iff₀ hrp]
      have h : ((r:ℝ)*(q:ℝ)) ≤ X := by exact_mod_cast hhi
      simpa only [mul_comm (r:ℝ)] using h

private theorem small_prime_divides_cofactor {r q p : ℕ} (hp : p.Prime) (hp43 : p ≤ 43)
    (hq : q.Prime) (hq43 : 43 < q) (hd : p ∣ r*q) : p ∣ r := by
  rcases hp.dvd_mul.mp hd with h | h
  · exact h
  · have he := (Nat.dvd_prime hq).mp h
    exact (he.elim hp.ne_one (fun e => (not_le_of_gt hq43) (e ▸ hp43))).elim

theorem cofactor_partner_pairwise_disjoint (X : ℕ) :
    (primeCofactors : Set ℕ).PairwiseDisjoint (cofactorPartners X) := by
  intro r hr s hs hne
  change Disjoint (cofactorPartners X r) (cofactorPartners X s)
  rw [Finset.disjoint_left]
  intro n hn hm
  obtain ⟨hrp,_,hr43,_⟩ := prime_cofactor_properties hr
  obtain ⟨hsp,_,_,_⟩ := prime_cofactor_properties hs
  obtain ⟨q,hq,hq43,_,_,he⟩ := (cofactor_partner_mem hrp.pos).mp hn
  obtain ⟨p,hp,hp43,_,_,he'⟩ := (cofactor_partner_mem hsp.pos).mp hm
  have hd : r ∣ s*p := ⟨q,he'.trans he.symm⟩
  have h := (Nat.dvd_prime hsp).mp (small_prime_divides_cofactor hrp hr43 hp hp43 hd)
  exact h.elim hrp.ne_one hne

theorem semiprime_partners_in_shell (X : ℕ) : semiprimePartners X ⊆ upperOddShell X := by
  intro n hn
  obtain ⟨r,hr,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨hrp,hrodd,_,_⟩ := prime_cofactor_properties hr
  obtain ⟨q,hq,hq43,hlo,hhi,rfl⟩ := (cofactor_partner_mem hrp.pos).mp hn
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  exact upper_odd_shell_iff.mpr ⟨Nat.mul_pos hrp.pos hq.pos,hhi,hrodd.mul hqodd,hlo⟩

theorem semiprime_partner_sign {X n : ℕ} (hn : n ∈ semiprimePartners X) : muR n = 1 := by
  obtain ⟨r,hr,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨hrp,_,hr43,_⟩ := prime_cofactor_properties hr
  obtain ⟨q,hq,hq43,_,_,rfl⟩ := (cofactor_partner_mem hrp.pos).mp hn
  have hne : r ≠ q := by omega
  have h := isMultiplicative_moebius.map_mul_of_coprime (hrp.coprime_iff_not_dvd.mpr
    (fun h => (Nat.dvd_prime hq).mp h |>.elim hrp.ne_one hne))
  rw [moebius_apply_prime hrp,moebius_apply_prime hq] at h
  have h' : moebius (r*q) = 1 := by linarith
  change (moebius (r*q):ℝ) = 1
  exact_mod_cast h'

theorem shell_prime_sign {X p : ℕ} (hp : p ∈ shellPrimes X) : muR p = -1 := by
  have h := moebius_apply_prime (Finset.mem_filter.mp hp).2
  change (moebius p:ℝ) = -1
  exact_mod_cast h

theorem semiprime_partners_disjoint_primes (X : ℕ) : Disjoint (semiprimePartners X) (shellPrimes X) := by
  rw [Finset.disjoint_left]
  intro n h hn
  linarith [semiprime_partner_sign h,shell_prime_sign hn]

theorem semiprime_partners_disjoint_paired (X : ℕ) : Disjoint (semiprimePartners X) (pairedBlock X) := by
  rw [Finset.disjoint_left]
  intro n hn hA
  obtain ⟨r,hr,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨hrp,_,hr43,hr11⟩ := prime_cofactor_properties hr
  obtain ⟨q,hq,hq43,_,_,rfl⟩ := (cofactor_partner_mem hrp.pos).mp hn
  rw [pairedBlock,Finset.mem_union] at hA
  rcases hA with h | h
  · obtain ⟨d,_,hed⟩ := Finset.mem_image.mp h
    have hd : 11 ∣ r*q := ⟨d,hed.symm⟩
    have h11 := small_prime_divides_cofactor (by decide : Nat.Prime 11) (by norm_num) hq hq43 hd
    exact (Nat.dvd_prime hrp).mp h11 |>.elim (by decide) (fun h => hr11 h.symm)
  · obtain ⟨d,_,hed⟩ := Finset.mem_image.mp h
    have hd : 15 ∣ r*q := ⟨d,hed.symm⟩
    have h3 := small_prime_divides_cofactor Nat.prime_three (by norm_num) hq hq43
      ((by decide : 3 ∣ 15).trans hd)
    have h5 := small_prime_divides_cofactor (by decide : Nat.Prime 5) (by norm_num) hq hq43
      ((by decide : 5 ∣ 15).trans hd)
    have hr3 : r = 3 := ((Nat.dvd_prime hrp).mp h3).resolve_left (by decide) |>.symm
    have hr5 : r = 5 := ((Nat.dvd_prime hrp).mp h5).resolve_left (by decide) |>.symm
    omega

theorem shell_primes_disjoint_paired {X : ℕ} (hX : 22 ≤ X) :
    Disjoint (shellPrimes X) (pairedBlock X) := by
  rw [Finset.disjoint_left]
  intro n hn hA
  have hprime := (Finset.mem_filter.mp hn).2
  rw [pairedBlock,Finset.mem_union] at hA
  rcases hA with h | h
  · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp h
    have h := (paired_seed_iff.mp hd).2.2.2.2.1
    have hdvd : 11 ∣ 11*d := dvd_mul_right 11 d
    rcases (Nat.dvd_prime hprime).mp hdvd with h | h <;> omega
  · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp h
    have h := (paired_seed_iff.mp hd).2.2.2.2.1
    have hdvd : 15 ∣ 15*d := dvd_mul_right 15 d
    rcases (Nat.dvd_prime hprime).mp hdvd with h | h <;> omega

end RHConnections.ArithmeticFourierShell
