module
public import SpectralTests.Parameters

@[expose] public section
noncomputable section
namespace GoldbachSpectral.BandSieve
open Finset Filter
open scoped Topology

def windowRoot (t : ℕ) := 2^(t^9)
def window (t : ℕ) := (windowRoot t)^64

theorem large_root (t : ℕ) : t≤windowRoot t := by
  exact (Nat.le_self_pow (by decide : 9≠0) t).trans Nat.lt_two_pow_self.le

theorem polynomial_le_root (D k : ℕ) : ∀ᶠ t : ℕ in atTop, D*t^k≤windowRoot t := by
  filter_upwards [eventually_ge_atTop (max (D+k) 2)] with t ht
  have high : D+t*k ≤ t^9 := by
    have a : D≤D*t := Nat.le_mul_of_pos_right D (by omega)
    have b := Nat.mul_le_mul_right t (show D+k≤t by omega)
    have c := Nat.pow_le_pow_right (n := t) (by omega : 0<t) (by decide : 2≤9)
    nlinarith only [a,b,c]
  calc
    _ ≤ 2^D*(2^t)^k := Nat.mul_le_mul (show D<2^D from Nat.lt_two_pow_self).le (Nat.pow_le_pow_left (show t<2^t from Nat.lt_two_pow_self).le _)
    _ = 2^(D+t*k) := by rw [← pow_mul,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) high

theorem wheel_small : ∀ᶠ t : ℕ in atTop, wheel (bandPrimes (sieveBand t))≤windowRoot t := by
  filter_upwards [eventually_ge_atTop 274] with t ht
  let z := sieveBand t
  let s := bandPrimes z
  let B := 2*z
  have card : s.card≤B+1 := by
    have sub : s ⊆ range (B+1) := fun p hp => mem_range.mpr (Nat.lt_succ_iff.mpr (mem_band.mp hp).2.2)
    exact (card_le_card sub).trans (card_range _).le
  have bound := Finset.prod_le_prod (s := s) (fun p hp => (mem_band.mp hp).2.2.trans (show B<2^B from Nat.lt_two_pow_self).le)
  rw [prod_const,← pow_mul] at bound
  have bp : B=16*t^4 := by dsimp [B,z,sieveBand]; ring
  have s1 : 1≤t^4 := Nat.one_le_pow _ _ (by omega)
  have s2 : 1≤t^8 := Nat.one_le_pow _ _ (by omega)
  have four : t^4≤t^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have exp : B*s.card+1≤t^9 := by
    have v := Nat.mul_le_mul_left B card
    rw [bp] at v ⊢
    have hi := Nat.mul_le_mul_right (t^8) ht
    nlinarith only [v,hi,s2,four]
  change 2*(∏ p∈s,p)≤2^(t^9)
  exact (Nat.mul_le_mul_left 2 bound).trans ((by rw [pow_succ'] : 2*2^(B*s.card)=2^(B*s.card+1)).le.trans (Nat.pow_le_pow_right (by decide) exp))

theorem wheel_four {t : ℕ} (ht : 1≤t) (many : t^3≤(bandPrimes (sieveBand t)).card) :
    4≤wheel (bandPrimes (sieveBand t)) := by
  let s := bandPrimes (sieveBand t)
  have p0 : 0<s.card := (pow_pos ht 3).trans_le many
  obtain ⟨p,mem⟩ := card_pos.mp p0
  have pr := (mem_band.mp mem).1
  have full := Finset.prod_pos (s := s) (f := id) (fun u hu => (mem_band.mp hu).1.pos)
  have val := Nat.le_of_dvd full (Finset.dvd_prod_of_mem id mem)
  simp only [id_eq] at val
  have p2 := pr.two_le
  dsimp only [wheel]
  change 4≤2*∏ u∈s,u
  omega

theorem window_log (t : ℕ) : Real.log (window t:ℝ) ≤ 64*(t:ℝ)^9 := by
  simp only [window,windowRoot,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  have two : Real.log 2≤1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith only [mul_le_mul_of_nonneg_left two (show 0≤64*(t:ℝ)^9 by positivity)]

end GoldbachSpectral.BandSieve

