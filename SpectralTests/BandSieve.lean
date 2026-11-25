module
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Prime.Basic
public import SpectralTests.Thresholds

@[expose] public section
namespace GoldbachSpectral.BandSieve
open Finset
open scoped BigOperators

/-- Indicator of avoiding the prime divisors in the band. -/
def free (s : Finset ℕ) (n : ℕ) : ℤ :=
  ∏ p ∈ s, if p ∣ n then (0:ℤ) else 1

def hit (d n : ℕ) : ℤ := if d ∣ n then 1 else 0

private theorem subset_term {t : Finset ℕ} {n : ℕ}
    (prime : ∀ p ∈ t, Nat.Prime p) :
    (∏ p ∈ t, (if p ∣ n then (-1:ℤ) else 0)) =
      (-1:ℤ)^t.card * hit (∏ p ∈ t,p) n := by
  classical
  by_cases hall : ∀ p ∈ t, p ∣ n
  · have hd := Finset.prod_primes_dvd n (fun p hp => (prime p hp).prime) hall
    rw [hit, ite_eq_left hd, mul_one]
    calc
      _ = ∏ _ ∈ t, (-1:ℤ) := Finset.prod_congr rfl (fun p hp => ite_eq_left (hall p hp))
      _ = _ := Finset.prod_const _
  · push Not at hall
    obtain ⟨p,hp,hno⟩ := hall
    have hn : ¬ (∏ q ∈ t,q) ∣ n := fun h => hno ((Finset.dvd_prod_of_mem id hp).trans h)
    rw [hit, ite_eq_right hn, mul_zero]
    exact Finset.prod_eq_zero hp (ite_eq_right hno)

theorem inclusion_exclusion (s : Finset ℕ) (n : ℕ) (prime : ∀ p ∈ s, Nat.Prime p) :
    free s n = ∑ t ∈ s.powerset, (-1:ℤ)^t.card * hit (∏ p ∈ t,p) n := by
  classical
  unfold free
  calc
    _ = ∏ p ∈ s, (1 + (if p ∣ n then (-1:ℤ) else 0)) := by
      apply Finset.prod_congr rfl
      intro p _
      split_ifs <;> norm_num
    _ = _ := (Finset.prod_one_add s).trans (Finset.sum_congr rfl (fun t ht =>
      subset_term (fun p hp => prime p ((mem_powerset.mp ht) hp))))

private theorem absent {s : Finset ℕ} {z n j : ℕ} (hz : 1 ≤ z)
    (lower : ∀ p ∈ s, z ≤ p) (hn : 0 < n) (small : n < z^j) (hj : j ≤ s.card) :
    hit (∏ p ∈ s,p) n = 0 := by
  have hpow : z^j ≤ z^s.card := Nat.pow_le_pow_right hz hj
  have hprod : z^s.card ≤ ∏ p ∈ s,p := by
    simpa using (Finset.prod_le_prod (s := s) (f := fun _ => z) (g := id) lower)
  exact ite_eq_right (fun h => (not_lt_of_ge (hpow.trans (hprod.trans (Nat.le_of_dvd hn h)))) small)

def below (s : Finset ℕ) (k x y : ℕ) : ℤ :=
  ∑ t ∈ s.powerset, if t.card < k then
    (-1:ℤ)^t.card * (hit (∏ p ∈ t,p) x - hit (∏ p ∈ t,p) y) else 0

/-- The one-sided extra layer, before averaging. Its sign is positive for
odd k. The two arguments are positive and the cutoff inequalities are strict. -/
theorem extra_layer {s : Finset ℕ} {z k x y : ℕ} (hz : 1 ≤ z) (odd : Odd k)
    (pr : ∀ p ∈ s, Nat.Prime p) (band : ∀ p ∈ s, z ≤ p)
    (hx : 0 < x) (hxs : x < z^k) (hy : 0 < y) (hys : y < z^(k+1)) :
    free s x - free s y = below s k x y +
      ∑ t ∈ s.powerset, if t.card = k then hit (∏ p ∈ t,p) y else 0 := by
  classical
  rw [inclusion_exclusion s x pr,inclusion_exclusion s y pr, ← Finset.sum_sub_distrib]
  unfold below
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have lo := fun p (hp : p ∈ t) => band p (mem_powerset.mp ht hp)
  rcases lt_trichotomy t.card k with h|h|h
  · simp [h,ne_of_lt h,mul_sub]
  · have no := absent hz lo hx hxs h.ge
    rw [ite_eq_right (by omega : ¬ t.card < k), ite_eq_left h, h, odd.neg_one_pow, no]
    ring
  · have nx := absent hz lo hx hxs h.le
    have ny := absent hz lo hy hys (by omega)
    simp [nx,ny,show ¬t.card < k by omega,ne_of_gt h]

end GoldbachSpectral.BandSieve
