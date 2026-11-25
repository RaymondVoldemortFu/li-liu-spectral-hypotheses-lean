module
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
namespace GoldbachSpectral
open ArithmeticFunction

/-- A point of the support of the coprime von Mangoldt correlation (1.3). -/
def GoodPair (N n m : ℕ) : Prop :=
  n + m = N ∧ (n * m).Coprime N ∧ IsPrimePow n ∧ IsPrimePow m

instance (N n m : ℕ) : Decidable (GoodPair N n m) := by unfold GoodPair; infer_instance

theorem goodPair_comm {N n m : ℕ} : GoodPair N n m ↔ GoodPair N m n := by
  unfold GoodPair
  rw [Nat.add_comm n m, Nat.mul_comm n m]
  tauto

/-- The exact coefficient, before the smooth weight and division by N. -/
noncomputable def coeff (N n : ℕ) : ℝ :=
  if (n * (N-n)).Coprime N then vonMangoldt n * vonMangoldt (N-n) else 0

theorem coeff_ne_zero_iff {N n : ℕ} (hn : n ≤ N) :
    coeff N n ≠ 0 ↔ GoodPair N n (N-n) := by
  have hs : n + (N - n) = N := by omega
  by_cases h : (n * (N-n)).Coprime N <;>
    simp [coeff, GoodPair, hs, h, vonMangoldt_ne_zero_iff]

/-- No admissible pair with either ordering at distance less than wN from N/2. -/
def EmptyWindow (N : ℕ) (w : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ N → |(n:ℝ) / N - 1/2| < w → ¬ GoodPair N n (N-n)

/-- The one-variable form of the weighted sum, restricted to the support n+m=N. -/
noncomputable def sample (N : ℕ) (F : ℝ → ℝ) : ℝ :=
  (∑ n ∈ Finset.range (N+1), coeff N n * F ((n:ℝ)/N)) / N

theorem sample_zero_of_empty {N : ℕ} {w : ℝ} {f g : ℝ → ℝ}
    (gap : EmptyWindow N w) (hs : ∀ u, w ≤ |u-1/2| → f u = 0) :
    sample N (fun u => f u * g u) = 0 := by
  unfold sample
  rw [Finset.sum_eq_zero, zero_div]
  intro n hn
  have hn' := Finset.mem_range.mp hn
  by_cases h : |(n:ℝ)/N-1/2| < w
  · have hz : coeff N n = 0 := by
      by_contra he
      exact gap n (by omega) h ((coeff_ne_zero_iff (by omega)).mp he)
    rw [hz, zero_mul]
  · simp only [hs _ (le_of_not_gt h), zero_mul, mul_zero]

def center (m : ℕ) : ℕ := m.factorial * (2*m.factorial+3)

private theorem plus_one_not_power (a : ℕ) (ha : 1 ≤ a) :
    ¬ IsPrimePow (a*(2*a+3)+1) := by
  have cop : (a+1).Coprime (2*a+1) := by
    by_contra hh
    obtain ⟨p,hp,h1,h2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
    have h3 : p ∣ 2*(a+1) := h1.trans (dvd_mul_left _ _)
    have h4 := Nat.dvd_sub h3 h2
    have h5 : 2*(a+1)-(2*a+1) = 1 := by omega
    rw [h5, Nat.dvd_one] at h4
    exact hp.ne_one h4
  have eqn : a*(2*a+3)+1 = (a+1)*(2*a+1) := by ring
  rw [eqn]
  intro h
  rcases (cop.isPrimePow_dvd_mul h).mp (dvd_refl _) with h1 | h2
  · have := Nat.le_of_dvd (by omega : 0 < a+1) h1
    nlinarith
  · have := Nat.le_of_dvd (by omega : 0 < 2*a+1) h2
    nlinarith

theorem factorial_gap (m j : ℕ) (hj : j ≤ m) :
    ¬ GoodPair (2*center m) (center m-j) (center m+j) := by
  intro h
  have hc : m.factorial ∣ center m := dvd_mul_right _ _
  have hbig : 2 ≤ center m := by
    have : 0 < m.factorial := Nat.factorial_pos m
    unfold center
    nlinarith
  obtain ⟨_,cop,_,pp⟩ := h
  have cop' := (Nat.coprime_mul_iff_left.mp cop).2
  rcases j with _ | _ | j
  · simp only [Nat.add_zero] at cop'
    have := Nat.eq_one_of_dvd_coprimes cop' (dvd_refl _) (dvd_mul_left _ _)
    omega
  · exact plus_one_not_power _ (Nat.factorial_pos m) pp
  · have d : j+2 ∣ center m := (Nat.dvd_factorial (by omega) hj).trans hc
    have := Nat.eq_one_of_dvd_coprimes cop' (dvd_add d (dvd_refl (j+2)))
      (d.trans (dvd_mul_left _ _))
    omega

theorem window_of_offsets {k r : ℕ} (hk : 0 < k)
    (gap : ∀ j : ℕ, j < r → ¬ GoodPair (2*k) (k-j) (k+j)) :
    EmptyWindow (2*k) ((r:ℝ)/(2*k)) := by
  intro n hn hd h
  push_cast at hd
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hk2 : (0:ℝ) < 2*k := by positivity
  rw [abs_lt] at hd
  have hu : (n:ℝ) < k+r := by
    have := (div_lt_iff₀ hk2).mp (show (n:ℝ)/(2*k) < r/(2*k) + 1/2 by linarith [hd.2])
    field_simp at this
    linarith
  have hl : (k:ℝ) < n+r := by
    have := (lt_div_iff₀ hk2).mp (show 1/2 - r/(2*k) < (n:ℝ)/(2*k) by linarith [hd.1])
    field_simp at this
    linarith
  have hu' : n < k+r := by exact_mod_cast hu
  have hl' : k < n+r := by exact_mod_cast hl
  by_cases hnk : n ≤ k
  · apply gap (k-n) (by omega)
    rw [show k-(k-n) = n by omega, show k+(k-n) = 2*k-n by omega]
    exact h
  · apply gap (n-k) (by omega)
    rw [show k-(n-k) = 2*k-n by omega, show k+(n-k) = n by omega]
    exact goodPair_comm.mp h

theorem factorial_window (m : ℕ) :
    EmptyWindow (2*center m) (((m+1:ℕ):ℝ)/(2*center m)) := by
  apply window_of_offsets
  · unfold center
    exact Nat.mul_pos (Nat.factorial_pos _) (by omega)
  · intro j hj
    exact factorial_gap m j (by omega)

end GoldbachSpectral

