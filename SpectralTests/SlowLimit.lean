module
public import SpectralTests.Widths

@[expose] public section
namespace GoldbachSpectral
open Filter

/-- Normalized decay along all even moduli. Under global GRH these are
precisely the moduli that enter the eventual spectral hypotheses. -/
def EvenDecay (M : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ N ≥ K, Even N → M N ≤ ε*singular N

/-- Exact scalar characterization of the existential, slowly growing choice of
h. The upper bound uses the actual singular series and the original width. -/
theorem some_width_iff_decay (M : ℕ → ℝ) (positive : ∀ N, 0 ≤ M N) :
    (∃ h : ℕ → ℝ, Admissible h ∧ ∃ K : ℕ, ∀ N ≥ K, Even N →
      Sbound (deltaSq N (singular N)) (M N) (width N (singular N) (h N))) ↔ EvenDecay M := by
  have spos (n : ℕ) : 0 < singular n := zero_lt_one.trans_le (singular_lower n)
  constructor
  · rintro ⟨h,⟨hp,hi,hw⟩,K,test⟩ ε hε
    obtain ⟨A,hA⟩ := hi (1/ε)
    obtain ⟨B,hB⟩ := hw
    refine ⟨max 4 (max K (max A B)),fun n hn he => ?_⟩
    have pos := hp n he (by omega)
    have sq := S_implies_normalized_bound (by omega : 1<n) (spos n) pos (hB n (by omega) he)
      (test n (by omega) he)
    have hh : h n * M n ≤ singular n := by
      have t := sq_nonneg (h n*M n)
      by_contra! bad
      have inc := mul_self_lt_mul_self (spos n).le bad
      nlinarith
    have hh' : 1 ≤ h n*ε := (div_le_iff₀ hε).mp (hA n (by omega) he)
    have a := mul_le_mul_of_nonneg_right hh' (positive n)
    have b := mul_le_mul_of_nonneg_left hh hε.le
    nlinarith only [a,b]
  · intro decay
    let U := prescribedH 0
    obtain ⟨uPos,uLim,uWidth⟩ := prescribed_admissible 0
    let h := fun n => (singular n)/(2*(M n + singular n / U n))
    have denom (n : ℕ) : 0 < 2*(M n + singular n/U n) := by
      have := positive n
      have := spos n
      have hu : 0 < U n := uPos n
      positivity
    have id (n : ℕ) : h n * (2*(M n + singular n/U n)) = singular n :=
      div_mul_cancel₀ _ (denom n).ne'
    have hpos (n : ℕ) : 0 < h n := div_pos (spos n) (denom n)
    have cap (n : ℕ) : h n ≤ U n := by
      apply (div_le_iff₀ (denom n)).mpr
      have hu := uPos n
      change 0 < U n at hu
      have eq : U n*(singular n/U n) = singular n := mul_div_cancel₀ _ hu.ne'
      nlinarith [mul_nonneg hu.le (positive n),spos n]
    have product (n : ℕ) : 2*h n*M n ≤ singular n := by
      nlinarith [id n, mul_nonneg (hpos n).le (div_pos (spos n) (uPos n)).le]
    have limit (t : ℝ) : ∃ K : ℕ, ∀ n ≥ K, Even n → t ≤ h n := by
      let B := max t 1
      have bp : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
      obtain ⟨K,hK⟩ := decay (1/(4*B)) (by positivity)
      obtain ⟨J,hJ⟩ := eventually_atTop.mp (uLim.eventually_ge_atTop (4*B))
      refine ⟨max K J,fun n hn he => ?_⟩
      have m := hK n (by omega) he
      have u : 4*B ≤ U n := hJ n (by omega)
      have v : singular n/U n ≤ singular n/(4*B) :=
        div_le_div_of_nonneg_left (spos n).le (by positivity) u
      apply (le_max_left t 1).trans
      apply (le_div_iff₀ (denom n)).mpr
      have m' : M n ≤ singular n/(4*B) := by simpa [div_eq_mul_inv,mul_comm] using m
      have total := add_le_add m' v
      have exact' : B * (2*(singular n/(4*B)+singular n/(4*B))) = singular n := by field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_left total bp.le]
    obtain ⟨J,hJ⟩ := eventually_atTop.mp uWidth
    have wcap (n : ℕ) (hn : 2 ≤ n) : width n (singular n) (h n) ≤ width n (singular n) (U n) := by
      have ln := Real.log_pos (by exact_mod_cast (show 1<n by omega) : (1:ℝ)<n)
      unfold width
      apply div_le_div_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (spos n).le)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hpos n).le (cap n) 2) (pow_nonneg ln.le 3)
    refine ⟨h,⟨fun n _ _ => hpos n,limit,⟨max J 2,fun n hn _ => (wcap n (by omega)).trans (hJ n (by omega))⟩⟩,
      2,fun n hn _ => ?_⟩
    have np : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have lpos := Real.log_pos (by exact_mod_cast (show 1<n by omega) : (1:ℝ)<n)
    have s := spos n
    have epos : 0 ≤ width n (singular n) (h n) := by unfold width; positivity
    have sq := pow_le_pow_left₀ (mul_nonneg (by linarith [hpos n] : 0 ≤ 2*h n) (positive n)) (product n) 2
    unfold Sbound
    calc
      _ ≤ 4*width n (singular n) (h n)*M n^2 := by
        nlinarith [mul_nonneg (sq_nonneg (width n (singular n) (h n))) (sq_nonneg (M n))]
      _ ≤ deltaSq n (singular n) := by
        unfold width deltaSq
        field_simp
        nlinarith [mul_le_mul_of_nonneg_right sq (pow_nonneg lpos.le 3)]

end GoldbachSpectral
