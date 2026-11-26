module
public import SieveResidues
public import SieveEuler
public import Mathlib.NumberTheory.Primorial

/-! A two-dimensional Selberg upper bound with a uniform interval
remainder. The square is summed over the integers in the interval. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset MathlibNt.SieveTheory.LiuWeight
namespace GoldbachSpectral435.GoldbachSieve

def hit (a d : ℕ) : ℝ := if d∣a then 1 else 0

private lemma hit_mul (a d e : ℕ) : hit a d*hit a e=hit a (d.lcm e) := by
  unfold hit
  simp only [Nat.lcm_dvd_iff]
  split_ifs <;> simp_all

private lemma trimmed_main (S : BoundingSieve) (R : ℕ) (hr : 1≤R) :
    let D := truncatedSelbergCarrier S R
    let w := truncatedSelbergOptimalLambda S R
    (∑ d∈D, ∑ e∈D, w d*w e*S.nu (d.lcm e))=1/truncatedSelbergDenominator S R := by
  classical
  intro D w
  let U := S.prodPrimes.divisors
  have sub : D⊆U := filter_subset ..
  have zero {d : ℕ} (h : d∉D) : w d=0 := truncatedSelbergOptimalLambda_eq_zero_of_not_mem h
  have full : (∑ d∈D, ∑ e∈D, w d*w e*S.nu (d.lcm e))=∑ d∈U, ∑ e∈U, w d*w e*S.nu (d.lcm e) := by
    calc
      _ = ∑ d∈D, ∑ e∈U, w d*w e*S.nu (d.lcm e) :=
        sum_congr rfl (fun d _ => sum_subset sub (fun e _ h => by rw [zero h]; ring))
      _ = _ := sum_subset sub (fun d _ h => by simp [zero h])
  rw [full,← mainSum_truncatedSelbergOptimalLambda S hr,S.mainSum_lambdaSquared_eq_sum_sum_mul]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e _
  rw [S.nu_mult.map_lcm (S.nu_pos_of_dvd_prodPrimes
    ((Nat.gcd_dvd_left d e).trans (Nat.dvd_of_mem_divisors hd))).ne']
  dsimp only [w]
  ring

/-- Sift any finite sequence of values with a remainder at most E d in
each residue count. The total remainder is at most E R^4. -/
theorem interval_upper (S : BoundingSieve) (R : ℕ) (hr : 1≤R) (I : Finset ℕ) (a : ℕ→ℕ)
    (X E : ℝ) (ep : 0≤E)
    (error : ∀ d : ℕ, d∣S.prodPrimes → |(∑ n∈I, hit (a n) d)-X*S.nu d|≤E*d) :
    (∑ n∈I, if S.prodPrimes.Coprime (a n) then (1:ℝ) else 0)≤
      X/truncatedSelbergDenominator S R+E*(R:ℝ)^4 := by
  classical
  let D := truncatedSelbergCarrier S R
  let w := truncatedSelbergOptimalLambda S R
  let F := fun n d => w d*hit (a n) d
  have w1 : w 1=1 := truncatedSelbergOptimalLambda_one S hr
  have mem : 1∈D := mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _,S.prodPrimes_squarefree.ne_zero⟩,hr⟩
  have dv {d : ℕ} (h : d∈D) : d∣S.prodPrimes := Nat.dvd_of_mem_divisors (mem_filter.mp h).1
  have upper {d : ℕ} (h : d∈D) : d≤R := (mem_filter.mp h).2
  have cn : D.card≤R := by
    have sub : D⊆Icc 1 R := fun d h => mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (mem_filter.mp h).1,upper h⟩
    simpa using card_le_card sub
  have sieve (n : ℕ) : (if S.prodPrimes.Coprime (a n) then (1:ℝ) else 0)≤(∑ d∈D,F n d)^2 := by
    split_ifs with cop
    · have only : (∑ d∈D, F n d)=1 := by
        rw [sum_eq_single 1]
        · simp [F,hit,w1]
        · intro d hd ne
          have no : ¬d∣a n := fun t => ne (Nat.eq_one_of_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd (dv hd) t))
          simp [F,hit,no]
        · exact fun hm => False.elim (hm mem)
      simp [only]
    · exact sq_nonneg _
  have square (n : ℕ) : (∑ d∈D,F n d)^2=∑ d∈D,∑ e∈D,w d*w e*hit (a n) (d.lcm e) := by
    rw [sq,sum_mul]
    apply sum_congr rfl
    intro d _
    rw [mul_sum]
    apply sum_congr rfl
    intro e _
    rw [← hit_mul]
    dsimp [F]
    ring
  have exchange : (∑ n∈I, (∑ d∈D,F n d)^2)=∑ d∈D,∑ e∈D, w d*w e*(∑ n∈I,hit (a n) (d.lcm e)) := by
    simp_rw [square]
    rw [sum_comm]
    apply sum_congr rfl
    intro d _
    rw [sum_comm]
    exact sum_congr rfl (fun e _ => (mul_sum ..).symm)
  have pair {d e : ℕ} (hd : d∈D) (he : e∈D) :
      w d*w e*(∑ n∈I,hit (a n) (d.lcm e))≤X*(w d*w e*S.nu (d.lcm e))+E*(R:ℝ)^2 := by
    let m := d.lcm e
    let c := (∑ n∈I,hit (a n) m)-X*S.nu m
    have er : |c|≤E*m := error m (Nat.lcm_dvd_iff.mpr ⟨dv hd,dv he⟩)
    have coef : |w d*w e|≤1 := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (abs_truncatedSelbergOptimalLambda_le_one (d:=d) S hr)
        (abs_truncatedSelbergOptimalLambda_le_one (d:=e) S hr) (abs_nonneg _) zero_le_one
    have size : m≤R^2 := (Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_mem_divisors (mem_filter.mp hd).1)
      (Nat.pos_of_mem_divisors (mem_filter.mp he).1)) (Nat.lcm_dvd_mul d e)).trans
        (by rw [sq]; exact Nat.mul_le_mul (upper hd) (upper he))
    have cmp : w d*w e*c≤E*(R:ℝ)^2 := by
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right coef (abs_nonneg _)).trans
        (by rw [one_mul]; exact er.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast size) ep))
    dsimp only [c,m] at cmp
    linarith
  have m2 : (D.card:ℝ)^2≤(R:ℝ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast cn) 2
  apply (sum_le_sum (fun n _ => sieve n)).trans
  rw [exchange]
  apply (sum_le_sum (fun d hd => sum_le_sum (fun e he => pair hd he))).trans
  simp_rw [sum_add_distrib,← mul_sum]
  rw [trimmed_main S R hr]
  simp only [sum_const,nsmul_eq_mul]
  have errorTotal := mul_le_mul_of_nonneg_right m2 (show 0≤E*(R:ℝ)^2 by positivity)
  nlinarith only [errorTotal,show X*(1/truncatedSelbergDenominator S R)=X/truncatedSelbergDenominator S R by ring]

#print axioms interval_upper
end GoldbachSpectral435.GoldbachSieve
