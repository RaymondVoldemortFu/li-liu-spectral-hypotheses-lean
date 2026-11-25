module
public import PhysicalAP
public import Opposite
public import SpectralTests.BandPrimes

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Chebyshev Finset Set
namespace GoldbachSpectral435

/-- A uniform bound for all prime powers discarded by parity, a nonunit
progression, or a gcd condition. The majorant is an ordinary Chebyshev sum. -/
theorem exceptional_mass (M : ℕ) (hm : 0<M) (s : Finset ℕ) (W : ℕ → ℝ)
    (cut : ∀ n∈s,n≤M) (weight : ∀ n∈s, W n≤1)
    (noPrime : ∀ n∈s,n.Prime → W n=0) :
    ∑ n∈s,mangoldt n*W n ≤ 2*Real.sqrt M*Real.log M := by
  classical
  let A := (Finset.Ioc 0 M).filter (fun n => ¬n.Prime)
  have z (n : ℕ) (hn : n∈s) (out : n∉A) : mangoldt n*W n ≤ 0 := by
    by_cases p : n.Prime
    · simp [noPrime n hn p]
    · have nz : n=0 := by
        by_contra nz
        exact out (mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.pos_of_ne_zero nz,cut n hn⟩,p⟩)
      simp [nz,mangoldt]
  calc
    _ ≤ ∑ n∈s,if n∈A then mangoldt n else 0 := by
      apply sum_le_sum
      intro n hn
      split
      · exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (weight _ hn)
      · exact z _ hn (by assumption)
    _ = ∑ n∈s.filter (·∈A),mangoldt n := (sum_filter ..).symm
    _ ≤ ∑ n∈A,mangoldt n := sum_le_sum_of_subset_of_nonneg (fun n hn => (mem_filter.mp hn).2)
      (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = psi M-theta M := by simpa [A] using (psi_sub_theta_eq_sum_not_prime (M:ℝ)).symm
    _ ≤ _ := psi_sub_theta_le (by exact_mod_cast hm)

theorem missing_coprime (M q : ℕ) (hm : 0<M) (hq : 0<q) (s : Finset ℕ) (W : ℕ → ℝ)
    (cut : ∀ n∈s,n≤M) (weight : ∀ n∈s,W n≤1) (low : ∀ n∈s,n≤q → W n=0) :
    (∑ n∈s,if n.Coprime q then 0 else mangoldt n*W n) ≤ 2*Real.sqrt M*Real.log M := by
  classical
  let f := fun n => if n.Coprime q then 0 else W n
  have h := exceptional_mass M hm s f cut (fun n hn => by
    dsimp [f]; split <;> first | exact zero_le_one | exact weight n hn) (fun n hn p => by
      dsimp [f]
      split
      · rfl
      next bad =>
        have dvd : n∣q := Classical.not_not.mp (fun no => bad (p.coprime_iff_not_dvd.mpr no))
        exact low n hn (Nat.le_of_dvd hq dvd))
  apply le_trans _ h
  apply sum_le_sum
  intro n _
  dsimp [f]; split_ifs <;> simp

def restrictedMass (q M m : ℕ) (t : ZMod q) (f : ℝ → ℝ) : ℝ :=
  ∑ n∈range M, if (n:ZMod q)=t ∧ n.Coprime m then weightedMangoldt M n f else 0

private theorem small_broad (M n : ℕ) (mp : 0<M) (low : 4*n≤M) : broad (n/(M:ℝ))=0 := by
  by_contra nz
  have p := (broad_support nz).1
  have hr : 4*(n:ℝ)≤M := by exact_mod_cast low
  have r := (lt_div_iff₀ (show 0<(M:ℝ) by exact_mod_cast mp)).mp p
  linarith

theorem class_all (q M m : ℕ) [NeZero q] (mp : 0<M) (smallq : 4*q≤M) (smallm : 4*m≤M)
    (mpos : 0<m) (t : ZMod q) (E : ℝ) (ep : 0≤E)
    (ap : IsUnit t → |classMass q M t broad-principalMass q M broad/q.totient|≤E) :
    |restrictedMass q M m t broad-(if IsUnit t then principalMass q M broad/q.totient else 0)| ≤
      E+2*Real.sqrt M*Real.log M := by
  classical
  let s := (range M).filter (fun n : ℕ => (n:ZMod q)=t)
  let W := fun n : ℕ => broad (n/(M:ℝ))
  have cut (n : ℕ) (hn : n∈s) : n≤M := (mem_range.mp (mem_filter.mp hn).1).le
  have w (n : ℕ) : 0≤weightedMangoldt M n broad := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg broad.nonneg
  have sum0 : classMass q M t broad = ∑ n∈s,weightedMangoldt M n broad := by simp only [classMass,s,sum_filter]
  have sum1 : restrictedMass q M m t broad =
      ∑ n∈s,if n.Coprime m then weightedMangoldt M n broad else 0 := by
    simp only [restrictedMass,s,sum_filter]; apply sum_congr rfl
    intro n _; split_ifs <;> simp_all
  have nonneg : 0≤restrictedMass q M m t broad := by
    rw [sum1]; exact sum_nonneg (fun n _ => by split <;> first | exact w n | exact le_rfl)
  have less : restrictedMass q M m t broad≤classMass q M t broad := by
    rw [sum1,sum0]; exact sum_le_sum (fun n _ => by split <;> first | exact le_rfl | exact w n)
  by_cases unit : IsUnit t
  · rw [ite_eq_left unit]
    have loss := missing_coprime M m mp mpos s W cut (fun _ _ => broad.le_one)
      (fun n _ low => small_broad M n mp (by omega))
    have diff : classMass q M t broad-restrictedMass q M m t broad =
        ∑ n∈s,if n.Coprime m then 0 else mangoldt n*W n := by
      rw [sum0,sum1,← sum_sub_distrib]
      apply sum_congr rfl
      intro n _; split_ifs <;> simp [weightedMangoldt,W]
    rw [← diff] at loss
    obtain ⟨lo,hi⟩ := abs_le.mp (ap unit)
    have logpos : 0≤Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤M by omega))
    have ex : 0≤2*Real.sqrt (M:ℝ)*Real.log M := by positivity
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · rw [ite_eq_right unit,sub_zero,abs_of_nonneg nonneg]
    have thin := exceptional_mass M mp s W cut (fun _ _ => broad.le_one) (fun n hn prim => by
      have bad : ¬n.Coprime q := fun c => unit ((mem_filter.mp hn).2 ▸ (ZMod.isUnit_iff_coprime n q).mpr c)
      have dvd : n∣q := Classical.not_not.mp (fun no => bad (prim.coprime_iff_not_dvd.mpr no))
      exact small_broad M n mp (by have l := Nat.le_of_dvd (NeZero.pos q) dvd; omega))
    rw [sum0] at less
    exact less.trans (thin.trans (by linarith))

/-- Uniform lower bound for the common principal term. All the primes in
the interior interval exceed the progression modulus. -/
theorem principal_lower : ∃ K : ℕ, ∀ M≥K, ∀ q : ℕ, 0<q → 4*q≤M → (M:ℝ)/16≤principalMass q M broad := by
  obtain ⟨X,P⟩ := GoldbachSpectral.BandSieve.prime_mass_windows (c := 1/4) (C := 3) (by norm_num) (by norm_num)
  obtain ⟨K,large⟩ := exists_nat_gt (max (4*X) 16)
  refine ⟨K,?_⟩
  intro M hM q qp small
  have mk : (K:ℝ)≤M := by exact_mod_cast hM
  have mp : 0<(M:ℝ) := by linarith [lt_of_le_of_lt (le_max_right _ _) large]
  let a : ℝ := 7*M/16
  let b : ℝ := 9*M/16
  have ap : 0<a := by dsimp [a]; positivity
  have bp : 0<b := by dsimp [b]; positivity
  have ab : a≤b := by dsimp [a,b]; linarith
  have m := P (M/4) (by linarith [lt_of_le_of_lt (le_max_left _ _) large]) a b
    (by dsimp [a]; linarith) ab (by dsimp [b]; linarith) (by dsimp [a,b]; linarith)
  let I := Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊
  have sub : Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊b⌋₊ := fun n hn =>
    Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hn).1.trans (Nat.floor_mono ab),(Nat.mem_primesLE.mp hn).2⟩
  have diff : theta b-theta a=∑ n∈I,Real.log n := by
    rw [theta_eq_sum_primesLE,theta_eq_sum_primesLE,sub_eq_iff_eq_add]
    exact (sum_sdiff sub).symm
  rw [diff] at m
  have info (n : ℕ) (hn : n∈I) : a<(n:ℝ) ∧ (n:ℝ)≤b ∧ n.Prime := by
    obtain ⟨up,down⟩ := mem_sdiff.mp hn
    obtain ⟨le,p⟩ := Nat.mem_primesLE.mp up
    exact ⟨(Nat.floor_lt ap.le).mp (lt_of_not_ge (fun h => down (Nat.mem_primesLE.mpr ⟨h,p⟩))),
      (Nat.le_floor_iff bp.le).mp le,p⟩
  have inc : I ⊆ range M := by
    intro n hn
    have u := (info n hn).2.1
    dsimp [b] at u
    exact mem_range.mpr (by exact_mod_cast (by linarith : (n:ℝ)<M))
  have hit (n : ℕ) (hn : n∈I) : Real.log n = if n.Coprime q then weightedMangoldt M n broad else 0 := by
    obtain ⟨l,u,p⟩ := info n hn
    dsimp [a] at l
    dsimp [b] at u
    have qr : 4*(q:ℝ)≤M := by exact_mod_cast small
    have nq : q<n := by exact_mod_cast (by linarith : (q:ℝ)<n)
    have cp := p.coprime_iff_not_dvd.mpr (fun dv => (not_le_of_gt nq) (Nat.le_of_dvd qp dv))
    rw [ite_eq_left cp,weightedMangoldt,ArithmeticFunction.vonMangoldt_apply_prime p,broad.one_of_mem_closedBall,mul_one]
    rw [Metric.mem_closedBall,Real.dist_eq,abs_le]
    change -(1/16:ℝ)≤(n:ℝ)/M-1/2 ∧ (n:ℝ)/M-1/2≤1/16
    have L := (le_div_iff₀ mp).mpr (by linarith : 7/16*(M:ℝ)≤n)
    have U := (div_le_iff₀ mp).mpr (by linarith : (n:ℝ)≤9/16*M)
    constructor <;> linarith
  change _ ≤ ∑ n∈range M,if n.Coprime q then weightedMangoldt M n broad else 0
  apply (show (M:ℝ)/16≤∑ n∈I,Real.log n by dsimp only [a,b] at m; linarith only [m]).trans
  rw [sum_congr rfl hit]
  exact sum_le_sum_of_subset_of_nonneg inc (fun n _ _ => by
    split <;> first | exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg broad.nonneg | exact le_rfl)

#print axioms principal_lower
#print axioms class_all
#print axioms exceptional_mass
#print axioms missing_coprime
end GoldbachSpectral435

