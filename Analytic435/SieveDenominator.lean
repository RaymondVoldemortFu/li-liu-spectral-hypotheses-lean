module
public import MathlibNt.SieveTheory.Selberg.TruncatedOptimalWeights
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Data.Nat.Factorization.Basic

/-! Elementary estimates for the two forbidden residue classes 0 and N
in the upper-bound sieve for a Goldbach interval. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators
namespace GoldbachSpectral435.GoldbachSieve

/-- The elementary factorial bound for the logarithmic size of the
local sieve densities. It holds for every subset of the primes up to z. -/
theorem prime_log_sum (z : ℕ) (zp : 0<z) (P : Finset ℕ)
    (prime : ∀ p∈P, p.Prime) (small : ∀ p∈P, p≤z) :
    (∑ p∈P, Real.log p/(p:ℝ))≤2*Real.log z := by
  let I := Ioc 0 z
  have zreal : 0<(z:ℝ) := by exact_mod_cast zp
  have per (p : ℕ) (hp : p∈P) :
      (z:ℝ)*(Real.log p/p)≤2*(((z/p:ℕ):ℝ)*Real.log p) := by
    have pp := (prime p hp).pos
    have pos : 0<(p:ℝ) := by exact_mod_cast pp
    have one : 1≤z/p := (Nat.one_le_div_iff pp).mpr (small p hp)
    have size : z≤2*(z/p)*p := by
      have rem := Nat.mod_lt z pp
      have id := Nat.div_add_mod z p
      have m := Nat.mul_le_mul_left p one
      nlinarith
    have sz : (z:ℝ)≤2*((z/p:ℕ):ℝ)*p := by exact_mod_cast size
    have logp := Real.log_nonneg (show (1:ℝ)≤p by exact_mod_cast pp)
    calc
      _ = ((z:ℝ)/p)*Real.log p := by ring
      _ ≤ (2*((z/p:ℕ):ℝ))*Real.log p := mul_le_mul_of_nonneg_right ((div_le_iff₀ pos).mpr sz) logp
      _ = _ := by ring
  have count (p : ℕ) :
      (((z/p:ℕ):ℝ)*Real.log p)=∑ n∈I, if p∣n then Real.log p else 0 := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]
    congr 2
    exact_mod_cast (Nat.Ioc_filter_dvd_card_eq_div z p).symm
  have atn (n : ℕ) (hn : n∈I) : (∑ p∈P, if p∣n then Real.log p else 0)≤Real.log z := by
    have np : 0<n := (mem_Ioc.mp hn).1
    let S := P.filter (fun p => p∣n)
    have pr : ∀ p∈S, p.Prime := fun p hp => prime p (mem_filter.mp hp).1
    have prod := Finset.prod_primes_dvd n (fun p hp => (pr p hp).prime) (fun p hp => (mem_filter.mp hp).2)
    have pos : 0<∏ p∈S,p := prod_pos (fun p hp => (pr p hp).pos)
    have upper : ∏ p∈S, p≤z := (Nat.le_of_dvd np prod).trans (mem_Ioc.mp hn).2
    rw [← sum_filter]
    change (∑ p∈S, Real.log p)≤Real.log z
    rw [← Real.log_prod (fun p (hp : p∈S) => (Nat.cast_pos.mpr (pr p hp).pos : 0<(p:ℝ)).ne'),← Nat.cast_prod]
    exact Real.log_le_log (by exact_mod_cast pos) (by exact_mod_cast upper)
  have total : (z:ℝ)*(∑ p∈P, Real.log p/(p:ℝ))≤2*((z:ℝ)*Real.log z) := by
    calc
      _ = ∑ p∈P, (z:ℝ)*(Real.log p/p) := mul_sum ..
      _ ≤ ∑ p∈P, 2*(((z/p:ℕ):ℝ)*Real.log p) := sum_le_sum per
      _ = 2*∑ n∈I, ∑ p∈P, if p∣n then Real.log p else 0 := by
        simp_rw [count]
        rw [← mul_sum,sum_comm]
      _ ≤ 2*∑ _n∈I, Real.log z := mul_le_mul_of_nonneg_left (sum_le_sum atn) (by norm_num)
      _ = _ := by simp [I]
  apply le_of_mul_le_mul_left _ zreal
  exact total.trans_eq (by ring)

/-- Multiplying the Euler weights by log of their squarefree index has
a finite exact first moment. -/
theorem subset_moment (S : Finset ℕ) (w b : ℕ→ℝ) (pos : ∀ p∈S, 0≤w p) :
    (∑ T∈S.powerset, (∏ p∈T, w p)*(∑ p∈T, b p))=
      (∏ p∈S, (1+w p))*(∑ p∈S, w p*b p/(1+w p)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have ok := ih (fun q hq => pos q (mem_insert_of_mem hq))
    have sp := pos p (mem_insert_self ..)
    have pp : 1+w p≠0 := by linarith
    rw [sum_powerset_insert hp,prod_insert hp,sum_insert hp]
    have addterm (T : Finset ℕ) (ht : T∈S.powerset) :
        (∏ q∈insert p T, w q)*(∑ q∈insert p T, b q)=
        (w p*b p)*(∏ q∈T, w q)+w p*((∏ q∈T, w q)*(∑ q∈T, b q)) := by
      have no := notMem_mono (mem_powerset.mp ht) hp
      rw [prod_insert no,sum_insert no]
      ring
    rw [sum_congr rfl addterm,sum_add_distrib,← mul_sum,← mul_sum,ok,← prod_one_add]
    field_simp
    ring

def localDensity (N p : ℕ) : ℝ := (if p∣N then 1 else 2)/(p:ℝ)

lemma density_range (N p : ℕ) (even : Even N) (hp : p.Prime) :
    0<localDensity N p ∧ localDensity N p<1 := by
  have pp : 0<(p:ℝ) := by exact_mod_cast hp.pos
  unfold localDensity
  split_ifs with h
  · exact ⟨by positivity,(div_lt_one pp).mpr (by exact_mod_cast hp.one_lt)⟩
  · have neq : p≠2 := by rintro rfl; exact h (even_iff_two_dvd.mp even)
    exact ⟨by positivity,(div_lt_one pp).mpr (by exact_mod_cast (show 2<p by have := hp.two_le; omega))⟩

theorem density_log_sum (N z : ℕ) (zp : 0<z) (P : Finset ℕ) (pr : ∀ p∈P, p.Prime)
    (sm : ∀ p∈P, p≤z) : (∑ p∈P, localDensity N p*Real.log p)≤4*Real.log z := by
  have cap (p : ℕ) (hp : p∈P) : localDensity N p*Real.log p≤2*(Real.log p/p) := by
    have lg := Real.log_nonneg (show (1:ℝ)≤p by exact_mod_cast (pr p hp).pos)
    have up : localDensity N p≤2/p := by
      unfold localDensity
      split_ifs
      · gcongr; norm_num
      · rfl
    exact (mul_le_mul_of_nonneg_right up lg).trans_eq (by ring)
  exact (sum_le_sum cap).trans (by rw [← mul_sum]; linarith only [prime_log_sum z zp P pr sm])

def odds (N p : ℕ) : ℝ := localDensity N p/(1-localDensity N p)

/-- At least one half of the mass of the full product of Selberg factors
already comes from squarefree indices at most z^8. The estimate is uniform
in the even integer and in the chosen subset of the primes. -/
theorem retained_mass (N z R : ℕ) (ev : Even N) (zp : 1<z) (level : z^8≤R)
    (P : Finset ℕ) (pr : ∀ p∈P, p.Prime) (sm : ∀ p∈P, p≤z) :
    (∏ p∈P, (1+odds N p))/2 ≤
      ∑ T∈P.powerset, if (∏ p∈T,p)≤R then ∏ p∈T, odds N p else 0 := by
  classical
  let w := odds N
  let mass := fun T : Finset ℕ => ∏ p∈T, w p
  let d := fun T : Finset ℕ => ∏ p∈T,p
  let Z := ∏ p∈P,(1+w p)
  have wp (p : ℕ) (hp : p∈P) : 0≤w p := (div_pos (density_range _ _ ev (pr p hp)).1
    (sub_pos.mpr (density_range _ _ ev (pr p hp)).2)).le
  have all (T : Finset ℕ) (h : T∈P.powerset) := mem_powerset.mp h
  have mp (T : Finset ℕ) (h : T∈P.powerset) : 0≤mass T := prod_nonneg (fun p hp => wp p (all T h hp))
  have score (p : ℕ) (hp : p∈P) :
      w p*Real.log p/(1+w p)=localDensity N p*Real.log p := by
    have hr := (density_range _ _ ev (pr p hp)).2
    have nz : 1-localDensity N p≠0 := (sub_pos.mpr hr).ne'
    dsimp [w,odds]
    field_simp
    ring
  have zpos : 0≤Z := prod_nonneg (fun p hp => by linarith [wp p hp])
  have moment : (∑ T∈P.powerset, mass T*(∑ p∈T, Real.log p))≤Z*(4*Real.log z) := by
    change (∑ T∈P.powerset, (∏ p∈T,w p)*(∑ p∈T, Real.log p))≤_
    rw [subset_moment P w _ wp,sum_congr rfl score]
    exact mul_le_mul_of_nonneg_left (density_log_sum N z (by omega) P pr sm) zpos
  have logz : 0<Real.log z := Real.log_pos (by exact_mod_cast zp)
  have tail (T : Finset ℕ) (h : T∈P.powerset) :
      (8*Real.log z)*(if d T≤R then 0 else mass T)≤mass T*(∑ p∈T, Real.log p) := by
    split_ifs with small
    · rw [mul_zero]
      exact mul_nonneg (mp T h) (sum_nonneg fun p hp => Real.log_nonneg (by exact_mod_cast (pr p (all T h hp)).pos))
    · have bound : z^8≤d T := level.trans (le_of_lt (lt_of_not_ge small))
      have dx : 0<(z:ℝ)^8 := by positivity
      have q : Real.log ((z:ℝ)^8)≤Real.log (d T) := Real.log_le_log dx (by exact_mod_cast bound)
      rw [Real.log_pow] at q
      have lg : Real.log (d T)=∑ p∈T, Real.log p := by
        dsimp [d]
        rw [Nat.cast_prod]
        exact Real.log_prod (s:=T) (f:=fun p : ℕ => (p:ℝ)) (fun p hp => (Nat.cast_pos.mpr (pr p (all T h hp)).pos).ne')
      rw [lg] at q
      simpa only [mul_comm (8*Real.log _),Nat.cast_ofNat] using mul_le_mul_of_nonneg_left q (mp T h)
  have b := (sum_le_sum tail).trans moment
  rw [← mul_sum] at b
  have tbound : (∑ T∈P.powerset, if d T≤R then 0 else mass T)≤Z/2 := by
    apply le_of_mul_le_mul_left _ (show 0<8*Real.log z by positivity)
    exact b.trans_eq (by ring)
  have split : (∑ T∈P.powerset, if d T≤R then mass T else 0)+
      (∑ T∈P.powerset, if d T≤R then 0 else mass T)=Z := by
    rw [← sum_add_distrib]
    exact (sum_congr rfl (fun T _ => by split_ifs <;> simp [mass])).trans (prod_one_add P).symm
  change Z/2≤∑ T∈P.powerset, if d T≤R then mass T else 0
  linarith

open MathlibNt.SieveTheory.LiuWeight

/-- The denominator of the actual truncated Selberg optimizer dominates
half of the Euler product for the two Goldbach residue classes. -/
theorem selberg_lower (N z R : ℕ) (ev : Even N) (zp : 1<z) (level : z^8≤R)
    (P : Finset ℕ) (pr : ∀ p∈P, p.Prime) (sm : ∀ p∈P, p≤z) (S : BoundingSieve)
    (dv : ∀ p∈P, p∣S.prodPrimes) (nu : ∀ p∈P, S.nu p=localDensity N p) :
    (∏ p∈P, (1+odds N p))/2 ≤truncatedSelbergDenominator S R := by
  classical
  let d := fun T : Finset ℕ => ∏ p∈T,p
  let Q := P.powerset.filter (fun T => d T≤R)
  have sub (T : Finset ℕ) (h : T∈Q) : T⊆P := mem_powerset.mp (mem_filter.mp h).1
  have image : Q.image d⊆truncatedSelbergCarrier S R := by
    intro n hn
    obtain ⟨T,h,rfl⟩ := mem_image.mp hn
    have di := Finset.prod_primes_dvd S.prodPrimes (fun p hp => (pr p (sub T h hp)).prime) (fun p hp => dv p (sub T h hp))
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨di,S.prodPrimes_squarefree.ne_zero⟩,(mem_filter.mp h).2⟩
  have inject : Set.InjOn d (↑Q) := by
    intro T h V j eq
    have first := Nat.primeFactors_prod (fun p hp => pr p (sub T h hp))
    have second := Nat.primeFactors_prod (fun p hp => pr p (sub V j hp))
    exact first.symm.trans ((congrArg Nat.primeFactors eq).trans second)
  have atPrime (p : ℕ) (hp : p∈P) : S.selbergTerms p=odds N p := by
    rw [S.selbergTerms_apply,(pr p hp).primeFactors,prod_singleton,nu p hp]
    rfl
  have fact (T : Finset ℕ) (h : T∈Q) : (∏ p∈T, odds N p)=S.selbergTerms (d T) := by
    rw [show S.selbergTerms (d T)=∏ p∈T, S.selbergTerms p from
      S.selbergTerms_isMultiplicative.map_prod_of_prime T (fun p hp => pr p (sub T h hp))]
    exact prod_congr rfl (fun p hp => (atPrime p (sub T h hp)).symm)
  have before := retained_mass N z R ev zp level P pr sm
  apply before.trans
  change (∑ T∈P.powerset, if d T≤R then ∏ p∈T, odds N p else 0)≤_
  rw [← sum_filter]
  change (∑ T∈Q, ∏ p∈T, odds N p)≤_
  rw [sum_congr rfl fact,← sum_image inject]
  exact sum_le_sum_of_subset_of_nonneg image (fun n hn _ =>
    (S.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hn).1)).le)

#print axioms selberg_lower
#print axioms retained_mass
#print axioms density_log_sum
end GoldbachSpectral435.GoldbachSieve
