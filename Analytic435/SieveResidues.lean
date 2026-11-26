module
public import SieveDenominator
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! Complete and incomplete periods for the two Goldbach residue classes. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset
namespace GoldbachSpectral435.GoldbachSieve

def root (N d : ℕ) (x : ZMod d) : Prop := x*(x-N)=0

def roots (N d : ℕ) [NeZero d] : Finset (ZMod d) := by classical exact univ.filter (root N d)

@[simp] lemma mem_roots {N d : ℕ} [NeZero d] (x : ZMod d) : x∈roots N d ↔ root N d x := by
  classical simp [roots]

theorem root_card_prime (N p : ℕ) (hp : p.Prime) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (roots N p).card=if p∣N then 1 else 2 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : NeZero p := ⟨hp.ne_zero⟩
  classical
  have eq : roots N p={0,(N:ZMod p)} := by ext x; simp [root,mul_eq_zero,sub_eq_zero]
  rw [eq]
  by_cases h : p∣N
  · simp [(ZMod.natCast_eq_zero_iff N p).mpr h,h]
  · have ne : (N:ZMod p)≠0 := mt (ZMod.natCast_eq_zero_iff N p).mp h
    rw [ite_eq_right h,card_pair_eq_two_iff]
    exact ne.symm

theorem root_card_mul (N d e : ℕ) [NeZero d] [NeZero e] (cop : d.Coprime e) :
    (roots N (d*e)).card=(roots N d).card*(roots N e).card := by
  classical
  let r := ZMod.chineseRemainder cop
  have eq (x : ZMod (d*e)) : root N (d*e) x ↔ root N d (r x).1 ∧ root N e (r x).2 := by
    unfold root
    rw [← r.injective.eq_iff (a:=x*(x-N)) (b:=0)]
    simp only [map_mul,map_sub,map_natCast,map_zero,Prod.ext_iff,Prod.fst_mul,Prod.snd_mul,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_natCast,Prod.snd_natCast,Prod.fst_zero,Prod.snd_zero]
  rw [← card_product]
  apply card_bij (fun x _ => r x)
  · intro x hx
    simpa only [mem_product,mem_roots] using (eq x).mp (mem_roots x |>.mp hx)
  · intro x _ y _ h
    exact r.injective h
  · intro y hy
    refine ⟨r.symm y,(mem_roots _).mpr ((eq _).mpr ?_),r.apply_symm_apply _⟩
    simpa only [r.apply_symm_apply,mem_product,mem_roots] using hy

def density (N : ℕ) : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (localDensity N)

lemma density_prime (N p : ℕ) (hp : p.Prime) : density N p=localDensity N p := by
  simp [density,ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,hp.primeFactors]

theorem density_mult (N : ℕ) : (density N).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

private lemma card_congr (N : ℕ) {a b : ℕ} [NeZero a] [NeZero b] (h : a=b) :
    (roots N a).card=(roots N b).card := by subst b; rfl

theorem root_card_density (N d : ℕ) [NeZero d] (sq : Squarefree d) :
    ((roots N d).card:ℝ)=(d:ℝ)*density N d := by
  classical
  let f := fun T : Finset ℕ => ∏ p∈T,p
  have aux (T : Finset ℕ) (pr : ∀ p∈T, p.Prime) :
      letI : NeZero (f T) := ⟨(prod_pos fun p hp => (pr p hp).pos).ne'⟩
      ((roots N (f T)).card:ℝ)=(f T:ℝ)*density N (f T) := by
    induction T using Finset.induction_on with
    | empty =>
      have eq : roots N 1=univ := by ext x; rw [mem_roots]; exact iff_of_true (Subsingleton.elim _ _) (mem_univ _)
      simp [f,eq,(density_mult N).map_one]
    | @insert p T hp ih =>
      have prT : ∀ q∈T, q.Prime := fun q h => pr q (mem_insert_of_mem h)
      have pp := pr p (mem_insert_self ..)
      let _ : NeZero p := ⟨pp.ne_zero⟩
      let _ : NeZero (f T) := ⟨(prod_pos fun q h => (prT q h).pos).ne'⟩
      have cop : p.Coprime (f T) := Nat.Coprime.prod_right (fun q h =>
        (Nat.coprime_primes pp (prT q h)).mpr (fun eq => hp (eq ▸ h)))
      let r := f T
      have work : ((roots N (p*r)).card:ℝ)=((p*r:ℕ):ℝ)*density N (p*r) := by
        rw [root_card_mul N p r cop,Nat.cast_mul,root_card_prime N p pp,ih prT,
          (density_mult N).map_mul_of_coprime cop,density_prime N p pp,Nat.cast_mul]
        have nz : (p:ℝ)≠0 := by exact_mod_cast pp.ne_zero
        unfold localDensity
        split_ifs <;> push_cast <;> field_simp <;> ring
      have eq : f (insert p T)=p*r := prod_insert hp
      let _ : NeZero (f (insert p T)) := ⟨(prod_pos fun p hp => (pr p hp).pos).ne'⟩
      rw [card_congr N eq,eq]
      exact work
  have e := Nat.prod_primeFactors_of_squarefree sq
  have h := aux d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  let _ : NeZero (f d.primeFactors) := ⟨(prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos).ne'⟩
  have e' : f d.primeFactors=d := e
  rw [card_congr N e',e'] at h
  exact h

/-- The incomplete interval [0,Y) counts roots of x(x-N) modulo d. -/
def rootCount (N d Y : ℕ) : ℕ := by classical exact ((range Y).filter (fun n : ℕ => root N d (n:ZMod d))).card

private lemma root_sum (N d Y : ℕ) :
    rootCount N d Y=∑ n∈range Y, if (n:ZMod d)*(n-N)=0 then (1:ℕ) else 0 := by
  classical
  unfold rootCount
  rw [← sum_filter,sum_const,nsmul_eq_mul,Nat.mul_one]
  congr 1
  apply Finset.filter_congr
  intro x _
  rfl

lemma root_sum_real (N d Y : ℕ) :
    (rootCount N d Y:ℝ)=∑ n∈range Y, if (n:ZMod d)*(n-N)=0 then (1:ℝ) else 0 := by
  rw [root_sum]
  push_cast
  rfl

private lemma root_period (N d : ℕ) [NeZero d] : rootCount N d d=(roots N d).card := by
  classical
  unfold rootCount
  apply card_bij (fun (n : ℕ) _ => (n:ZMod d))
  · intro n h; exact (mem_roots _).mpr (mem_filter.mp h).2
  · intro n hn j hj eq
    have v := congrArg ZMod.val eq
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hn).1),
      Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hj).1)] using v
  · intro x hx
    exact ⟨x.val,mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt x),by simpa using (mem_roots x).mp hx⟩,ZMod.natCast_zmod_val x⟩

private lemma count_blocks (N d q r : ℕ) : rootCount N d (q*d+r)=q*rootCount N d d+rootCount N d r := by
  classical
  have split (m h : ℕ) : rootCount N d (m*d+h)=rootCount N d (m*d)+rootCount N d h := by
    simp_rw [root_sum]
    rw [sum_range_add]
    congr 1
    apply sum_congr rfl
    intro j _
    simp
  induction q with
  | zero => simp
  | succ q ih =>
    rw [split (q+1) r,Nat.succ_mul,split q d,Nat.succ_mul]
    have base := ih
    have blocks : rootCount N d (q*d)=q*rootCount N d d := by
      rw [split q r] at base
      omega
    rw [blocks]

theorem root_discrepancy (N d Y : ℕ) [NeZero d] (sq : Squarefree d) :
    |(rootCount N d Y:ℝ)-(Y:ℝ)*density N d|≤d := by
  classical
  let q := Y/d
  let r := Y%d
  have de : q*d+r=Y := by simpa [q,r,Nat.mul_comm] using Nat.div_add_mod Y d
  have less : r<d := Nat.mod_lt _ (NeZero.pos d)
  have count := count_blocks N d q r
  rw [de,root_period] at count
  have sub (a : ℕ) : rootCount N d a≤a := by
    unfold rootCount
    exact (card_filter_le ..).trans_eq (card_range _)
  have pos : 0<(d:ℝ) := by exact_mod_cast NeZero.pos d
  have size := root_card_density N d sq
  have low : 0≤density N d := nonneg_of_mul_nonneg_right ((Nat.cast_nonneg _).trans size.le) pos
  have up : density N d≤1 := by
    apply le_of_mul_le_mul_left _ pos
    rw [mul_one,← size,← root_period]
    exact_mod_cast sub d
  have zr : ((r:ℕ):ℝ)≤d := by exact_mod_cast less.le
  have cr : (rootCount N d r:ℝ)≤d := by exact_mod_cast (sub r).trans less.le
  have rem : (q:ℝ)*d+r=Y := by exact_mod_cast de
  have total : (rootCount N d Y:ℝ)=(q:ℝ)*(roots N d).card+rootCount N d r := by exact_mod_cast count
  have exactErr : (rootCount N d Y:ℝ)-(Y:ℝ)*density N d=(rootCount N d r:ℝ)-r*density N d := by
    rw [total,size,← rem]; ring
  rw [exactErr,abs_le]
  constructor
  · linarith only [Nat.cast_nonneg (α:=ℝ) (rootCount N d r),mul_le_mul zr up low (Nat.cast_nonneg (α:=ℝ) d)]
  · linarith only [cr,mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) low]

#print axioms root_discrepancy
end GoldbachSpectral435.GoldbachSieve
