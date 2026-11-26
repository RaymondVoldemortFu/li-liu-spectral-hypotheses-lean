module
public import SieveResidues
public import HorizonFactors

/-! Complete periods and translated intervals for the pairs surviving
the congruence conditions at primes up to the logarithmic cutoff. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset
namespace GoldbachSpectral435.GoldbachSieve

def allowed (H d : ℕ) [NeZero d] : Finset (ZMod d) := by
  classical exact univ.filter (fun x : ZMod d => IsUnit (x*(x-H)))

@[simp] lemma mem_allowed (H d : ℕ) [NeZero d] (x : ZMod d) :
    x∈allowed H d ↔ IsUnit (x*(x-H)) := by classical simp [allowed]

private lemma prime_allowed (H p : ℕ) (pp : p.Prime) :
    letI : NeZero p := ⟨pp.ne_zero⟩
    ((allowed H p).card:ℝ)=(p:ℝ)*(1-localDensity H p) := by
  classical
  let _ : Fact p.Prime := ⟨pp⟩
  let _ : NeZero p := ⟨pp.ne_zero⟩
  have e : allowed H p=(roots H p)ᶜ := by ext x; simp [root,isUnit_iff_ne_zero]
  have h := card_compl_add_card (roots H p)
  rw [← e,ZMod.card,root_card_prime H p pp] at h
  have pr : (p:ℝ)≠0 := by exact_mod_cast pp.ne_zero
  unfold localDensity
  split_ifs with dvd
  · simp only [dvd,ite_true] at h
    have b : ((allowed H p).card:ℝ)+1=p := by exact_mod_cast h
    field_simp
    nlinarith
  · simp only [dvd,ite_false] at h
    have b : ((allowed H p).card:ℝ)+2=p := by exact_mod_cast h
    field_simp
    nlinarith

private lemma mul_allowed (H d e : ℕ) [NeZero d] [NeZero e] (cop : d.Coprime e) :
    (allowed H (d*e)).card=(allowed H d).card*(allowed H e).card := by
  classical
  let r := ZMod.chineseRemainder cop
  have eq (x : ZMod (d*e)) : x∈allowed H (d*e) ↔ (r x).1∈allowed H d ∧ (r x).2∈allowed H e := by
    simp only [mem_allowed]
    rw [← isUnit_map_iff r (x*(x-H)),map_mul,map_sub,map_natCast,Prod.isUnit_iff]
    rfl
  rw [← card_product]
  apply card_bij (fun x _ => r x)
  · intro x h; exact mem_product.mpr ((eq x).mp h)
  · intro x _ y _ h; exact r.injective h
  · intro y h
    exact ⟨r.symm y,(eq _).mpr (by simpa only [r.apply_symm_apply] using mem_product.mp h),r.apply_symm_apply _⟩

private lemma allowed_congr (H : ℕ) {a b : ℕ} [NeZero a] [NeZero b] (e : a=b) :
    (allowed H a).card=(allowed H b).card := by subst b; rfl

def survivingDensity (H z : ℕ) : ℝ := ∏ p∈smallPrimes z, (1-localDensity H p)

instance primorialNeZero (z : ℕ) : NeZero (primorial z) := ⟨(primorial_pos z).ne'⟩

theorem allowed_count (H z : ℕ) :
    ((allowed H (primorial z)).card:ℝ)=(primorial z:ℝ)*survivingDensity H z := by
  classical
  let f := fun T : Finset ℕ => ∏ p∈T,p
  have aux (T : Finset ℕ) (pr : ∀ p∈T, p.Prime) :
      letI : NeZero (f T) := ⟨(prod_pos fun p hp => (pr p hp).pos).ne'⟩
      ((allowed H (f T)).card:ℝ)=(f T:ℝ)*∏ p∈T, (1-localDensity H p) := by
    induction T using Finset.induction_on with
    | empty =>
      have eq : allowed H 1=univ := by
        ext x
        rw [mem_allowed]
        exact iff_of_true (by rw [Subsingleton.elim (x*(x-H)) 1]; exact isUnit_one) (mem_univ _)
      simp [f,eq]
    | @insert p T hp ih =>
      have prT : ∀ q∈T, q.Prime := fun q h => pr q (mem_insert_of_mem h)
      have pp := pr p (mem_insert_self ..)
      let _ : NeZero p := ⟨pp.ne_zero⟩
      let _ : NeZero (f T) := ⟨(prod_pos fun q h => (prT q h).pos).ne'⟩
      have cop : p.Coprime (f T) := Nat.Coprime.prod_right (fun q h =>
        (Nat.coprime_primes pp (prT q h)).mpr (fun eq => hp (eq ▸ h)))
      have eq : f (insert p T)=p*f T := prod_insert hp
      let _ : NeZero (f (insert p T)) := ⟨(prod_pos fun p h => (pr p h).pos).ne'⟩
      rw [allowed_congr H eq,eq,prod_insert hp,mul_allowed H p (f T) cop,Nat.cast_mul,Nat.cast_mul,
        prime_allowed H p pp,ih prT]
      ring
  exact aux (smallPrimes z) (fun p h => (mem_filter.mp h).2)

/-- The first argument of each pair ranges over [A,A+Y). -/
def intervalCount {d : ℕ} [NeZero d] (E : Finset (ZMod d)) (A Y : ℕ) : ℕ := by
  classical exact ((range Y).filter (fun n : ℕ => ((A+n:ℕ):ZMod d)∈E)).card

private lemma interval_sum {d : ℕ} [NeZero d] (E : Finset (ZMod d)) (A Y : ℕ) :
    intervalCount E A Y=∑ n∈range Y, if ((A+n:ℕ):ZMod d)∈E then (1:ℕ) else 0 := by
  classical
  rw [← sum_filter,sum_const,nsmul_eq_mul,Nat.mul_one,intervalCount]
  rfl

private lemma complete_period {d : ℕ} [NeZero d] (E : Finset (ZMod d)) (A : ℕ) :
    intervalCount E A d=E.card := by
  classical
  unfold intervalCount
  apply card_bij (fun (n : ℕ) _ => ((A+n:ℕ):ZMod d))
  · exact fun n h => (mem_filter.mp h).2
  · intro n hn j hj h
    simp only [Nat.cast_add,add_right_inj] at h
    have v := congrArg ZMod.val h
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hn).1),
      Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hj).1)] using v
  · intro x hx
    let v := x-(A:ZMod d)
    have e : ((A+v.val:ℕ):ZMod d)=x := by rw [Nat.cast_add,ZMod.natCast_zmod_val]; dsimp [v]; abel
    exact ⟨v.val,mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),e ▸ hx⟩,e⟩

private lemma blocks {d : ℕ} [NeZero d] (E : Finset (ZMod d)) (A q r : ℕ) :
    intervalCount E A (q*d+r)=q*E.card+intervalCount E A r := by
  classical
  have split (m h : ℕ) : intervalCount E A (m*d+h)=intervalCount E A (m*d)+intervalCount E A h := by
    simp_rw [interval_sum]
    rw [sum_range_add]
    congr 1
    apply sum_congr rfl
    intro j _
    simp
  have full (m : ℕ) : intervalCount E A (m*d)=m*E.card := by
    induction m with
    | zero => simp [intervalCount]
    | succ m ih => rw [Nat.succ_mul,split,complete_period,ih,Nat.succ_mul]
  rw [split,full]

/-- Exact count at any integral number of periods, including translated intervals. -/
theorem interval_multiples {d : ℕ} [NeZero d] (E : Finset (ZMod d)) (A k : ℕ) :
    intervalCount E A (k*d)=k*E.card := by
  simpa [intervalCount] using blocks E A k 0

/-- A translate costs at most one incomplete period, independently of the offset. -/
theorem interval_error {d : ℕ} [NeZero d] (E : Finset (ZMod d)) (A Y : ℕ) :
    |(intervalCount E A Y:ℝ)-(Y:ℝ)*(E.card/d)|≤d := by
  let q := Y/d
  let r := Y%d
  have e : q*d+r=Y := by simpa [q,r,Nat.mul_comm] using Nat.div_add_mod Y d
  have rem : (q:ℝ)*d+r=Y := by exact_mod_cast e
  have c := blocks E A q r
  rw [e] at c
  have total : (intervalCount E A Y:ℝ)=(q:ℝ)*E.card+intervalCount E A r := by exact_mod_cast c
  have b : intervalCount E A r≤r := (card_filter_le ..).trans_eq (card_range _)
  have h : (r:ℝ)≤d := by exact_mod_cast (Nat.mod_lt Y (NeZero.pos d)).le
  have a : (intervalCount E A r:ℝ)≤r := by exact_mod_cast b
  have p : 0<(d:ℝ) := by exact_mod_cast NeZero.pos d
  have le : (E.card:ℝ)/d≤1 := (div_le_one p).mpr (by exact_mod_cast E.card_le_univ.trans_eq (ZMod.card d))
  have nn : 0≤(E.card:ℝ)/d := by positivity
  have bnd := mul_le_mul_of_nonneg_left le (Nat.cast_nonneg (α:=ℝ) r)
  rw [total,← rem,add_mul,mul_assoc,mul_div_cancel₀ _ p.ne',abs_le]
  constructor <;> nlinarith only [a,h,bnd,mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) nn,
    Nat.cast_nonneg (α:=ℝ) (intervalCount E A r)]

theorem sifted_interval (H z A Y : ℕ) :
    |(intervalCount (allowed H (primorial z)) A Y:ℝ)-(Y:ℝ)*survivingDensity H z|≤primorial z := by
  have h := interval_error (allowed H (primorial z)) A Y
  rwa [allowed_count,mul_div_cancel_left₀ _ (by exact_mod_cast (primorial_pos z).ne')] at h

#print axioms sifted_interval
end GoldbachSpectral435.GoldbachSieve
