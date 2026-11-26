module
public import PrimeClassVariance
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! The principal coefficient of a primitive additive phase on the
invertible residue classes, for arbitrary positive moduli. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open ConditionalGoldbach Finset Complex ArithmeticFunction
open scoped ArithmeticFunction
namespace GoldbachSpectral435.CriticalCharacter

private lemma coprime_indicator (q n : ℕ) (qp : 0<q) :
    (∑ d∈q.divisors,if d∣n then (ArithmeticFunction.moebius d:ℂ) else 0)=
      if n.Coprime q then 1 else 0 := by
  classical
  have gp := Nat.gcd_pos_of_pos_right n qp
  have eq : q.divisors.filter (fun d => d∣n)=(n.gcd q).divisors := by
    ext d
    simp only [mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff,qp.ne',gp.ne',ne_eq,not_false_eq_true,and_true]
    tauto
  rw [← sum_filter,eq,← Int.cast_sum]
  have inv := congrArg (fun A : ArithmeticFunction ℤ => A (n.gcd q)) moebius_mul_coe_zeta
  rw [coe_mul_zeta_apply,one_apply] at inv
  rw [inv]
  change ((if n.gcd q=1 then (1:ℤ) else 0:ℤ):ℂ)=if n.gcd q=1 then 1 else 0
  split <;> norm_num

private lemma multiples (d q : ℕ) (dp : 0<d) (dv : d∣q) (F : ℕ→ℂ) :
    (∑ n∈range q,if d∣n then F n else 0)=∑ k∈range (q/d), F (d*k) := by
  obtain ⟨m,rfl⟩ := dv
  rw [Nat.mul_div_cancel_left _ dp,← sum_filter]
  symm
  apply sum_bij (fun k _ => d*k)
  · intro k hk
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hk) dp),dvd_mul_right ..⟩
  · intro k _ l _ same; exact Nat.eq_of_mul_eq_mul_left dp same
  · intro n hn
    obtain ⟨small,⟨k,rfl⟩⟩ := mem_filter.mp hn
    exact ⟨k,mem_range.mpr (Nat.lt_of_mul_lt_mul_left (mem_range.mp small)),rfl⟩
  · intro _ _; rfl

private lemma primitive_progression (q : ℕ) [NeZero q] (ψ : AddChar (ZMod q) ℂ)
    (inj : Function.Injective ψ) (d : ℕ) (dv : d∣q) :
    (∑ n∈range q,if d∣n then ψ n else 0)=if d=q then 1 else 0 := by
  have qp := NeZero.pos q
  have dp := Nat.pos_of_dvd_of_pos dv qp
  rw [multiples d q dp dv]
  have term (k : ℕ) : ψ ((d*k:ℕ):ZMod q)=(ψ d)^k := by
    rw [Nat.cast_mul,mul_comm,← nsmul_eq_mul,AddChar.map_nsmul_eq_pow]
  simp_rw [term]
  by_cases eq : d=q
  · subst d; simp [qp.ne']
  rw [ite_eq_right eq]
  have notOne : ψ d≠1 := by
    intro one
    have zero := inj (one.trans ψ.map_zero_eq_one.symm)
    have back := (ZMod.natCast_eq_zero_iff d q).mp zero
    exact eq (Nat.dvd_antisymm dv back)
  have power : (ψ d)^(q/d)=1 := by
    rw [← term, Nat.mul_div_cancel' dv, ZMod.natCast_self,ψ.map_zero_eq_one]
  rw [geom_sum_eq notOne,power,sub_self,zero_div]

/-- A complete reduced-residue sum of an injective additive character is μ(q). -/
theorem primitive_additive_mean (q : ℕ) [NeZero q] (ψ : AddChar (ZMod q) ℂ)
    (inj : Function.Injective ψ) : (∑ a∈unitClasses q,ψ a)=(ArithmeticFunction.moebius q:ℂ) := by
  classical
  have qp := NeZero.pos q
  have rangeEq : (∑ a∈unitClasses q,ψ a)=∑ n∈range q,if n.Coprime q then ψ n else 0 := by
    rw [unitClasses,sum_filter]
    apply sum_bij (fun (a : ZMod q) _ => a.val)
    · intro a _; exact mem_range.mpr a.val_lt
    · intro a _ b _ eq; exact ZMod.val_injective q eq
    · intro n hn; exact ⟨n,mem_univ _,ZMod.val_natCast_of_lt (mem_range.mp hn)⟩
    · intro a _
      have iu := ZMod.isUnit_iff_coprime a.val q
      rw [ZMod.natCast_zmod_val] at iu ⊢
      simp only [iu]
  have term (n : ℕ) : (if n.Coprime q then ψ n else 0)=
      ∑ d∈q.divisors,(ArithmeticFunction.moebius d:ℂ)*(if d∣n then ψ n else 0) := by
    have ind := congrArg (· *ψ (n:ZMod q)) (coprime_indicator q n qp)
    rw [sum_mul] at ind
    calc
      _ = (if n.Coprime q then 1 else 0:ℂ)*ψ n := by split <;> simp
      _ = _ := by
        rw [← ind]
        apply sum_congr rfl
        intro d _
        split <;> simp
  rw [rangeEq]
  simp_rw [term]
  rw [sum_comm]
  simp_rw [← mul_sum]
  have per (d : ℕ) (hd : d∈q.divisors) := primitive_progression q ψ inj d (Nat.mem_divisors.mp hd).1
  rw [sum_congr rfl (fun d hd => congrArg ((ArithmeticFunction.moebius d:ℂ)*·) (per d hd))]
  simp [mul_ite,Nat.mem_divisors,qp.ne']

#print axioms primitive_additive_mean
end GoldbachSpectral435.CriticalCharacter
