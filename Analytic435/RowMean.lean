module
public import ShiftMean
public import SpectralTests.Parameters

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral GoldbachSpectral.BandSieve Finset
namespace GoldbachSpectral435

def bandObservable (P H a N : ℕ) : ℝ :=
  ∑ m∈Icc P (2*P), if m.Coprime N then
    mangoldt m*shape a H P m*(mangoldt (N-m)-mangoldt (N+m)) else 0

def rowMean (q M P H a : ℕ) : ℝ :=
  ∑ n∈range M, if (n:ZMod q)=(a:ZMod q) then broad (n/(M:ℝ))*bandObservable P H a n else 0

theorem transpose_mean (q M P H a : ℕ) :
    rowMean q M P H a = ∑ m∈Icc P (2*P),mangoldt m*shape a H P m*
      (shiftedMass q M m a false-shiftedMass q M m a true) := by
  unfold rowMean shiftedMass bandObservable
  simp only [Bool.false_eq_true,ite_false,ite_true,← sum_sub_distrib,mul_sum]
  rw [Finset.sum_comm (s := Icc P (2*P))]
  apply sum_congr rfl
  intro n _
  by_cases yes : (n:ZMod q)=(a:ZMod q)
  · rw [ite_eq_left yes]
    apply sum_congr rfl
    intro m _
    simp only [yes,true_and]
    split_ifs <;> ring
  · simp [yes]

private theorem abs_unit (q : ℕ) (z : ℤ) : IsUnit (z:ZMod q) ↔ z.natAbs.Coprime q := by
  cases z with
  | ofNat n => simpa using ZMod.isUnit_iff_coprime n q
  | negSucc n =>
    simpa only [Int.cast_negSucc, IsUnit.neg_iff,Int.natAbs_negSucc,Nat.cast_succ] using
      (show IsUnit (((n+1:ℕ):ZMod q)) ↔ (n+1).Coprime q from ZMod.isUnit_iff_coprime _ _)

private theorem weight_mass {P H a : ℕ} (hp : 0<P) :
    (∑ m∈Icc P (2*P),mangoldt m*shape a H P m) ≤ (P+1:ℝ)*Real.log (2*P) := by
  have h (m : ℕ) (hm : m∈Icc P (2*P)) : mangoldt m*shape a H P m≤Real.log (2*(P:ℝ)) := by
    have pos := hp.trans_le (mem_Icc.mp hm).1
    have le := (mem_Icc.mp hm).2
    have sh : shape a H P m≤1 := (mul_le_of_le_one_right inner.nonneg outer.le_one).trans inner.le_one
    exact (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg sh).trans
      (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast pos) (by exact_mod_cast le)))
  have total := sum_le_sum h
  simpa only [sum_const,nsmul_eq_mul,Nat.card_Icc,show 2*P+1-P=P+1 by omega,Nat.cast_add,Nat.cast_one] using total

def meanError (C D : ℝ) (q M P : ℕ) : ℝ :=
  Real.sqrt M*(C*(M:ℝ)^(1/4:ℝ)*q^2)+2*Real.sqrt M*Real.log M+D*(2*P)*Real.log (2*M)

theorem mean_lower :
    ∃ C D : ℝ, 0<C ∧ 0<D ∧ ∀ q : ℕ, ∀ [NeZero q], 4≤q → GRH q →
      ∀ M H P a : ℕ, 0<M → 4*q≤M → 0<P → 8*P≤M →
        (principalMass q M broad/q.totient)*row q a H P-2*meanError C D q M P*((P+1:ℝ)*Real.log (2*P))
          ≤ rowMean q M P H a := by
  obtain ⟨C,D,cp,dp,est⟩ := shifted_estimate
  refine ⟨C,D,cp,dp,?_⟩
  intro q inst hq g M H P a mp qs pp ps
  let U := principalMass q M broad/q.totient
  let E := meanError C D q M P
  have lM : 0≤Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤M by omega))
  have l2 : 0≤Real.log (2*(M:ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1≤2*M by omega))
  have ep : 0≤E := by dsimp [E,meanError]; positivity
  have error (m : ℕ) (hm : m∈Icc P (2*P)) (plus : Bool) :
      |shiftedMass q M m a plus-(if IsUnit (if plus then (a:ZMod q)+m else (a:ZMod q)-m) then U else 0)|≤E := by
    obtain ⟨ml,mu⟩ := mem_Icc.mp hm
    apply (est q hq g M m mp qs (by omega) (by omega) a plus).trans
    dsimp [E,meanError]
    gcongr
    exact_mod_cast mu
  let v := fun m : ℕ => mangoldt m*shape a H P m
  let ca := fun m : ℕ => if (Int.natAbs ((a:ℤ)-m)).Coprime q then (1:ℝ) else 0
  let cb := fun m : ℕ => if (a+m).Coprime q then (1:ℝ) else 0
  have each (m : ℕ) (hm : m∈Icc P (2*P)) :
      U*(v m*(ca m-cb m))-2*E*v m ≤ v m*(shiftedMass q M m a false-shiftedMass q M m a true) := by
    have left := (abs_le.mp (error m hm false)).1
    have right := (abs_le.mp (error m hm true)).2
    have i1 : IsUnit ((a:ZMod q)-m) ↔ (Int.natAbs ((a:ℤ)-m)).Coprime q := by
      simpa using abs_unit q ((a:ℤ)-m)
    have i2 : IsUnit ((a:ZMod q)+m) ↔ (a+m).Coprime q := by simpa using ZMod.isUnit_iff_coprime (a+m) q
    have z : U*(ca m-cb m)-2*E ≤ shiftedMass q M m a false-shiftedMass q M m a true := by
      simp only [Bool.false_eq_true,ite_false,ite_true,i1,i2] at left right
      dsimp [ca,cb]
      split_ifs at * <;> linarith
    have nonneg : 0≤v m := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (mul_nonneg inner.nonneg outer.nonneg)
    exact le_trans (by ring_nf; rfl) (mul_le_mul_of_nonneg_left z nonneg)
  have all := sum_le_sum each
  rw [sum_sub_distrib,← mul_sum,← mul_sum] at all
  rw [transpose_mean]
  apply le_trans _ all
  apply sub_le_sub_left
  exact mul_le_mul_of_nonneg_left (weight_mass pp) (by positivity)

#print axioms mean_lower
end GoldbachSpectral435

