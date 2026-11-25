module
public import SmoothShift

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset
namespace GoldbachSpectral435

def shiftedMass (q M m : ℕ) (a : ZMod q) (plus : Bool) : ℝ :=
  ∑ n∈range M, if (n:ZMod q)=a ∧ m.Coprime n then
    mangoldt (if plus then n+m else n-m)*broad (n/(M:ℝ)) else 0

private def moved (q M i j m : ℕ) (a : ZMod q) : ℝ :=
  ∑ u∈range M, if ((u+i:ℕ):ZMod q)=a ∧ (u+j).Coprime m then
    mangoldt (u+j)*broad ((u+i:ℕ)/(M:ℝ)) else 0

private theorem moves (q M m : ℕ) (a : ZMod q) (hm : 0<M) (small : 4*m≤M) :
    shiftedMass q M m a false = moved q M m 0 m a ∧ shiftedMass q M m a true = moved q M 0 m m a := by
  let f := fun n : ℕ => if (n:ZMod q)=a ∧ m.Coprime n then
    mangoldt (n-m)*broad (n/(M:ℝ)) else 0
  have front (n : ℕ) (hn : n<m) : f n=0 := by simp [f,weight_zero_low M n hm (by omega)]
  have tail (n : ℕ) (hn : M≤n) : f n=0 := by simp [f,weight_zero_high M n hm hn]
  constructor
  · change ∑ n∈range M,f n=_
    rw [← translate_supported M m f front tail]
    unfold moved
    apply sum_congr rfl
    intro u _
    simp only [f,Nat.add_zero,Nat.add_sub_cancel,Nat.coprime_add_self_right,(Nat.coprime_comm : m.Coprime u ↔ u.Coprime m)]
  · unfold shiftedMass moved
    apply sum_congr rfl
    intro n _
    simp only [ite_true,Nat.add_zero,Nat.coprime_add_self_left,(Nat.coprime_comm : m.Coprime n ↔ n.Coprime m)]

private theorem moved_error {q : ℕ} [NeZero q] (M i j m : ℕ) (hm : 0<M) (js : 4*j≤M)
    (a : ZMod q) (D : ℝ) (dp : 0≤D) (lip : ∀ x y : ℝ, |broad x-broad y|≤D*|x-y|) :
    |moved q M i j m a-restrictedMass q M m (a+j-i) broad| ≤ D*(i+j)*Real.log (2*M) := by
  rw [← class_translate M i j m hm js a,moved,← sum_sub_distrib]
  have h := shift_weight_error M i j m hm (by omega) a D dp lip
  convert h using 2
  apply sum_congr rfl
  intro u _
  split_ifs <;> simp only [weightedMangoldt,sub_self,mul_sub]

/-- Both signed shifts have the same principal mass coefficient. The error
is uniform even for classes or source samples that fail coprimality. -/
theorem shifted_estimate :
    ∃ C D : ℝ, 0<C ∧ 0<D ∧ ∀ q : ℕ, ∀ [NeZero q], 4≤q → GRH q →
      ∀ M m : ℕ, 0<M → 4*q≤M → 0<m → 4*m≤M → ∀ a : ZMod q, ∀ plus : Bool,
        let t := if plus then a+m else a-m
        |shiftedMass q M m a plus-(if IsUnit t then principalMass q M broad/q.totient else 0)| ≤
          Real.sqrt M*(C*(M:ℝ)^(1/4:ℝ)*q^2) + 2*Real.sqrt M*Real.log M + D*m*Real.log (2*M) := by
  obtain ⟨C,cp,ap⟩ := physical_AP broad broadWeight
  obtain ⟨D,dp,lip⟩ := broad_lipschitz
  refine ⟨C,D,cp,dp,?_⟩
  intro q inst hq g M m hm sq mp sm a plus t
  let E := Real.sqrt M*(C*(M:ℝ)^(1/4:ℝ)*q^2)
  have h := class_all q M m hm sq sm mp t E (by dsimp [E]; positivity) (ap q hq g M hm t)
  have shift : |shiftedMass q M m a plus-restrictedMass q M m t broad| ≤ D*m*Real.log (2*M) := by
    cases plus
    · rw [(moves q M m a hm sm).1]
      simpa [t] using moved_error M m 0 m hm (by omega) a D dp.le lip
    · rw [(moves q M m a hm sm).2]
      simpa [t] using moved_error M 0 m m hm sm a D dp.le lip
  exact (abs_sub_le _ (restrictedMass q M m t broad) _).trans ((add_le_add shift h).trans_eq (by dsimp [E]; ring))

#print axioms shifted_estimate
end GoldbachSpectral435

