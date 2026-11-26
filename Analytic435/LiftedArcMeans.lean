module
public import RationalPrimeArcs
public import Mathlib.Data.ZMod.Units

/-! Normalized reduced-residue means under a change of modulus.
Lifting to 4q makes the character estimates apply even for q = 1, 2, 3. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open ConditionalGoldbach Finset Complex Filter
namespace GoldbachSpectral435.CriticalCharacter

private lemma group_average {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (π : G→*H) (surj : Function.Surjective π) (f : H→ℂ) :
    (∑ x : G,f (π x))/(Fintype.card G:ℂ)=(∑ h : H,f h)/(Fintype.card H:ℂ) := by
  have row (h : H) : (∑ x : G,f (h*π x))=∑ x : G,f (π x) := by
    obtain ⟨y,rfl⟩ := surj h
    simpa only [map_mul] using (Group.mulLeft_bijective y).sum_comp (fun x : G => f (π x))
  have col (x : G) : (∑ h : H,f (h*π x))=∑ h : H,f h := (Group.mulRight_bijective (π x)).sum_comp f
  have eq : (Fintype.card H:ℂ)*(∑ x : G, f (π x))=(Fintype.card G:ℂ)*(∑ h : H,f h) := calc
    _ = ∑ h : H, ∑ x : G, f (h*π x) := by simp_rw [row]; simp
    _ = _ := by rw [sum_comm]; simp_rw [col]; simp
  have gp : (Fintype.card G:ℂ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : (Fintype.card H:ℂ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (div_eq_div_iff gp hp).mpr (by simpa only [mul_comm] using eq)

private lemma sum_units (q : ℕ) [NeZero q] (f : ZMod q→ℂ) :
    (∑ x∈unitClasses q,f x)=∑ u : (ZMod q)ˣ, f u := by
  classical
  symm
  apply sum_bij (fun (u : (ZMod q)ˣ) _ => (u:ZMod q))
  · intro u _; exact mem_unitClasses.mpr u.isUnit
  · intro u _ v _ eq; exact Units.ext eq
  · intro x hx; obtain ⟨u,rfl⟩ := mem_unitClasses.mp hx; exact ⟨u,mem_univ _,rfl⟩
  · intro _ _; rfl

def liftedPhase {q Q : ℕ} (dv : q∣Q) (ψ : AddChar (ZMod q) ℂ) : AddChar (ZMod Q) ℂ :=
  ψ.compAddMonoidHom (ZMod.castHom dv (ZMod q)).toAddMonoidHom

theorem lifted_mean {q Q : ℕ} [NeZero Q] [NeZero q] (dv : q∣Q) (ψ : AddChar (ZMod q) ℂ) :
    unitMean Q (liftedPhase dv ψ)=unitMean q ψ := by
  rw [unitMean,unitMean,sum_units,sum_units]
  have eq := group_average (ZMod.unitsMap dv) (ZMod.unitsMap_surjective dv) (fun u : (ZMod q)ˣ => ψ u)
  rwa [ZMod.card_units_eq_totient,ZMod.card_units_eq_totient] at eq

lemma unit_mean_norm (q : ℕ) [NeZero q] (ψ : AddChar (ZMod q) ℂ) : ‖unitMean q ψ‖≤1 := by
  rw [unitMean,sum_units,norm_div,Complex.norm_natCast,div_le_one (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q)))]
  apply (norm_sum_le ..).trans
  simp [ZMod.card_units_eq_totient]

lemma arc_lift {q Q : ℕ} (dv : q∣Q) (ψ : AddChar (ZMod q) ℂ) (M : ℕ) (f : ℝ→ℝ) (t : ℝ) :
    arcSum M f (liftedPhase dv ψ) t=arcSum M f ψ t := by
  unfold arcSum
  apply sum_congr rfl
  intro n _
  have e : liftedPhase dv ψ n=ψ (n:ZMod q) := by
    change ψ ((ZMod.castHom dv (ZMod q)) (n:ZMod Q))=_
    rw [map_natCast]
  rw [e]

/-- A principal approximation with the exact coefficient for every positive
reduced denominator q. The principal sum removes primes dividing 4q. -/
theorem every_rational_arc (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C F : ℝ, 0<C ∧ 0≤F ∧ ∀ᶠ M : ℕ in atTop, ∀ (q : ℕ) [NeZero q], 4*q≤M → GRH (4*q) →
      ∀ (ψ : AddChar (ZMod q) ℂ), Function.Injective ψ → ∀ t : ℝ,
      ‖arcSum M f ψ t-(ArithmeticFunction.moebius q:ℂ)/q.totient*principalArc (4*q) M f t‖≤
        Real.sqrt (4*q:ℕ)*(C*(1+|t|)^4*Real.sqrt M*(6+Real.log (4*q:ℕ)))+
          F*(Nat.log 2 M:ℝ)*Real.log (4*q:ℕ) := by
  obtain ⟨C,F,cp,fp,est⟩ := additive_arc_bound f hf
  refine ⟨C,F,cp,fp,?_⟩
  filter_upwards [est] with M bound
  intro q inst size grh ψ inj t
  have dv : q∣4*q := dvd_mul_left ..
  have qp := NeZero.pos q
  have m : unitMean q ψ=(ArithmeticFunction.moebius q:ℂ)/q.totient := by rw [unitMean,primitive_additive_mean q ψ inj]
  have ok := bound (4*q) (by omega) size grh (liftedPhase dv ψ) t
  rwa [arc_lift,lifted_mean,m] at ok

#print axioms every_rational_arc
end GoldbachSpectral435.CriticalCharacter
