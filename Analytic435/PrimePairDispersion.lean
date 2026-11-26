module
public import PrimeClassVariance
public import PrimePairProjection

/-! Dispersion of two genuine prime weights on a prescribed sum or
difference modulo an arbitrary modulus. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset
namespace GoldbachSpectral435.GoldbachSieve
open CriticalCharacter

def classPairs (q H M L : ℕ) [NeZero q] (sign : Bool) (f g : ℝ→ℝ) : ℝ :=
  ∑ t∈allowed H q,classMass q M t f*classMass q L (partner sign H t) g

def deviationBound (C : ℝ) (q M : ℕ) := C*Real.sqrt M*(Real.log M)^2*(6+Real.log q)

private lemma partner_injective {q : ℕ} (sign : Bool) (H : ℕ) :
    Function.Injective (partner (q:=q) sign H) := by
  intro a b eq
  cases sign <;> simp_all [partner]

private lemma restricted_variance {q H : ℕ} [NeZero q] (sign : Bool) (b : ZMod q→ℝ) :
    (∑ t∈allowed H q,b t^2)≤∑ t∈unitClasses q,b t^2 ∧
    (∑ t∈allowed H q,b (partner sign H t)^2)≤∑ t∈unitClasses q,b t^2 := by
  classical
  constructor
  · apply sum_le_sum_of_subset_of_nonneg (fun t ht => mem_unitClasses.mpr (units_of_allowed ht sign).1)
    exact fun _ _ _ => sq_nonneg _
  · let E := allowed H q
    let T := partner (q:=q) sign H
    have inj : Function.Injective T := partner_injective sign H
    have subset : E.image T⊆unitClasses q := by
      intro u hu
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hu
      exact mem_unitClasses.mpr (units_of_allowed ht sign).2
    have le := sum_le_sum_of_subset_of_nonneg (f:=fun t => b t^2) subset (fun _ _ _ => sq_nonneg _)
    rwa [sum_image inj.injOn] at le

private lemma bilinear_bound {α : Type*} (E : Finset α) (a b : α→ℝ) (X Y : ℝ)
    (xp : 0≤X) (yp : 0≤Y) (ha : (∑ t∈E,a t^2)≤X^2) (hb : (∑ t∈E,b t^2)≤Y^2) :
    |∑ t∈E,a t*b t|≤X*Y := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg xp yp)).mp
  rw [sq_abs,mul_pow]
  exact (sum_mul_sq_le_sq_mul_sq E a b).trans (mul_le_mul ha hb (sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _))

private lemma linear_bound {α : Type*} (E : Finset α) (a : α→ℝ) (X : ℝ)
    (xp : 0≤X) (ha : (∑ t∈E,a t^2)≤X^2) : |∑ t∈E,a t|≤Real.sqrt E.card*X := by
  have one : (∑ _t∈E,(1:ℝ)^2)=(Real.sqrt E.card)^2 := by simp
  simpa using bilinear_bound E (fun _ => 1) a (Real.sqrt E.card) X (Real.sqrt_nonneg _) xp one.le ha

theorem pairs_of_variance (q H M L : ℕ) [NeZero q] (sign : Bool) (f g : ℝ→ℝ)
    (X Y : ℝ) (xp : 0≤X) (yp : 0≤Y)
    (av : (∑ t∈unitClasses q,(classError M f t)^2)≤X^2)
    (bv : (∑ t∈unitClasses q,(classError L g t)^2)≤Y^2) :
    let E := allowed H q
    let x := principalMass q M f/q.totient
    let y := principalMass q L g/q.totient
    |classPairs q H M L sign f g-E.card*x*y|≤X*Y+Real.sqrt E.card*(|x| *Y+|y| *X) := by
  classical
  intro E x y
  let a := fun t : ZMod q => classError M f t
  let b := fun t : ZMod q => classError L g (partner sign H t)
  have ha : (∑ t∈E,a t^2)≤X^2 := (restricted_variance (H:=H) sign a).1.trans av
  have hb : (∑ t∈E,b t^2)≤Y^2 := (restricted_variance (H:=H) sign (classError L g)).2.trans bv
  have expand : classPairs q H M L sign f g-E.card*x*y=
      (∑ t∈E,a t*b t)+x*(∑ t∈E,b t)+y*(∑ t∈E,a t) := by
    have per (t : ZMod q) : classMass q M t f*classMass q L (partner sign H t) g=
        a t*b t+x*b t+y*a t+x*y := by dsimp [a,b,classError,x,y]; ring
    unfold classPairs
    simp_rw [per,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul]
    change _-E.card*x*y=_
    ring
  rw [expand]
  have tri := (abs_add_le ((∑ t∈E,a t*b t)+x*∑ t∈E,b t) (y*∑ t∈E,a t)).trans
    (add_le_add (abs_add_le (∑ t∈E,a t*b t) (x*∑ t∈E,b t)) (le_refl _))
  simp only [abs_mul] at tri
  have A' := mul_le_mul_of_nonneg_left (linear_bound E b Y yp hb) (abs_nonneg x)
  have B' := mul_le_mul_of_nonneg_left (linear_bound E a X xp ha) (abs_nonneg y)
  linarith only [tri,A',B',bilinear_bound E a b X Y xp yp ha hb]

theorem prime_pair_dispersion (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g) :
    ∃ C D : ℝ, 0<C ∧ 0<D ∧ ∀ (q H M L : ℕ) [NeZero q], 4≤q → q≤M → q≤L → GRH q → ∀ sign : Bool,
      let E := allowed H q
      let x := principalMass q M f / q.totient
      let y := principalMass q L g / q.totient
      let X := deviationBound C q M
      let Y := deviationBound D q L
      |classPairs q H M L sign f g-E.card*x*y|≤
        X*Y+Real.sqrt E.card*(|x| *Y+|y| *X) := by
  classical
  obtain ⟨C,cp,A⟩ := class_variance_bound f hf
  obtain ⟨D,dp,B⟩ := class_variance_bound g hg
  refine ⟨C,D,cp,dp,?_⟩
  intro q H M L inst q4 qm ql grh sign E x y X Y
  have logq : 0≤Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤q by omega))
  have xp : 0≤X := by dsimp [X,deviationBound]; positivity
  have yp : 0≤Y := by dsimp [Y,deviationBound]; positivity
  exact pairs_of_variance q H M L sign f g X Y xp yp (A q M q4 qm grh) (B q L q4 ql grh)

#print axioms prime_pair_dispersion
end GoldbachSpectral435.GoldbachSieve
