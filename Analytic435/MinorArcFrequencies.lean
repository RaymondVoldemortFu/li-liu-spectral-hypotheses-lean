module
public import MinorArcSize
public import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-! Minor arcs for the ordinary real-frequency prime exponential sum. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Finset Complex
namespace GoldbachSpectral435.CriticalCharacter

def primeFourier (M : ℕ) (f : ℝ→ℝ) (ξ : ℝ) :=
  ∑ n∈range M,(weightedMangoldt M n f:ℂ)*Complex.exp ((2*Real.pi*ξ*n:ℝ)*I)

instance (r : ℚ) : NeZero r.den := ⟨r.den_ne_zero⟩

def rationalPhase (r : ℚ) : AddChar (ZMod r.den) ℂ := ZMod.stdAddChar.mulShift (r.num:ZMod r.den)

lemma rational_injective (r : ℚ) : Function.Injective (rationalPhase r) := by
  have u := (ZMod.isUnit_iff_coprime r.num.natAbs r.den).mpr r.reduced
  have num : IsUnit (r.num:ZMod r.den) := by
    generalize r.num=k at u ⊢
    cases k with
    | ofNat n => simpa using u
    | negSucc n =>
      rw [Int.cast_negSucc]
      simpa using u.neg
  exact (ZMod.injective_stdAddChar (N:=r.den)).comp num.mul_right_injective

lemma rational_phase_value (r : ℚ) (n : ℕ) :
    rationalPhase r n=Complex.exp ((2*Real.pi*(r:ℝ)*n:ℝ)*I) := by
  rw [rationalPhase,AddChar.mulShift_apply]
  have e : (r.num:ZMod r.den)*(n:ZMod r.den)=((r.num*(n:ℤ):ℤ):ZMod r.den) := by push_cast; rfl
  rw [e,ZMod.stdAddChar_coe,Rat.cast_def]
  congr 1
  push_cast
  ring

lemma physical_rational_arc (M : ℕ) (mp : 0<M) (f : ℝ→ℝ) (r : ℚ) (ξ : ℝ) :
    primeFourier M f ξ=arcSum M f (rationalPhase r) (2*Real.pi*(M:ℝ)*(ξ-r)) := by
  unfold primeFourier arcSum
  apply sum_congr rfl
  intro n _
  simp only [rational_phase_value]
  rw [mul_assoc (↑(weightedMangoldt M n f):ℂ) (Complex.exp _) (Complex.exp _),← Complex.exp_add]
  congr 2
  have nz : (M:ℂ)≠0 := Nat.cast_ne_zero.mpr mp.ne'
  push_cast
  field_simp
  ring

/-- Fractions in the Dirichlet dissection with denominator below R. -/
def majorArcs (R U : ℕ) : Set ℝ :=
  {ξ | ∃ r : ℚ, r.den<R ∧ |ξ-(r:ℝ)|≤1/(((U:ℝ)+1)*r.den)}

/-- On the complementary minor arcs the unnormalized sum has size
O_f(M log(M)/sqrt(R) + log(M)^2). The GRH input is restricted to the
denominators appearing in the Dirichlet approximation. -/
theorem minor_arc_bound (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C F : ℝ, 0<C ∧ 0≤F ∧ ∀ᶠ M : ℕ in atTop, ∀ R U : ℕ,
    4≤R → 0<U → R*U≤M → M≤R*(U+1) →
    (∀ (q : ℕ) [NeZero q], R≤q → q≤U → GRH q) → ∀ ξ : ℝ, ξ∉majorArcs R U →
      ‖primeFourier M f ξ‖≤C*(M:ℝ)*(6+Real.log M)/Real.sqrt R+F*(Real.log M)^2 := by
  obtain ⟨C,K,F,cp,kp,fp,all⟩ := arc_size_bound f hf
  let B := (1+2*Real.pi)^4
  have bp : 0<B := by dsimp [B]; positivity
  have lp : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C*B+2*K,F/Real.log 2,by positivity,div_nonneg fp lp.le,?_⟩
  filter_upwards [all] with M est
  intro R U r4 up lo hi grh ξ outside
  obtain ⟨r,approx,qu⟩ := Real.exists_rat_abs_sub_le_and_den_le ξ up
  let q := r.den
  have rq : R≤q := le_of_not_gt (fun small => outside ⟨r,small,approx⟩)
  have qp : 0<(q:ℝ) := Nat.cast_pos.mpr r.pos
  have rp : 0<(R:ℝ) := Nat.cast_pos.mpr (by omega)
  have ump : U≤M := (Nat.le_mul_of_pos_left U (by omega)).trans lo
  have qm : q≤M := qu.trans ump
  have mp : 0<M := up.trans_le ump
  have mr : 0<(M:ℝ) := Nat.cast_pos.mpr mp
  have lM := Real.log_nonneg (Nat.one_le_cast.mpr mp)
  have lq : Real.log (q:ℝ)≤Real.log M := Real.log_le_log qp (Nat.cast_le.mpr qm)
  let T := 2*Real.pi*(M:ℝ)*(ξ-(r:ℝ))
  have den : 0<((U:ℝ)+1)*q := mul_pos (by positivity) qp
  have ratio : (M:ℝ)*|ξ-(r:ℝ)|≤1 := by
    have bound : (M:ℝ)≤(R:ℝ)*(U+1) := by exact_mod_cast hi
    have larger : (R:ℝ)*(U+1)≤((U:ℝ)+1)*q := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr rq) (by positivity)
    apply (mul_le_mul_of_nonneg_left approx mr.le).trans
    rw [mul_one_div,div_le_one den]
    exact bound.trans larger
  have tb : |T|≤2*Real.pi := by
    dsimp only [T]
    rw [abs_mul,abs_of_pos (by positivity : 0<2*Real.pi*(M:ℝ)),mul_assoc]
    exact mul_le_of_le_one_right (by positivity) ratio
  have q4 : 4≤r.den := r4.trans rq
  have applied := est q q4 qm (grh q rq qu) (rationalPhase r) (rational_injective r) T
  rw [physical_rational_arc M mp f r ξ]
  apply applied.trans
  have rootRq : Real.sqrt R*Real.sqrt q≤Real.sqrt M := by
    rw [← Real.sqrt_mul rp.le]
    apply Real.sqrt_le_sqrt
    exact_mod_cast (Nat.mul_le_mul_left R qu).trans lo
  have rootR : 0<Real.sqrt (R:ℝ) := Real.sqrt_pos.mpr rp
  have rootQ := Real.sqrt_pos.mpr qp
  have rootM := Real.sqrt_pos.mpr mr
  have j : 0≤6+Real.log (q:ℝ) := by have := Real.log_nonneg (Nat.one_le_cast.mpr r.pos); change 0≤6+Real.log (r.den:ℝ); linarith
  let L := 6+Real.log (M:ℝ)
  have one : 1≤L := by dsimp only [L]; linarith
  have cb : C*(1+|T|)^4≤C*B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith only [tb] : 1+|T|≤1+2*Real.pi) 4) cp.le
  have product : Real.sqrt q*(C*(1+|T|)^4*Real.sqrt M*(6+Real.log q))≤C*B*M*L/Real.sqrt R := by
    apply (le_div_iff₀ rootR).mpr
    have mag := mul_le_mul (mul_le_mul cb (le_rfl : Real.sqrt M≤_) rootM.le (mul_pos cp bp).le)
      (show 6+Real.log (q:ℝ)≤6+Real.log (M:ℝ) by linarith only [lq]) j (by positivity)
    have cap := mul_le_mul rootRq mag (by positivity) rootM.le
    calc
      _ = (Real.sqrt R*Real.sqrt q)*(C*(1+|T|)^4*Real.sqrt M*(6+Real.log q)) := by ring
      _ ≤ Real.sqrt M*(C*B*Real.sqrt M*(6+Real.log (M:ℝ))) := cap
      _ = _ := by dsimp [L]; linear_combination C*B*(6+Real.log (M:ℝ))*Real.sq_sqrt mr.le
  have mean : 2*K*M/Real.sqrt q≤2*K*M*L/Real.sqrt R := by
    apply (div_le_div_of_nonneg_left (by positivity) rootR (Real.sqrt_le_sqrt (Nat.cast_le.mpr rq))).trans
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) one) rootR.le
  have logpow := Real.log_le_log (show 0<(2:ℝ)^Nat.log 2 M by positivity)
    (by exact_mod_cast Nat.pow_log_le_self 2 mp.ne' : (2:ℝ)^Nat.log 2 M≤M)
  rw [Real.log_pow] at logpow
  have powb := (le_div_iff₀ lp).mpr logpow
  have qlog := Real.log_nonneg (Nat.one_le_cast.mpr r.pos)
  have loss := mul_le_mul (mul_le_mul_of_nonneg_left powb fp) lq qlog (by positivity)
  exact (add_le_add (add_le_add product mean) loss).trans_eq (by dsimp [L]; ring)

#print axioms minor_arc_bound
end GoldbachSpectral435.CriticalCharacter
