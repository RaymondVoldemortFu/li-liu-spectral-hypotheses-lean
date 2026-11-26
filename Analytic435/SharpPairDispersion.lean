module
public import SharpPrimeTwist
public import NearLineDispersion

/-! A bound for a single large congruence that tracks its mesh and the
conductor logarithm separately. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Finset MeasureTheory
namespace GoldbachSpectral435.GoldbachSieve
open CriticalCharacter

private lemma sharp_rate {q m p e C J h : ℝ} (qp : 0<q) (mp : 0<m) (pp : 0<p)
    (ep : 0<e) (cp : 0<C) (jp : 0≤J) (hp : 0≤h) (den : p^2≤2*q*e) (cap : q*J^2≤h^2*m) :
    p*(C*Real.sqrt m*J)/(m*Real.sqrt e)≤2*C*h := by
  have q2 := Real.sq_sqrt qp.le
  have e2 := Real.sq_sqrt ep.le
  have m2 := Real.sq_sqrt mp.le
  have pmax : p≤2*Real.sqrt q*Real.sqrt e := by
    apply (sq_le_sq₀ pp.le (by positivity)).mp
    rw [mul_pow,mul_pow,q2,e2]
    nlinarith only [den,mul_nonneg qp.le ep.le]
  have rcap : Real.sqrt q*J≤h*Real.sqrt m := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rwa [mul_pow,mul_pow,q2,m2]
  apply (div_le_iff₀ (mul_pos mp (Real.sqrt_pos.mpr ep))).mpr
  calc
    _ ≤ (2*Real.sqrt q*Real.sqrt e)*(C*Real.sqrt m*J) := mul_le_mul_of_nonneg_right pmax (by positivity)
    _ = (2*C*Real.sqrt m*Real.sqrt e)*(Real.sqrt q*J) := by ring
    _ ≤ (2*C*Real.sqrt m*Real.sqrt e)*(h*Real.sqrt m) := mul_le_mul_of_nonneg_left rcap (by positivity)
    _ = _ := by linear_combination 2*C*h*Real.sqrt e*m2

/-- If q(6+log q)²≤h²M, the normalized congruence has error at most a
quadratic polynomial in h, with its constant term equal to zero. -/
theorem sharp_near_line_error (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g) :
    ∃ C D : ℝ, 0<C ∧ 0<D ∧ ∀ᶠ M : ℕ in atTop, ∀ (z j H : ℕ) (h : ℝ), 2≤z → 0<H → Even H →
      let q := liftedModulus z j
      let T := truncatedSeries H z
      let U := principalMass q M f/M
      let V := principalMass q M g/M
      4≤q → q≤M → 0≤h → (q:ℝ)*(6+Real.log q)^2≤h^2*M → 1/2≤T → GRH q → ∀ sign : Bool,
      |(q:ℝ)*classPairs q H M M sign f g/((M:ℝ)^2*T)-U*V|≤
        (C*h)*(D*h)+|U| *(D*h)+|V| *(C*h) := by
  obtain ⟨C,cp,A⟩ := sharp_prime_twist f hf
  obtain ⟨D,dp,B'⟩ := sharp_prime_twist g hg
  refine ⟨2*C,2*D,by positivity,by positivity,?_⟩
  filter_upwards [A,B'] with M a b
  intro z j H h zz hp ev q T U V q4 qm hp' cap low grh sign
  let p : ℝ := q.totient
  let e : ℝ := (allowed H q).card
  let B := (C*Real.sqrt M*(6+Real.log q))
  let K := (D*Real.sqrt M*(6+Real.log q))
  let P := classPairs q H M M sign f g
  have qr : 0<(q:ℝ) := by exact_mod_cast (NeZero.pos q)
  have mr : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have pp : 0<p := Nat.cast_pos.mpr (NeZero.pos _)
  have tp : 0<T := by linarith
  have eq : (q:ℝ)*e=T*p^2 := (div_eq_iff (pow_ne_zero _ pp.ne')).mp (lifted_density zz hp ev j)
  have ep : 0<e := pos_of_mul_pos_right (eq ▸ mul_pos tp (sq_pos_of_pos pp)) qr.le
  have den : p^2≤2*(q:ℝ)*e := by nlinarith only [eq,mul_le_mul_of_nonneg_right low (sq_nonneg p)]
  have logq : 0≤Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤q by omega))
  have xp : 0≤B := by dsimp only [B]; positivity
  have yp : 0≤K := by dsimp only [K]; positivity
  have av := variance_of_twists M f B (a q q4 qm grh)
  have bv := variance_of_twists M g K (b q q4 qm grh)
  have bound := rescale_pair_error mr pp ep (pairs_of_variance q H M M sign f g B K xp yp av bv)
  have left := sharp_rate qr mr pp ep cp (show 0≤6+Real.log (q:ℝ) by positivity) hp' den cap
  have right := sharp_rate qr mr pp ep dp (show 0≤6+Real.log (q:ℝ) by positivity) hp' den cap
  have rp : 0≤p*K/((M:ℝ)*Real.sqrt e) := by positivity
  have eqP : (q:ℝ)*P/((M:ℝ)^2*T)=p^2*P/((M:ℝ)^2*e) := by
    field_simp
    nlinarith only [congrArg (fun t : ℝ => P*(M:ℝ)^2*t) eq,congrArg (fun t : ℝ => P*t) eq]
  change |(q:ℝ)*P/((M:ℝ)^2*T)-U*V|≤_
  rw [eqP]
  exact bound.trans (add_le_add (add_le_add (mul_le_mul left right rp (by positivity))
    (mul_le_mul_of_nonneg_left right (abs_nonneg U))) (mul_le_mul_of_nonneg_left left (abs_nonneg V)))


#print axioms sharp_near_line_error
end GoldbachSpectral435.GoldbachSieve
