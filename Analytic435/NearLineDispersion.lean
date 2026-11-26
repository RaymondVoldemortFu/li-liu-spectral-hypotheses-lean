module
public import PrimePairDispersion
public import DyadicSieveModuli

/-! A uniform two-prime estimate in congruences of modulus as large as
the length of summation divided by a power of its logarithm. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Finset MeasureTheory
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open PhysicalTests

private lemma rate {q M : ℕ} (qm : q≤M) (qp : 0<q) (l6 : 6≤Real.log (M:ℝ))
    (cap : (q:ℝ)*(Real.log M)^8≤M) (p e C : ℝ) (pp : 0<p) (ep : 0<e) (cp : 0<C)
    (den : p^2≤2*(q:ℝ)*e) :
    p*deviationBound C q M/((M:ℝ)*Real.sqrt e)≤4*C/Real.log M := by
  let L := Real.log (M:ℝ)
  have lp : 0<L := by dsimp [L]; linarith
  have qr : 0<(q:ℝ) := Nat.cast_pos.mpr qp
  have mr : 0<(M:ℝ) := Nat.cast_pos.mpr (qp.trans_le qm)
  have eq1 := Real.sq_sqrt qr.le
  have eq2 := Real.sq_sqrt ep.le
  have eq3 := Real.sq_sqrt mr.le
  have pmax : p≤2*Real.sqrt q*Real.sqrt e := by
    apply (sq_le_sq₀ pp.le (by positivity)).mp
    rw [mul_pow,mul_pow,eq1,eq2]
    nlinarith only [den,mul_nonneg qr.le ep.le]
  have rcap : Real.sqrt q*L^4≤Real.sqrt M := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,eq1,← pow_mul,eq3]
    exact cap
  have jcap : 6+Real.log (q:ℝ)≤2*L := by
    have h := Real.log_le_log qr (Nat.cast_le.mpr qm)
    dsimp [L]
    linarith
  have prod := mul_le_mul_of_nonneg_right pmax (show 0≤C*Real.sqrt M*L^2*(2*L)*L by positivity)
  have j := mul_le_mul_of_nonneg_left jcap (show 0≤p*C*Real.sqrt M*L^2*L by positivity)
  have pay := mul_le_mul_of_nonneg_right rcap (show 0≤4*C*Real.sqrt M*Real.sqrt e by positivity)
  apply (div_le_div_iff₀ (mul_pos mr (Real.sqrt_pos.mpr ep)) lp).mpr
  unfold deviationBound
  change p*(C*Real.sqrt M*L^2*(6+Real.log q))*L≤4*C*((M:ℝ)*Real.sqrt e)
  nlinarith only [prod,j,pay,congrArg (fun t : ℝ => 4*C*t*Real.sqrt e) eq3]

lemma rescale_pair_error {P m p e F G X Y : ℝ} (mp : 0<m) (pp : 0<p) (ep : 0<e)
    (disp : |P-e*(F/p)*(G/p)|≤X*Y+Real.sqrt e*(|F/p| *Y+|G/p| *X)) :
    let b := p*X/(m*Real.sqrt e)
    let c := p*Y/(m*Real.sqrt e)
    |p^2*P/(m^2*e)-(F/m)*(G/m)|≤b*c+|F/m| *c+|G/m| *b := by
  intro b c
  let A := p^2/(m^2*e)
  have ap : 0<A := by dsimp [A]; positivity
  have eq1 : p^2*P/(m^2*e)-(F/m)*(G/m)=A*(P-e*(F/p)*(G/p)) := by dsimp [A]; field_simp
  rw [eq1,abs_mul,abs_of_pos ap]
  apply (mul_le_mul_of_nonneg_left disp ap.le).trans_eq
  dsimp only [A,b,c]
  rw [abs_div,abs_div,abs_div,abs_div,abs_of_pos mp,abs_of_pos pp]
  have rt := Real.sq_sqrt ep.le
  field_simp
  rw [rt]
  ring

/-- Compare a congruence sum to the exact principal-character masses.
The bound is uniform in the shift and in every eligible dyadic lift. -/
theorem near_line_error (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g) :
    ∃ C D : ℝ, 0<C ∧ 0<D ∧ ∀ (z j H M : ℕ), 2≤z → 0<H → Even H →
      let q := liftedModulus z j
      let T := truncatedSeries H z
      let L := Real.log (M:ℝ)
      let U := principalMass q M f/M
      let V := principalMass q M g/M
      4≤q → q≤M → 6≤L → (q:ℝ)*L^8≤M → 1/2≤T → GRH q → ∀ sign : Bool,
      |(q:ℝ)*classPairs q H M M sign f g/((M:ℝ)^2*T)-U*V|≤
        (C/L)*(D/L)+|U| *(D/L)+|V| *(C/L) := by
  obtain ⟨C,D,cp,dp,all⟩ := prime_pair_dispersion f g hf hg
  refine ⟨4*C,4*D,by positivity,by positivity,?_⟩
  intro z j H M zz hp ev q T L U V q4 qm l6 cap low grh sign
  let p : ℝ := q.totient
  let e : ℝ := (allowed H q).card
  let B := deviationBound C q M
  let K := deviationBound D q M
  let P := classPairs q H M M sign f g
  have qr : 0<(q:ℝ) := by exact_mod_cast (NeZero.pos q)
  have mr : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have pp : 0<p := Nat.cast_pos.mpr (NeZero.pos _)
  have tp : 0<T := by linarith
  have eq : (q:ℝ)*e=T*p^2 := (div_eq_iff (pow_ne_zero _ pp.ne')).mp (lifted_density zz hp ev j)
  have ep : 0<e := pos_of_mul_pos_right (eq ▸ mul_pos tp (sq_pos_of_pos pp)) qr.le
  have den : p^2≤2*(q:ℝ)*e := by nlinarith only [eq,mul_le_mul_of_nonneg_right low (sq_nonneg p)]
  have bound := rescale_pair_error mr pp ep (all q H M M q4 qm qm grh sign)
  have left := rate qm (NeZero.pos q) l6 cap p e C pp ep cp den
  have right := rate qm (NeZero.pos q) l6 cap p e D pp ep dp den
  have logq : 0≤Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤q by omega))
  have lp : 0<L := by linarith
  have rp : 0≤p*K/((M:ℝ)*Real.sqrt e) := by dsimp [K,deviationBound]; positivity
  have eqP : (q:ℝ)*P/((M:ℝ)^2*T)=p^2*P/((M:ℝ)^2*e) := by
    field_simp
    nlinarith only [congrArg (fun t : ℝ => P*(M:ℝ)^2*t) eq,congrArg (fun t : ℝ => P*t) eq]
  change |(q:ℝ)*P/((M:ℝ)^2*T)-U*V|≤_
  rw [eqP]
  exact bound.trans (add_le_add (add_le_add (mul_le_mul left right rp (by positivity))
    (mul_le_mul_of_nonneg_left right (abs_nonneg U))) (mul_le_mul_of_nonneg_left left (abs_nonneg V)))

#print axioms near_line_error
end GoldbachSpectral435.GoldbachSieve
