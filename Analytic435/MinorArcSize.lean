module
public import RationalPrimeArcs

/-! Size of a prime exponential sum near a rational with a large
denominator. The principal term is bounded using the exact Ramanujan sum. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open ConditionalGoldbach Finset Filter Complex
namespace GoldbachSpectral435.CriticalCharacter
open GoldbachSieve

/-- Uniform elementary lower bound for Euler's totient. -/
theorem totient_square_bound (n : ℕ) : n≤2*n.totient^2 := by
  suffices ∀ n : ℕ, n≤2*n.totient^2 ∧ (Odd n → n≤n.totient^2) from (this n).1
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases z : n=0
    · simp [z]
    by_cases o : n=1
    · simp [o]
    obtain ⟨p,pp,m,rfl⟩ := Nat.exists_prime_and_dvd o
    have mp : 0<m := Nat.pos_of_ne_zero (fun h => z (by simp [h]))
    have small : m<p*m := by simpa using Nat.mul_lt_mul_of_pos_right pp.one_lt mp
    obtain ⟨cap,oddCap⟩ := ih m small
    by_cases two : p=2
    · subst p
      have even : ¬Odd (2*m) := by simp
      refine ⟨?_,fun odd => (even odd).elim⟩
      by_cases dvd : 2∣m
      · rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two dvd]
        nlinarith
      · have om : Odd m := Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp dvd)
        rw [Nat.totient_two_mul_of_odd om]
        exact Nat.mul_le_mul_left 2 (oddCap om)
    · have p3 : 3≤p := by have := pp.two_le; omega
      have fac : p≤(p-1)^2 := by
        have r : 2≤p-1 := by omega
        have eq : p=(p-1)+1 := by omega
        nlinarith
      have mult := Nat.totient_super_multiplicative p m
      rw [Nat.totient_prime pp] at mult
      have sq := Nat.pow_le_pow_left mult 2
      rw [mul_pow] at sq
      refine ⟨(Nat.mul_le_mul fac cap).trans (by nlinarith only [sq]),?_⟩
      intro odd
      exact (Nat.mul_le_mul fac (oddCap (Nat.odd_mul.mp odd).2)).trans sq

private lemma principal_arc_size (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ K : ℝ, 0<K ∧ ∀ q M t, ‖principalArc q M f t‖≤K*M := by
  obtain ⟨F,fb⟩ := hf.norm_bounded
  have cap (u : ℝ) : |f u|≤F := by simpa only [Complex.norm_real,Real.norm_eq_abs] using fb u
  have fp := (abs_nonneg _).trans (cap 0)
  let K := Real.log 4+4
  have kp : 0<K := by dsimp [K]; positivity
  refine ⟨2*(F+1)*K,by positivity,?_⟩
  intro q M t
  have U (b : Bool) : |principalMass q M (trigTest b t f)|≤F*(K*M) := by
    let w := trigTest b t f
    have norm (u : ℝ) : |w u|≤F := by
      cases b <;> simp only [w,trigTest,Bool.false_eq_true,ite_false,ite_true,cosTest,sinTest,abs_mul]
      · exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans (cap _)
      · exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans (cap _)
    have crude : (∑ n∈range M,mangoldt n)≤K*M := by
      have extend := sum_le_sum_of_subset_of_nonneg (range_mono (show M≤M+1 by omega))
        (f:=mangoldt) (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      apply extend.trans
      have ps := Chebyshev.psi_le_const_mul_self (x:=(M:ℝ)) (by positivity)
      simpa only [Chebyshev.psi_eq_sum_range,Nat.floor_natCast] using ps
    unfold principalMass
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ n∈range M,F*mangoldt n := by
        apply sum_le_sum
        intro n _
        split
        · rw [weightedMangoldt,abs_mul,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact (mul_le_mul_of_nonneg_left (norm _) ArithmeticFunction.vonMangoldt_nonneg).trans_eq (mul_comm ..)
        · rw [abs_zero]; positivity
      _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left crude fp
  have tri := norm_add_le (principalMass q M (cosTest t f):ℂ) (I*(principalMass q M (sinTest t f):ℂ))
  simp only [norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at tri
  have C := U false
  have S := U true
  change |principalMass q M (cosTest t f)|≤_ at C
  change |principalMass q M (sinTest t f)|≤_ at S
  apply tri.trans
  linarith only [C,S,mul_nonneg kp.le (Nat.cast_nonneg (α:=ℝ) M)]

/-- The three terms measure the error from the nonprincipal characters,
the density of the principal additive phase, and the prime powers dividing q. -/
theorem arc_size_bound (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C K F : ℝ, 0<C ∧ 0<K ∧ 0≤F ∧ ∀ᶠ M : ℕ in atTop, ∀ (q : ℕ) [NeZero q],
      4≤q → q≤M → GRH q → ∀ (ψ : AddChar (ZMod q) ℂ), Function.Injective ψ → ∀ t : ℝ,
      ‖arcSum M f ψ t‖≤Real.sqrt q*(C*(1+|t|)^4*Real.sqrt M*(6+Real.log q))+
        (2*K)*M/Real.sqrt q+F*(Nat.log 2 M:ℝ)*Real.log q := by
  obtain ⟨C,F,cp,fp,all⟩ := rational_arc_bound f hf
  obtain ⟨K,kp,main⟩ := principal_arc_size f hf
  refine ⟨C,K,F,cp,kp,fp,?_⟩
  filter_upwards [all] with M est
  intro q inst q4 qm grh ψ inj t
  have qp : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have phi : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have mp : 0≤(M:ℝ) := Nat.cast_nonneg _
  have root : Real.sqrt q≤2*(q.totient:ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    have bound : (q:ℝ)≤2*(q.totient:ℝ)^2 := by exact_mod_cast totient_square_bound q
    nlinarith only [bound,sq_nonneg (q.totient:ℝ)]
  have mu : ‖(ArithmeticFunction.moebius q:ℂ)‖≤1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=q)
  let a := (ArithmeticFunction.moebius q:ℂ)/q.totient
  have m : ‖a*principalArc q M f t‖≤(2*K)*M/Real.sqrt q := by
    rw [norm_mul,show ‖a‖=_ from norm_div ..,Complex.norm_natCast]
    apply (mul_le_mul (div_le_div_of_nonneg_right mu phi.le) (main q M t)
      (norm_nonneg _) (by positivity : 0≤1/(q.totient:ℝ))).trans
    apply (le_div_iff₀ (Real.sqrt_pos.mpr qp)).mpr
    rw [one_div,← div_eq_inv_mul,div_mul_eq_mul_div,div_le_iff₀ phi]
    have scale := mul_le_mul_of_nonneg_left root (mul_nonneg kp.le mp)
    linarith only [scale]
  have tri := norm_add_le (arcSum M f ψ t-a*principalArc q M f t) (a*principalArc q M f t)
  rw [sub_add_cancel] at tri
  exact tri.trans ((add_le_add (est q q4 qm grh ψ inj t) m).trans_eq (by ring))

#print axioms totient_square_bound
#print axioms arc_size_bound
end GoldbachSpectral435.CriticalCharacter
