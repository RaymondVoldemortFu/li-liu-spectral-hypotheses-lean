module
public import LiftedArcMeans
public import PrincipalArcPNT
public import MinorArcFrequencies
public import ArchimedeanFrequencies

/-! Rational major arcs for the ordinary prime Fourier sum with the
archimedean integral and the arithmetic coefficient evaluated separately. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open ConditionalGoldbach Finset Filter Complex MeasureTheory
namespace GoldbachSpectral435.CriticalCharacter
open GoldbachSieve

def archimedeanArc (f : ℝ→ℝ) (t : ℝ) : ℂ :=
  (unitIntegral (cosTest t f):ℂ)+I*(unitIntegral (sinTest t f):ℂ)

theorem archimedean_integral (f : ℝ→ℝ) (hf : FiniteModelWeight f) (t : ℝ) :
    archimedeanArc f t=∫ u : ℝ,(f u:ℂ)*Complex.exp ((t*u:ℝ)*I) := by
  have e (u : ℝ) : (f u:ℂ)*Complex.exp ((t*u:ℝ)*I)=
      complexTest (cosTest t f) u+I*complexTest (sinTest t f) u := by
    rw [Complex.exp_mul_I]
    simp only [complexTest,cosTest,sinTest,Complex.ofReal_mul,Complex.ofReal_sin,Complex.ofReal_cos]
    ring
  simp_rw [e]
  rw [integral_add (complex_test_integrable (cosWeight hf _)) ((complex_test_integrable (sinWeight hf _)).const_mul I),
    integral_const_mul,archimedeanArc,unitIntegral_eq (cosWeight hf _),unitIntegral_eq (sinWeight hf _)]
  simp only [complexTest,integral_complex_ofReal]

private lemma principal_exclusion (q M : ℕ) (qp : 0<q) (w : ℝ→ℝ) (F : ℝ) (bound : ∀ u, |w u|≤F) :
    |principalMass q M w-primeSum M w|≤F*((Nat.log 2 M:ℝ)*Real.log q) := by
  have fp := (abs_nonneg _).trans (bound 0)
  rw [principalMass,primeSum,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ n∈range M,F*excludedMass q n := by
      apply sum_le_sum
      intro n _
      by_cases cp : n.Coprime q
      · simp only [ite_eq_left cp,sub_self,abs_zero,excludedMass,mul_zero,le_refl]
      · simp only [ite_eq_right cp,zero_sub,abs_neg,excludedMass,weightedMangoldt,abs_mul,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact (mul_le_mul_of_nonneg_left (bound _) ArithmeticFunction.vonMangoldt_nonneg).trans_eq (mul_comm ..)
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (excluded_mass_bound q M qp) fp

theorem principal_arc_integral (f : ℝ→ℝ) (hf : FiniteModelWeight f) (A : ℝ) (ap : 0<A) :
    ∃ D K F : ℝ, 0<D ∧ 0<K ∧ 0≤F ∧ ∀ᶠ M : ℕ in atTop, ∀ q : ℕ, 0<q → ∀ t : ℝ,
      ‖principalArc q M f t-(M:ℂ)*archimedeanArc f t‖≤
        D*(1+|t|)*(K*M/(Real.log M)^A+1)+F*(Nat.log 2 M:ℝ)*Real.log q := by
  obtain ⟨D,K,dp,kp,est⟩ := oscillatory_pnt f hf A ap
  obtain ⟨F,b⟩ := hf.norm_bounded
  have flat (u : ℝ) : |f u|≤F := by simpa only [Complex.norm_real,Real.norm_eq_abs] using b u
  have fp := (abs_nonneg _).trans (flat 0)
  refine ⟨2*D,K,2*F,by positivity,kp,by positivity,?_⟩
  filter_upwards [est] with M bound
  intro q qp t
  let a := fun b => principalMass q M (trigTest b t f)-(M:ℝ)*unitIntegral (trigTest b t f)
  let E := D*(1+|t|)*(K*M/(Real.log M)^A+1)
  let V := F*((Nat.log 2 M:ℝ)*Real.log q)
  have both (j : Bool) : |a j|≤V+E := by
    let w := trigTest j t f
    have cap (u : ℝ) : |w u|≤F := by
      cases j <;> simp only [w,trigTest,Bool.false_eq_true,ite_false,ite_true,sinTest,cosTest,abs_mul]
      · exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans (flat _)
      · exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans (flat _)
    exact (abs_sub_le (principalMass q M w) (primeSum M w) ((M:ℝ)*unitIntegral w)).trans
      (add_le_add (principal_exclusion q M qp w F cap) (bound j t))
  have e : principalArc q M f t-(M:ℂ)*archimedeanArc f t=(a false:ℂ)+I*(a true:ℂ) := by
    simp only [a,principalArc,archimedeanArc,trigTest,Bool.false_eq_true,ite_false,ite_true,
      Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_natCast]
    ring
  rw [e]
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_I,one_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
  exact (add_le_add (both false) (both true)).trans_eq (by dsimp only [E,V]; ring)

/-- For every reduced rational, the integral term has coefficient μ(q)/φ(q).
All constants are independent of the center, the frequency, and the length. -/
theorem physical_major_arc (f : ℝ→ℝ) (hf : FiniteModelWeight f) (A : ℝ) (ap : 0<A) :
    ∃ C D K F : ℝ, 0<C ∧ 0<D ∧ 0<K ∧ 0≤F ∧ ∀ᶠ M : ℕ in atTop, ∀ (r : ℚ),
      4*r.den≤M → GRH (4*r.den) → ∀ ξ : ℝ,
      let t := 2*Real.pi*(M:ℝ)*(ξ-r)
      let q := r.den
      let Q := 4*q
      ‖primeFourier M f ξ-(ArithmeticFunction.moebius q:ℂ)/q.totient*((M:ℂ)*archimedeanArc f t)‖≤
        Real.sqrt Q*(C*(1+|t|)^4*Real.sqrt M*(6+Real.log Q))+
          D*(1+|t|)*(K*M/(Real.log M)^A+1)+F*(Nat.log 2 M:ℝ)*Real.log Q := by
  obtain ⟨C,G,cp,gp,circle⟩ := every_rational_arc f hf
  obtain ⟨D,K,F,dp,kp,fp,main⟩ := principal_arc_integral f hf A ap
  refine ⟨C,D,K,G+F,cp,dp,kp,add_nonneg gp fp,?_⟩
  filter_upwards [circle,main,eventually_ge_atTop (1:ℕ)] with M bound est mp
  intro r size grh ξ
  let t := 2*Real.pi*(M:ℝ)*(ξ-r)
  let q := r.den
  let Q := 4*q
  let a := (ArithmeticFunction.moebius q:ℂ)/q.totient
  have norm : ‖a‖≤1 := by
    have e := unit_mean_norm q (rationalPhase r)
    rwa [unitMean,primitive_additive_mean q _ (rational_injective r)] at e
  have p := bound q size grh (rationalPhase r) (rational_injective r) t
  have emb := est Q (Nat.mul_pos (by decide) r.pos) t
  have tr := dist_triangle (arcSum M f (rationalPhase r) t) (a*principalArc Q M f t) (a*((M:ℂ)*archimedeanArc f t))
  simp only [dist_eq_norm] at tr
  rw [← mul_sub,norm_mul] at tr
  rw [physical_rational_arc M mp f r ξ]
  exact tr.trans ((add_le_add p ((mul_le_of_le_one_left (norm_nonneg _) norm).trans emb)).trans_eq (by ring))

#print axioms physical_major_arc
end GoldbachSpectral435.CriticalCharacter
