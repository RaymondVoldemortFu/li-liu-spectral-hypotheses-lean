module
public import SquareCorrelations

/-! Bounds for the actual Li–Liu Hardy test coefficients on squares at the
finite conductor-dependent cutoff. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset ConditionalGoldbach Complex Filter
open scoped Topology ComplexConjugate
namespace GoldbachSpectral435.SquareResidues
open GoldbachSpectral435.PerronApproximation

def squareFloor (N : ℕ) := max 1 ⌈(Real.log N)^100⌉₊
def baseEnd (N : ℕ) := N^(exponent N)
def allIndices (N : ℕ) := range (⌊cutoff N (exponent N)⌋₊+1)
def largeSquares (N : ℕ) := squares (squareFloor N) (baseEnd N)

theorem square_subset (N : ℕ) : largeSquares N ⊆ allIndices N := by
  intro n hn
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hn
  have b : u≤baseEnd N := by have := (mem_Ico.mp hu).2; omega
  have id : cutoff N (exponent N) = (((baseEnd N)^2:ℕ):ℝ) := by simp [cutoff,baseEnd]
  change u^2 ∈ range (⌊cutoff N (exponent N)⌋₊+1)
  rw [id,Nat.floor_natCast,mem_range]
  exact Nat.lt_succ_of_le (Nat.pow_le_pow_left b 2)

lemma diagonal_vec (N n : ℕ) (big : Real.exp 10 < (N:ℝ)) (hn : 0<n) :
    ‖diagonalHardyVector (a:=alpha N) n‖ ≤ 3 := by
  have ap := large_alpha_pos big
  have ha := (large_parameters big).2.2
  have nr : 1≤(n:ℝ) := by exact_mod_cast hn
  have bd {x : ℝ} (xp : 0≤x) : (n:ℝ)^(-2*x)/(1+x) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact (Real.rpow_le_one_of_one_le_of_nonpos nr (by linarith)).trans (by linarith)
  have square := diagonalHardyVector_norm_sq ha ap.le n hn
  have key := mul_le_mul_of_nonneg_left (add_le_add (bd ap.le) (bd (by norm_num [beta] : 0≤beta))) Real.pi_pos.le
  nlinarith only [square,key,Real.pi_lt_four]

lemma coefficient_decay (N m n R : ℕ) (big : Real.exp 10 < (N:ℝ))
    (xm : 1<cutoff N m) (hn : 0<n) (nr : n≤R^2) (f : HardySpace (alpha N) beta) (hf : ‖f‖≤1) :
    ‖testCoefficient N m n f‖ ≤ (6*Real.log R)*(n:ℝ)^(-(1/2:ℝ)) := by
  have lg : mangoldt n ≤ 2*Real.log R := by
    apply ArithmeticFunction.vonMangoldt_le_log.trans
    have z := Real.log_le_log (by exact_mod_cast hn : 0<(n:ℝ)) (by exact_mod_cast nr : (n:ℝ)≤((R^2:ℕ):ℝ))
    simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] using z
  have hW := smoothedPerronWeight_nonneg_le_one xm n
  have ip : ‖inner ℂ f (diagonalHardyVector n)‖ ≤ 3 :=
    (norm_inner_le_norm _ _).trans (by
      simpa using mul_le_mul hf (diagonal_vec N _ big hn) (norm_nonneg _) zero_le_one)
  have cp : ‖(n:ℂ)^(-(1/2:ℂ))‖ = (n:ℝ)^(-(1/2:ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hn]; norm_num
  have lg0 := ArithmeticFunction.vonMangoldt_nonneg (n:=n)
  change 0≤mangoldt n at lg0
  unfold testCoefficient
  simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,cp,
    abs_of_nonneg lg0,abs_of_nonneg hW.1]
  calc
    _ ≤ ((2*Real.log R)*(n:ℝ)^(-(1/2:ℝ)))*1*3 := by gcongr <;> first | exact hW.1 | exact hW.2
    _ = _ := by ring

private lemma square_coefficient (N m u R : ℕ) (big : Real.exp 10 < (N:ℝ))
    (xm : 1<cutoff N m) (hu : 0<u) (ur : u≤R) (f : HardySpace (alpha N) beta) (hf : ‖f‖≤1) :
    ‖testCoefficient N m (u^2) f‖ ≤ (6*Real.log R)/u := by
  apply (coefficient_decay N m (u^2) R big xm (pow_pos hu 2) (Nat.pow_le_pow_left ur 2) f hf).trans_eq
  rw [Nat.cast_pow,← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num [Real.rpow_neg_one,div_eq_mul_inv]

theorem parameters (N : ℕ) (big : Real.exp 10<(N:ℝ)) :
    1≤baseEnd N ∧ 1<cutoff N (exponent N) ∧
    Real.log (baseEnd N) ≤ 102*(Real.log N)^2 := by
  have four := (large_parameters big).1
  have nr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have l1 : 1≤Real.log N := by linarith [(Real.lt_log_iff_exp_lt (by positivity : 0<(N:ℝ))).mpr big]
  have ll : 0≤Real.log (Real.log N) := Real.log_nonneg l1
  have m1 : 1≤exponent N := le_max_left ..
  have e : (exponent N:ℝ) ≤ 102*Real.log N := by
    unfold exponent
    rw [Nat.cast_max,Nat.cast_one]
    apply max_le (by linarith)
    have ceil := Nat.ceil_lt_add_one (by positivity : 0≤100*Real.log (Real.log N))
    linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one l1)]
  refine ⟨Nat.one_le_pow _ _ (by omega),one_lt_pow₀ (one_lt_pow₀ nr (by omega)) (by decide),?_⟩
  rw [baseEnd,Nat.cast_pow,Real.log_pow]
  nlinarith only [mul_le_mul_of_nonneg_right e (show 0≤Real.log N by linarith)]

/-- The choice of a polylogarithmic lower bound for the base is compatible
with the Vandermonde spacing inequality on every sufficiently large level. -/
theorem floor_fits : ∀ᶠ N : ℕ in atTop, (squareFloor N)^3 < N := by
  have infR := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have small : (fun x : ℝ => (Real.log x)^300) =o[atTop] (fun x : ℝ => x) := by
    simpa only [Real.rpow_natCast,Real.rpow_one] using isLittleO_log_rpow_rpow_atTop (300:ℕ) (show (0:ℝ)<1 by norm_num)
  have lim := (small.bound (show (0:ℝ)<1/16 by norm_num)).filter_mono (le_refl _)
  filter_upwards [infR.eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually lim] with N ln bound
  have np : 0≤(N:ℝ) := Nat.cast_nonneg _
  change 1 ≤ Real.log (N:ℝ) at ln
  have l0 := zero_le_one.trans ln
  have L1 : 1≤(Real.log N)^100 := one_le_pow₀ ln
  have yl : (squareFloor N:ℝ) ≤ 2*(Real.log N)^100 := by
    unfold squareFloor
    rw [Nat.cast_max,Nat.cast_one]
    exact max_le (by linarith) (by linarith [Nat.ceil_lt_add_one (pow_nonneg l0 100)])
  have npos : 0<(N:ℝ) := by
    by_contra! h
    have z := le_antisymm h np
    rw [z,Real.log_zero] at ln
    linarith
  have b : (Real.log N)^300 ≤ (1/16)*(N:ℝ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg np,abs_of_nonneg (pow_nonneg l0 300)] using bound
  have cube := pow_le_pow_left₀ (Nat.cast_nonneg _) yl 3
  have eq : (2*(Real.log N)^100)^3=8*(Real.log N)^300 := by ring
  exact_mod_cast (show (squareFloor N:ℝ)^3<(N:ℝ) by linarith only [cube,eq,b,npos])

def amplitude {N : ℕ} (I : Finset ℕ) (c : ℕ → ℂ) (χ : Character N) : ℂ :=
  ∑ n ∈ I, c n*χ n

def meanEnergy (N : ℕ) [NeZero N] (F : Character N → ℂ) : ℝ :=
  (2/(N.totient:ℝ))*∑ χ ∈ oddCharacters N, ‖F χ‖^2

def diagonalEnergy (N : ℕ) (I : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ n ∈ I, if n.Coprime N then ‖c n‖^2 else 0

/-- Both the odd-character second moment and the independent diagonal of
the discarded squares are uniformly small for every unit Hardy test. -/
theorem large_square_energy (N : ℕ) [NeZero N] (he : Even N) (big : Real.exp 10<(N:ℝ))
    (fit : (squareFloor N)^3<N) (f : HardySpace (alpha N) beta) (hf : ‖f‖≤1) :
    let c := fun n => testCoefficient N (exponent N) n f
    let K : ℝ := 4*612^2*103*104
    meanEnergy N (amplitude (largeSquares N) c) ≤ K/(Real.log N)^92 ∧
      diagonalEnergy N (largeSquares N) c ≤ K/(Real.log N)^92 := by
  intro c K
  let R := baseEnd N
  let Y := squareFloor N
  let L := Real.log N
  let B := 6*Real.log R
  have ⟨rp,xp,rl⟩ := parameters N big
  have l1 : 1≤L := by
    have np : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
    dsimp [L]; linarith [(Real.lt_log_iff_exp_lt np).mpr big]
  have lp : 0<L := zero_lt_one.trans_le l1
  have hr : 1≤R := rp
  have log0 : 0≤Real.log R := Real.log_nonneg (by exact_mod_cast hr)
  have b0 : 0≤B := by dsimp [B]; positivity
  have hy : 0<Y := lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)
  have yr : L^100 ≤ (Y:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..))
  have cap (u : ℕ) (hu : u∈Ico Y (R+1)) : ‖c (u^2)‖ ≤ B/u :=
    square_coefficient N _ u R big xp (hy.trans_le (mem_Ico.mp hu).1)
      (Nat.le_of_lt_succ (mem_Ico.mp hu).2) f hf
  have bound : 4*B^2*(1+Real.log R)*(2+Real.log R)/Y ≤ K/L^92 := by
    have L2 : 1≤L^2 := one_le_pow₀ l1
    have b : B ≤ 612*L^2 := by dsimp [B,R,L]; linarith only [rl]
    have r1 : 1+Real.log R ≤ 103*L^2 := by change Real.log R ≤ 102*L^2 at rl; linarith
    have r2 : 2+Real.log R ≤ 104*L^2 := by linarith
    calc
      _ ≤ 4*(612*L^2)^2*(103*L^2)*(104*L^2)/(L^100) := by gcongr
      _ = _ := by dsimp [K]; field_simp
  refine ⟨(square_mean N Y R he (large_parameters big).1 fit hy hr c b0 cap).trans bound,?_⟩
  unfold diagonalEnergy
  change ∑ n ∈ squares Y R, _ ≤ _
  rw [sum_squares]
  have term (u : ℕ) (hu : u∈Ico Y (R+1)) :
      (if (u^2).Coprime N then ‖c (u^2)‖^2 else 0) ≤ (B/Y)*(B*(1/u)) := by
    have u0 : (0:ℝ)<u := by exact_mod_cast hy.trans_le (mem_Ico.mp hu).1
    have y0 : (0:ℝ)<Y := by exact_mod_cast hy
    have yu : (Y:ℝ) ≤ u := by exact_mod_cast (mem_Ico.mp hu).1
    have lo := (cap u hu).trans (div_le_div_of_nonneg_left b0 y0 yu)
    split_ifs
    · simpa only [sq,div_eq_mul_inv,one_mul] using mul_le_mul lo (cap u hu) (norm_nonneg _) (div_nonneg b0 y0.le)
    · positivity
  apply (sum_le_sum term).trans
  simp_rw [← mul_sum]
  have harm := harmonic_interval (R:=R) hy
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left harm b0) (by positivity : 0≤B/Y)).trans
  apply le_trans _ bound
  have base : 1 ≤ 4*(2+Real.log R) := by linarith
  have pos : 0≤B^2*(1+Real.log R) := by positivity
  have ineq := mul_le_mul_of_nonneg_left base pos
  calc
    _ = (B^2*(1+Real.log R))/Y := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [ineq]) (Nat.cast_nonneg _)

private lemma gram_mean (N : ℕ) [NeZero N] (he : Even N) (four : 4≤N)
    (f : HardySpace (alpha N) beta) :
    (meanEnergy N (amplitude (allIndices N) (fun n => testCoefficient N (exponent N) n f)):ℂ) =
    inner ℂ f (primeGram N (exponent N) f) := by
  rw [gram_quadratic N _ he four]
  exact odd_character_quadratic_complex N he four _ _

theorem full_mean_bound : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
    Real.exp 10<(N:ℝ) → GRH N → ∀ f : HardySpace (alpha N) beta, ‖f‖≤1 →
    meanEnergy N (amplitude (allIndices N) (fun n => testCoefficient N (exponent N) n f)) ≤
      C*(Real.log N)^2 := by
  obtain ⟨K,hK,err⟩ := operator_error
  obtain ⟨A,hA,M⟩ := lemma_6_4
  refine ⟨K+4*A,by positivity,?_⟩
  intro N inst he big g f hf
  obtain ⟨four,lp,ha⟩ := large_parameters big
  have l1 : 1≤Real.log N := by
    have np : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
    linarith [(Real.lt_log_iff_exp_lt np).mpr big]
  have mean := arithmeticOperator_trace_bound_of_average N big g ha A hA.le
    (fun x xp xb => (M N inst he big g x xp xb).2)
  have ar := (mean.1.isHilbertSchmidt.norm_le_hsNorm.trans mean.2.1).trans mean.2.2
  have ar' : ‖arithmeticOperator ha N‖ ≤ 4*A*(Real.log N)^2 := by
    convert ar using 1; simp [alpha,one_div]; ring
  have m1 : 1≤exponent N := le_max_left ..
  have hm : 100*Real.log (Real.log N) ≤ exponent N := (Nat.le_ceil _).trans
    (Nat.cast_le.mpr (le_max_right ..))
  have e := err N inst he big g ha (exponent N) m1 hm
  have gcap : ‖primeGram N (exponent N)‖ ≤ (K+4*A)*(Real.log N)^2 := by
    have dist := norm_sub_norm_le (primeGram N (exponent N)) (arithmeticOperator ha N)
    rw [norm_sub_rev] at dist
    have kd := div_le_self hK.le (one_le_pow₀ (n:=16) l1)
    nlinarith only [dist,e,kd,ar',mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=2) l1) hK.le]
  have cast := congrArg norm (gram_mean N he four f)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by unfold meanEnergy; positivity)] at cast
  rw [cast]
  exact (norm_inner_le_norm _ _).trans ((mul_le_mul hf
    (((primeGram N (exponent N)).le_opNorm f).trans (mul_le_of_le_one_right (norm_nonneg _) hf))
    (norm_nonneg _) zero_le_one).trans (by simpa using gcap))

/-- Removing a subfamily of coefficients costs its own energy and a mixed
term. The free parameter controls the mixed term uniformly. -/
theorem mean_delete (N : ℕ) [NeZero N] (I J : Finset ℕ) (sub : J⊆I) (c : ℕ→ℂ)
    (q : ℝ) (qp : 0<q) :
    |meanEnergy N (amplitude I c)-meanEnergy N (amplitude (I\J) c)| ≤
      meanEnergy N (amplitude I c)/q^2+(1+q^2)*meanEnergy N (amplitude J c) := by
  classical
  let w : ℝ := 2/N.totient
  have w0 : 0≤w := by dsimp [w]; positivity
  have scalar (z u : ℂ) :
      |‖z‖^2-‖z-u‖^2| ≤ ‖z‖^2/q^2+(1+q^2)*‖u‖^2 := by
    have dist := abs_norm_sub_norm_le z (z-u)
    rw [sub_sub_cancel] at dist
    have tri := norm_sub_le z u
    have young : 2*‖z‖*‖u‖ ≤ ‖z‖^2/q^2+q^2*‖u‖^2 := by
      have sqn := sq_nonneg (‖z‖/q-q*‖u‖)
      field_simp [qp.ne'] at sqn ⊢
      nlinarith only [sqn]
    rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    have b := mul_le_mul dist (show ‖z‖+‖z-u‖ ≤ 2*‖z‖+‖u‖ by linarith only [tri])
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg u)
    linarith only [b,young,show ‖u‖*(2*‖z‖+‖u‖)=2*‖z‖*‖u‖+‖u‖^2 by ring,
      show (1+q^2)*‖u‖^2 = ‖u‖^2 + q^2*‖u‖^2 by ring]
  have id (χ : Character N) : amplitude (I\J) c χ = amplitude I c χ-amplitude J c χ :=
    eq_sub_of_add_eq (Finset.sum_sdiff sub)
  unfold meanEnergy
  rw [← mul_sub,abs_mul,abs_of_nonneg w0,← sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) w0).trans
  calc
    _ ≤ w*∑ χ ∈ oddCharacters N, (‖amplitude I c χ‖^2/q^2+(1+q^2)*‖amplitude J c χ‖^2) := by
      apply mul_le_mul_of_nonneg_left _ w0
      apply sum_le_sum
      intro χ _
      rw [id]
      exact scalar _ _
    _ = _ := by rw [sum_add_distrib,← sum_div,← mul_sum]; dsimp [w]; ring

def finiteForm (N : ℕ) [NeZero N] (I : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  meanEnergy N (amplitude I c)-diagonalEnergy N I c

theorem full_form (N : ℕ) [NeZero N] (he : Even N) (four : 4≤N) (f : HardySpace (alpha N) beta) :
    (finiteForm N (allIndices N) (fun n => testCoefficient N (exponent N) n f):ℂ) =
      primePairForm N (exponent N) f := by
  rw [← off_diagonal_quadratic N _ he four,sub_apply,inner_sub_right,finiteForm,Complex.ofReal_sub,
    gram_mean N he four,diagonal_quadratic]
  congr 1
  unfold diagonalEnergy allIndices
  simp only [Complex.ofReal_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem form_delete (N : ℕ) [NeZero N] (I J : Finset ℕ) (sub : J⊆I) (c : ℕ→ℂ)
    (q : ℝ) (qp : 0<q) :
    |finiteForm N I c-finiteForm N (I\J) c| ≤
      meanEnergy N (amplitude I c)/q^2+(1+q^2)*meanEnergy N (amplitude J c)+diagonalEnergy N J c := by
  have ed : diagonalEnergy N (I\J) c+diagonalEnergy N J c=diagonalEnergy N I c := Finset.sum_sdiff sub
  have dp : 0≤diagonalEnergy N J c := by unfold diagonalEnergy; positivity
  unfold finiteForm
  rw [← ed,show meanEnergy N (amplitude I c) - (diagonalEnergy N (I\J) c + diagonalEnergy N J c) -
    (meanEnergy N (amplitude (I\J) c) - diagonalEnergy N (I\J) c) =
    (meanEnergy N (amplitude I c) - meanEnergy N (amplitude (I\J) c))-diagonalEnergy N J c by ring]
  exact (abs_sub _ _).trans (add_le_add (mean_delete N I J sub c q qp) (abs_of_nonneg dp).le)

/-- A uniform energy bound on discarded coefficients controls every mixed term
in the quadratic form of the original residual. -/
theorem trim_error (J : ℕ → Finset ℕ) (sub : ∀ N, J N ⊆ allIndices N)
    (K : ℝ) (hk : 0<K) (good : ∀ᶠ N : ℕ in atTop, ∀ (_ : NeZero N), Even N →
      Real.exp 10<(N:ℝ) → GRH N → ∀ f : HardySpace (alpha N) beta, ‖f‖≤1 →
      let c := fun n => testCoefficient N (exponent N) n f
      meanEnergy N (amplitude (J N) c) ≤ K/(Real.log N)^40 ∧
        diagonalEnergy N (J N) c ≤ K/(Real.log N)^40) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ (_ : NeZero N), Even N →
      Real.exp 10<(N:ℝ) → GRH N → ∀ (ha : alpha N<beta) (f : HardySpace (alpha N) beta),
      ‖f‖≤1 → ‖inner ℂ f (residualOperator ha N f) -
        ((finiteForm N (allIndices N\J N) (fun n => testCoefficient N (exponent N) n f):ℂ) -
         inner ℂ f (modelOperator ha N f))‖ ≤ C/(Real.log N)^16 := by
  obtain ⟨A,ap,full⟩ := full_mean_bound
  obtain ⟨B,bp,err⟩ := prime_pair_error
  refine ⟨B+A+3*K,by positivity,?_⟩
  filter_upwards [good] with N hN
  intro inst he big g ha f hf
  let L := Real.log N
  let c := fun n => testCoefficient N (exponent N) n f
  have l1 : 1≤L := by
    have np : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
    dsimp [L]; linarith [(Real.lt_log_iff_exp_lt np).mpr big]
  have lp : 0<L := zero_lt_one.trans_le l1
  have ⟨em,ed⟩ := hN inst he big g f hf
  have h := form_delete N _ _ (sub N) c (L^9) (by positivity)
  have hfull := full N inst he big g f hf
  have bnd : |finiteForm N (allIndices N) c - finiteForm N (allIndices N\J N) c| ≤
      (A+3*K)/L^16 := by
    apply h.trans
    calc
      _ ≤ (A*L^2)/(L^9)^2+(2*L^18)*(K/L^40)+K/L^40 := by
        have coef : 1+(L^9)^2 ≤ 2*L^18 := by
          rw [← pow_mul]; norm_num
          linarith only [one_le_pow₀ (n:=18) l1]
        exact add_le_add (add_le_add (div_le_div_of_nonneg_right hfull (by positivity))
          (mul_le_mul coef em (by unfold meanEnergy; positivity) (by positivity))) ed
      _ = A/L^16+2*(K/L^22)+K/L^40 := by field_simp
      _ ≤ A/L^16+2*(K/L^16)+K/L^16 := by gcongr <;> decide
      _ = _ := by ring
  have e := err N inst he big g ha f
  rw [← full_form N he (large_parameters big).1 f] at e
  have close := norm_add_le
    (inner ℂ f (residualOperator ha N f) -
      ((finiteForm N (allIndices N) c:ℂ)-inner ℂ f (modelOperator ha N f)))
    ((finiteForm N (allIndices N) c:ℂ) - (finiteForm N (allIndices N\J N) c:ℂ))
  rw [show ∀ a b d e : ℂ, (a-(b-d))+(b-e)=a-(e-d) by intros; ring] at close
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at close
  apply close.trans
  have unit : ‖f‖^2 ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg _) hf 2
  have first := e.trans (mul_le_of_le_one_right (by positivity) unit)
  exact (add_le_add first bnd).trans_eq (by dsimp [L]; ring)

#print axioms trim_error
#print axioms large_square_energy
end GoldbachSpectral435.SquareResidues
