module
public import Reflection
public import PrimeHyperbola

/-! Direct bounds for asymmetric physical windows of the original operator. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex Finset
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PhysicalHyperbola
open GoldbachSpectral435.PerronApproximation GoldbachSpectral435.LocalPrimeForm
open GoldbachSpectral435.Reflection GoldbachSpectral435.PrimeHyperbola

private lemma coefficient_bound {N n W : ℕ} (big : Real.exp 10<(N:ℝ))
    (np : 0<n) (nw : n≤W) (f : HardySpace (alpha N) beta) (hf : ‖f‖≤1) :
    ‖coefficient f n‖ ≤ 3*Real.log W*(n:ℝ)^(-(1/2:ℝ)) := by
  have pos : 0<(n:ℝ) := by exact_mod_cast np
  have ml : mangoldt n ≤ Real.log W := ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log pos (Nat.cast_le.mpr nw))
  have mn : 0≤mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have ip : ‖inner ℂ f (diagonalHardyVector n)‖ ≤ 3 := (norm_inner_le_norm _ _).trans
    (by simpa using mul_le_mul hf (SquareResidues.diagonal_vec N n big np) (norm_nonneg _) zero_le_one)
  have pow : ‖(n:ℂ)^(-(1/2:ℂ))‖ = (n:ℝ)^(-(1/2:ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos np]; norm_num
  simp only [coefficient,norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg mn,pow]
  calc
    _ ≤ (Real.log W*(n:ℝ)^(-(1/2:ℝ)))*3 := by gcongr
    _ = _ := by ring

private lemma skip_zero (I : Finset ℕ) (f : ℕ→ℝ) (h : f 0=0) :
    ∑ n ∈ I, f n=∑ n ∈ I.erase 0, f n := by
  by_cases m : 0∈I
  · simpa only [h,add_zero] using (sum_erase_add I f m).symm
  · rw [erase_eq_of_notMem m]

/-- With W=max(Y,Z), the signed arithmetic term on these two windows is
bounded by an explicit logarithmic factor times sqrt(Y Z)/N. The estimate
holds at the critical boundary, on the entire pair of Hilbert unit balls. -/
theorem rectangle_bound (N Y Z : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (yp : 0<Y) (zp : 0<Z) (x y : HardySpace (alpha N) beta)
    (xn : ‖x‖≤1) (yn : ‖y‖≤1)
    (hx : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → x t=0)
    (hy : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Z → y t=0) :
    let W := max Y Z
    ‖inner ℂ x ((arithmeticOperator ha N-diagonalOperator ha N) y)‖ ≤
      18*(3*Real.log W)^2*(Real.sqrt ((Y:ℝ)*Z)/N)*(1+Real.log (W+1:ℕ))^2 := by
  intro W
  have yw : Y≤W := le_max_left ..
  have zw : Z≤W := le_max_right ..
  have wp := yp.trans_le yw
  rw [mixed_local_pairs N W even big grh ha wp x y (widen yp yw x hx) (widen zp zw y hy)]
  let I := range W
  let J := I.erase 0
  let Q := Real.sqrt ((Y:ℝ)*Z)
  let c (n : ℕ) : ℂ := ((max ‖coefficient x n‖ ‖coefficient y n‖ : ℝ):ℂ)
  let v (n j : ℕ) := coefficient x n*conj (coefficient y j)*offDiagonalSign N n j
  have cn (n : ℕ) : ‖c n‖=max ‖coefficient x n‖ ‖coefficient y n‖ :=
    Complex.norm_real _ |>.trans (Real.norm_of_nonneg ((norm_nonneg _).trans (le_max_left ..)))
  have cp : J⊆Icc 1 W := by
    intro n hn
    obtain ⟨nz,ni⟩ := mem_erase.mp hn
    exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero nz,(mem_range.mp ni).le⟩
  have cap (n : ℕ) (hn : n∈J) : ‖c n‖≤3*Real.log W*(n:ℝ)^(-(1/2:ℝ)) := by
    obtain ⟨np,nw⟩ := mem_Icc.mp (cp hn)
    rw [cn]
    exact max_le (coefficient_bound big np nw x xn) (coefficient_bound big np nw y yn)
  have lg : 0≤Real.log W := Real.log_nonneg (by exact_mod_cast wp : (1:ℝ)≤W)
  have h := hyperbola_bound (NeZero.pos N) J cp c (Q:=Q) (Real.sqrt_nonneg _) (by positivity : 0≤3*Real.log W) cap
  have term (n j : ℕ) : ‖v n j‖≤
      if Real.sqrt ((n:ℝ)*j)≤Q then ‖pairTerm N n j c‖ else 0 := by
    split_ifs with sel
    · simp only [v,pairTerm,norm_mul,RCLike.norm_conj,cn]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left ..) (le_max_right ..)
        (norm_nonneg _) ((norm_nonneg _).trans (le_max_left ..))) (norm_nonneg _)
    · by_cases ny : Y≤n
      · simp [v,sample_zero yp ny (large_alpha_pos big).le ha x hx]
      · have zj : Z≤j := by
          by_contra! jl
          apply sel
          exact Real.sqrt_le_sqrt (mul_le_mul (Nat.cast_le.mpr (Nat.le_of_not_ge ny))
            (Nat.cast_le.mpr jl.le) (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        simp [v,sample_zero zp zj (large_alpha_pos big).le ha y hy]
  have z (f : HardySpace (alpha N) beta) : coefficient f 0=0 := by simp [coefficient,mangoldt]
  change ‖∑ n ∈ I, ∑ j ∈ I, v n j‖≤_
  calc
    _ ≤ ∑ n ∈ I, ∑ j ∈ I, ‖v n j‖ := (norm_sum_le ..).trans (sum_le_sum (fun n _ => norm_sum_le ..))
    _ = ∑ n ∈ J, ∑ j ∈ J, ‖v n j‖ := by
      rw [skip_zero I _ (by simp [v,z] : (∑ j ∈ I, ‖v 0 j‖)=0)]
      apply sum_congr rfl
      intro n _
      exact skip_zero I _ (by simp [v,z])
    _ ≤ _ := (sum_le_sum (fun n _ => sum_le_sum (fun j _ => term n j))).trans h

/-- At the original boundary these entire rectangular blocks decay even
when the geometric mean of their physical endpoints is only six powers
of log N below the modulus. -/
theorem critical_rectangle (N Y Z : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (yp : 0<Y) (zp : 0<Z)
    (size : max Y Z ≤ N^2) (cut : Real.sqrt ((Y:ℝ)*Z)≤N/(Real.log N)^6)
    (x y : HardySpace (alpha N) beta) (xn : ‖x‖≤1) (yn : ‖y‖≤1)
    (hx : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → x t=0)
    (hy : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Z → y t=0) :
    ‖inner ℂ x ((arithmeticOperator ha N-diagonalOperator ha N) y)‖ ≤ 10368/(Real.log N)^2 := by
  let W := max Y Z
  let L := Real.log N
  have np : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have lp : 0<L := (large_parameters big).2.1
  have l1 : 1≤L := by dsimp only [L]; linarith [(Real.lt_log_iff_exp_lt np).mpr big]
  have wp := yp.trans_le (le_max_left Y Z)
  have wr : 0<(W:ℝ) := by exact_mod_cast wp
  have lg : 0≤Real.log W := Real.log_nonneg (by exact_mod_cast wp : (1:ℝ)≤W)
  have lw : Real.log W≤2*L := by
    simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat,L] using
      Real.log_le_log wr (Nat.cast_le.mpr size)
  have lwp : 0≤1+Real.log (W+1:ℕ) := by
    have := Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 W) : (1:ℝ)≤(W+1:ℕ))
    linarith
  have lh : 1+Real.log (W+1:ℕ)≤4*L := by
    have wr1 : ((W+1:ℕ):ℝ)≤2*W := by exact_mod_cast (show W+1≤2*W by omega)
    have t := Real.log_le_log (by positivity : 0<((W+1:ℕ):ℝ)) wr1
    rw [Real.log_mul (by norm_num) wr.ne'] at t
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have q : Real.sqrt ((Y:ℝ)*Z)/N ≤ 1/L^6 := by
    apply (div_le_iff₀ np).mpr
    exact cut.trans_eq (by dsimp [L]; ring)
  have b := rectangle_bound N Y Z even big grh ha yp zp x y xn yn hx hy
  apply b.trans
  change 18*(3*Real.log W)^2*(Real.sqrt ((Y:ℝ)*Z)/N)*(1+Real.log (W+1:ℕ))^2 ≤ _
  calc
    _ ≤ 18*(3*(2*L))^2*(1/L^6)*(4*L)^2 := by gcongr
    _ = _ := by change _ = 10368/L^2; field_simp; ring

#print axioms critical_rectangle
#print axioms rectangle_bound
end GoldbachSpectral435.PhysicalHyperbola
