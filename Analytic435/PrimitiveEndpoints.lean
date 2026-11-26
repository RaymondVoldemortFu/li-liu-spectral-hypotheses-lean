module
public import ReflectionEnergy

/-! Removing the intervals below the first prime from the normalized
first-block estimate. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Finset
namespace GoldbachSpectral435.GoldbachPrimitive

def cutoffWeight (N : ℕ) (u : ℝ) : ℝ := 1-Real.exp (-(N*u))
def bridge (N : ℕ) (u : ℝ) : ℝ := primitive N u-u*primitive N 1

lemma cutoff_smooth (N : ℕ) : ContDiff ℝ 6 (cutoffWeight N) := by unfold cutoffWeight; fun_prop

lemma cutoff_deriv (N : ℕ) (u : ℝ) :
    HasDerivAt (cutoffWeight N) ((N:ℝ)*Real.exp (-(N*u))) u := by
  convert! (hasDerivAt_const u (1:ℝ)).sub (((hasDerivAt_id u).const_mul (N:ℝ)).neg.exp) using 1
  simp only [id_eq,mul_one,Pi.neg_apply]; ring

lemma cutoff_bounds (N : ℕ) {u : ℝ} (up : 0≤u) :
    0≤cutoffWeight N u ∧ cutoffWeight N u≤1 ∧ cutoffWeight N u≤N*u ∧
      (N:ℝ)*u/(1+N*u)≤cutoffWeight N u ∧ u*deriv (cutoffWeight N) u≤cutoffWeight N u := by
  let x := (N:ℝ)*u
  have xp : 0≤x := mul_nonneg (Nat.cast_nonneg _) up
  have e := Real.exp_pos (-x)
  have es : Real.exp (-x)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr xp)
  have b := Real.add_one_le_exp x
  have c := Real.add_one_le_exp (-x)
  have bx : (1+x)*Real.exp (-x)≤1 := by
    rw [Real.exp_neg,← div_eq_mul_inv]
    apply (div_le_one (Real.exp_pos _)).mpr
    linarith
  rw [(cutoff_deriv N u).deriv]
  change 0≤1-Real.exp (-x) ∧ 1-Real.exp (-x)≤1 ∧ 1-Real.exp (-x)≤x ∧
    x/(1+x)≤1-Real.exp (-x) ∧ u*((N:ℝ)*Real.exp (-x))≤1-Real.exp (-x)
  refine ⟨by linarith,by linarith,by linarith,?_,?_⟩
  · apply (div_le_iff₀ (show 0<1+x by linarith)).mpr
    nlinarith only [bx]
  · rw [← mul_assoc,mul_comm u (N:ℝ)]
    change x*Real.exp (-x)≤_
    nlinarith only [bx]

lemma cutoff_lower (N : ℕ) {u : ℝ} (up : 0≤u) :
    (if 1≤(N:ℝ)*u then (1:ℝ)/2 else N*u/2)≤cutoffWeight N u := by
  apply le_trans _ (cutoff_bounds N up).2.2.2.1
  have x := mul_nonneg (Nat.cast_nonneg N) up
  apply (le_div_iff₀ (show 0<1+(N:ℝ)*u by linarith)).mpr
  split_ifs with h
  · linarith
  · nlinarith only [mul_nonneg x (sub_nonneg.mpr (le_of_not_ge h))]

lemma cutoff_sq_le (N : ℕ) (np : 0<N) {a : ℝ} (ap : 0≤a) (ab : a<beta) {u : ℝ} (up : 0≤u) :
    cutoffWeight N u^2≤2*energyWeight N a u := by
  let x := (N:ℝ)*u
  have pos : 0≤x := mul_nonneg (Nat.cast_nonneg _) up
  obtain ⟨lo,hi,small,_,_⟩ := cutoff_bounds N up
  by_cases high : 1≤x
  · have u0 : 0<u := lt_of_le_of_ne up (by intro eq; norm_num [x,← eq] at high)
    have e := weight_lower np ap ab.le u0 high
    nlinarith only [e,mul_nonneg (sub_nonneg.mpr hi) (add_nonneg lo zero_le_one)]
  · have xl := le_of_not_ge high
    have exp : 2*beta≤(2:ℝ) := by norm_num [beta]
    have xr : x^2≤x^(2*beta) := by
      rcases pos.eq_or_lt with z|zp
      · rw [← z,Real.zero_rpow (by norm_num [beta])]; norm_num
      · rw [← Real.rpow_two]
        exact Real.rpow_le_rpow_of_exponent_ge zp xl exp
    have den := Real.rpow_le_one pos xl (show 0≤2*(beta-a) by linarith)
    have dpos := add_pos_of_pos_of_nonneg zero_lt_one (Real.rpow_nonneg pos (2*(beta-a)))
    change _≤2*(_/(1+_))
    rw [max_eq_left up,← mul_div_assoc]
    apply (le_div_iff₀ dpos).mpr
    have sq : cutoffWeight N u^2≤x^2 := pow_le_pow_left₀ lo small _
    exact (mul_le_mul_of_nonneg_left (show 1+x^(2*(beta-a))≤2 by linarith) (sq_nonneg _)).trans
      (by linarith only [sq.trans xr])

private lemma left_end {N : ℕ} (np : 0<N) {u : ℝ} (small : (N:ℝ)*u≤1) :
    primitive N u= -singularSeries N*u := by
  unfold primitive
  rw [sum_eq_zero]
  · ring
  intro n _
  split_ifs with h
  · have n0 : n=0 := by
      have lt := (div_lt_iff₀ (show 0<(N:ℝ) by exact_mod_cast np)).mp h
      rw [mul_comm] at lt
      have : (n:ℝ)<1 := lt.trans_le small
      have hn : n<1 := by exact_mod_cast this
      omega
    simp [n0,mass,mangoldt]
  · rfl

private lemma right_end {N : ℕ} (np : 0<N) {u : ℝ} (small : (N:ℝ)*(1-u)≤1) :
    primitive N u=primitive N 1+singularSeries N*(1-u) := by
  have nr : 0<(N:ℝ) := by exact_mod_cast np
  have s : ∀ n ∈ range N, (if (n:ℝ)/N<u then mass N n else 0)=
      (if (n:ℝ)/N<1 then mass N n else 0) := by
    intro n hn
    have less := mem_range.mp hn
    have n1 := (div_lt_one nr).mpr (Nat.cast_lt.mpr less)
    rw [ite_eq_left n1]
    split_ifs with h
    · rfl
    · have nn := (le_div_iff₀ nr).mp (le_of_not_gt h)
      have sub : N≤n+1 := by exact_mod_cast (show (N:ℝ)≤n+1 by nlinarith only [nn,small])
      have eq : N-n=1 := by omega
      simp [mass,eq,mangoldt]
  unfold primitive
  rw [sum_congr rfl s]
  ring

/-- After subtracting the straight line between the endpoint values, the
cumulative error vanishes at both boundaries with the Sobolev weight. -/
theorem bridge_bound (N : ℕ) (n2 : 2≤N) (D : ℝ)
    (bound : ∀ t∈Set.Icc (0:ℝ) 1, |primitive N t|≤D)
    {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) :
    |bridge N t| ≤ 8*(D+singularSeries N/N)*(cutoffWeight N t*cutoffWeight N (1-t)) := by
  let S := singularSeries N
  let K := D+S/N
  let E := primitive N 1
  let x := (N:ℝ)*t
  let y := (N:ℝ)*(1-t)
  have nr : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have nr2 : 2≤(N:ℝ) := by exact_mod_cast n2
  have rem := sub_nonneg.mpr ht.2
  have en : |E|≤D := bound 1 ⟨zero_le_one,le_rfl⟩
  have dp := (abs_nonneg _).trans en
  have sp : 0≤S := (singularSeries_pos N).le
  have dk : D≤K := le_add_of_nonneg_right (div_nonneg sp nr.le)
  have kp := dp.trans dk
  have low (v : ℝ) (vp : 0≤v) := cutoff_lower N vp
  have vx := low t ht.1
  have vy := low (1-t) rem
  have both : x+y=(N:ℝ) := by dsimp [x,y]; ring
  have total : |S+E|≤(N:ℝ)*K := by
    apply (abs_add_le ..).trans
    rw [abs_of_nonneg sp]
    have dd : D≤(N:ℝ)*D := by nlinarith only [mul_nonneg (show 0≤(N:ℝ)-1 by linarith) dp]
    apply (add_le_add le_rfl (en.trans dd)).trans_eq
    dsimp [K]
    field_simp
    ring
  have mult (v a b : ℝ) (vp : 0≤v) (a0 : 0≤a) (va : v/2≤a) (wb : 1/2≤b) :
      v*K≤8*K*(a*b) := by
    have mu := mul_le_mul va wb (by norm_num : (0:ℝ)≤1/2) a0
    have pass : v≤8*(a*b) := by linarith
    exact (mul_le_mul_of_nonneg_right pass kp).trans_eq (by ring)
  change |bridge N t|≤8*K*(cutoffWeight N t*cutoffWeight N (1-t))
  by_cases xl : 1≤x
  · rw [ite_eq_left xl] at vx
    by_cases yl : 1≤y
    · rw [ite_eq_left yl] at vy
      have o := mul_le_mul vx vy (by norm_num : (0:ℝ)≤1/2) (cutoff_bounds N ht.1).1
      have bound0 : |primitive N t-t*E|≤D+D := (abs_sub (primitive N t) (t*E)).trans (add_le_add (bound t ht) (by
        rw [abs_mul,abs_of_nonneg ht.1]
        exact (mul_le_mul_of_nonneg_left en ht.1).trans (mul_le_of_le_one_left dp ht.2)))
      have base : (2:ℝ)≤8*(cutoffWeight N t*cutoffWeight N (1-t)) := by linarith
      exact bound0.trans ((show D+D≤2*K by linarith).trans
        ((mul_le_mul_of_nonneg_right base kp).trans_eq (by ring)))
    · rw [ite_eq_right yl] at vy
      rw [bridge,right_end (by omega : 0<N) (le_of_not_ge yl)]
      change |E+S*(1-t)-t*E|≤_
      rw [show E+S*(1-t)-t*E=(1-t)*(S+E) by ring,abs_mul,abs_of_nonneg rem]
      calc
        _ ≤ y*K := (mul_le_mul_of_nonneg_left total rem).trans_eq (by dsimp [y]; ring)
        _ ≤ _ := (mult y _ _ (mul_nonneg nr.le rem) (cutoff_bounds N rem).1 vy vx).trans_eq (by ring)
  · rw [ite_eq_right xl] at vx
    have yl : 1≤y := by linarith [le_of_not_ge xl]
    rw [ite_eq_left yl] at vy
    rw [bridge,left_end (by omega : 0<N) (le_of_not_ge xl)]
    change |(-S*t-t*E)|≤_
    rw [show -S*t-t*E= -(t*(S+E)) by ring,abs_neg,abs_mul,abs_of_nonneg ht.1]
    exact ((mul_le_mul_of_nonneg_left total ht.1).trans_eq (by dsimp [x]; ring : t*((N:ℝ)*K)=x*K)).trans
      (mult x _ _ (mul_nonneg nr.le ht.1) (cutoff_bounds N ht.1).1 vx vy)

#print axioms bridge_bound
end GoldbachSpectral435.GoldbachPrimitive
