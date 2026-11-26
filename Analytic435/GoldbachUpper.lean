module
public import SieveInterval

/-! A uniform upper sieve on every translated Goldbach interval. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset MathlibNt.SieveTheory.LiuWeight
namespace GoldbachSpectral435.GoldbachSieve

private def system (N z A Y : ℕ) (ev : Even N) : BoundingSieve where
  support := (Ico A (A+Y)).image (fun n => n*(N-n))
  prodPrimes := primorial z
  prodPrimes_squarefree := squarefree_primorial z
  weights := fun j => (((Ico A (A+Y)).filter (fun n => n*(N-n)=j)).card:ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := Y
  nu := density N
  nu_mult := density_mult N
  nu_pos_of_prime := fun p hp _ => (density_prime N p hp).symm ▸ (density_range N p ev hp).1
  nu_lt_one_of_prime := fun p hp _ => (density_prime N p hp).symm ▸ (density_range N p ev hp).2

private lemma hit_root (N d n : ℕ) (hn : n≤N) :
    hit (n*(N-n)) d=(if (n:ZMod d)*(n-N)=0 then 1 else 0) := by
  have h : d∣n*(N-n) ↔ (n:ZMod d)*(n-N)=0 := by
    rw [← ZMod.natCast_eq_zero_iff,Nat.cast_mul,Nat.cast_sub hn]
    have neg : (n:ZMod d)*(N-n)= -((n:ZMod d)*(n-N)) := by ring
    rw [neg,neg_eq_zero]
  by_cases m : d∣n*(N-n)
  · simp [hit,m,h.mp m]
  · simp [hit,m,mt h.mpr m]

theorem interval_residue_error (N d A Y : ℕ) [NeZero d] (sq : Squarefree d) (inc : A+Y≤N+1) :
    |(∑ n∈Ico A (A+Y), hit (n*(N-n)) d)-(Y:ℝ)*density N d|≤2*d := by
  have eq := sum_congr rfl (fun n (hn : n∈Ico A (A+Y)) =>
    hit_root N d n (by have := (mem_Ico.mp hn).2; omega))
  rw [eq,sum_Ico_eq_sub _ (by omega : A≤A+Y),← root_sum_real,← root_sum_real]
  have h := abs_sub ((rootCount N d (A+Y):ℝ)-(A+Y:ℕ)*density N d)
    ((rootCount N d A:ℝ)-A*density N d)
  have alg : (rootCount N d (A+Y):ℝ)-rootCount N d A-Y*density N d=
      ((rootCount N d (A+Y):ℝ)-(A+Y:ℕ)*density N d)-((rootCount N d A:ℝ)-A*density N d) := by
    push_cast; ring
  rw [alg]
  exact h.trans ((add_le_add (root_discrepancy N d (A+Y) sq) (root_discrepancy N d A sq)).trans_eq (by ring))

def sifted (N z A Y : ℕ) : ℝ :=
  ∑ n∈Ico A (A+Y), if (primorial z).Coprime (n*(N-n)) then (1:ℝ) else 0

/-- A uniform finite upper estimate with a quadratic Euler product.
Both residue classes, including their coincidence when p divides N,
enter the main term. -/
theorem sifted_le (N z R A Y : ℕ) (ev : Even N) (zz : 2≤z) (hr : z^8≤R) (inc : A+Y≤N+1) :
    sifted N z A Y≤2*Y*(∏ p∈smallPrimes z, (1-localDensity N p))+2*(R:ℝ)^4 := by
  let S := system N z A Y ev
  have rp : 1≤R := (Nat.one_le_pow _ _ (by omega : 0<z)).trans hr
  have er (d : ℕ) (dv : d∣S.prodPrimes) := by
    let _ : NeZero d := ⟨(Nat.pos_of_dvd_of_pos dv (primorial_pos z)).ne'⟩
    exact interval_residue_error N d A Y (S.prodPrimes_squarefree.squarefree_of_dvd dv) inc
  have b := interval_upper S R rp (Ico A (A+Y)) (fun n => n*(N-n)) (Y:ℝ) 2 (by norm_num) er
  let P := smallPrimes z
  have pr (p : ℕ) (hp : p∈P) : p.Prime := (mem_filter.mp hp).2
  have sm (p : ℕ) (hp : p∈P) : p≤z := by have := mem_range.mp (mem_filter.mp hp).1; omega
  have sel := selberg_lower N z R ev (by omega) hr P pr sm S
    (fun p hp => (pr p hp).dvd_primorial_iff.mpr (sm p hp)) (fun p hp => density_prime N p (pr p hp))
  let V := ∏ p∈P, (1-localDensity N p)
  have vp : 0<V := prod_pos (fun p hp => sub_pos.mpr (density_range N p ev (pr p hp)).2)
  have eq : (∏ p∈P, (1+odds N p))*V=1 := by
    dsimp only [V]
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro p hp
    have nz := (sub_pos.mpr (density_range N p ev (pr p hp)).2).ne'
    unfold odds
    field_simp
    ring
  have dp := truncatedSelbergDenominator_pos S rp
  have ld := mul_le_mul_of_nonneg_right sel vp.le
  have pay : (Y:ℝ)/truncatedSelbergDenominator S R≤2*Y*V := by
    apply (div_le_iff₀ dp).mpr
    have b0 : 1≤2*V*truncatedSelbergDenominator S R := by nlinarith only [ld,eq]
    nlinarith only [mul_le_mul_of_nonneg_left b0 (Nat.cast_nonneg (α:=ℝ) Y)]
  exact b.trans (add_le_add pay le_rfl)

def primePairs (N A Y : ℕ) : ℝ :=
  ∑ n∈Ico A (A+Y), if n.Prime ∧ (N-n).Prime then (1:ℝ) else 0

private lemma small_ends (N z A Y : ℕ) (inc : A+Y≤N+1) :
    primePairs N A Y≤sifted N z A Y+2*((z:ℝ)+1) := by
  classical
  let I := Ico A (A+Y)
  let F := fun n : ℕ => if (primorial z).Coprime (n*(N-n)) then (1:ℝ) else 0
  have point (n : ℕ) : (if n.Prime ∧ (N-n).Prime then (1:ℝ) else 0)≤
      F n+((if n≤z then 1 else 0)+(if N-n≤z then 1 else 0)) := by
    by_cases prime : n.Prime ∧ (N-n).Prime
    · by_cases l : n≤z
      · simp only [prime,l,ite_true,F]; split_ifs <;> norm_num
      by_cases r : N-n≤z
      · simp only [prime,l,r,ite_true,ite_false,F]; split_ifs <;> norm_num
      have u := prime.1.coprime_iff_not_dvd.mpr (mt prime.1.dvd_primorial_iff.mp l)
      have v := prime.2.coprime_iff_not_dvd.mpr (mt prime.2.dvd_primorial_iff.mp r)
      have ok : (primorial z).Coprime (n*(N-n)) := Nat.coprime_mul_iff_right.mpr ⟨u.symm,v.symm⟩
      rw [ite_eq_left prime,ite_eq_right l,ite_eq_right r,add_zero,add_zero]
      change (1:ℝ) ≤ (if (primorial z).Coprime (n*(N-n)) then 1 else 0)
      rw [ite_eq_left ok]
    · simp only [prime,ite_false,F]; split_ifs <;> norm_num
  have left : ((I.filter (fun n => n≤z)).card:ℝ)≤z+1 := by
    have h : I.filter (fun n => n≤z)⊆range (z+1) := fun n hn => mem_range.mpr (by have := (mem_filter.mp hn).2; omega)
    exact_mod_cast (card_le_card h).trans_eq (card_range _)
  have right : ((I.filter (fun n => N-n≤z)).card:ℝ)≤z+1 := by
    have h : I.filter (fun n => N-n≤z)⊆Icc (N-z) N := by
      intro n hn
      obtain ⟨a,b⟩ := mem_filter.mp hn
      have c := (mem_Ico.mp a).2
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    have h' := card_le_card h
    rw [Nat.card_Icc] at h'
    exact_mod_cast (show (I.filter (fun n => N-n≤z)).card≤z+1 by omega)
  have b := sum_le_sum (s:=I) (fun n _ => point n)
  simp only [sum_add_distrib,sum_boole] at b
  change (∑ n∈I, if n.Prime ∧ (N-n).Prime then (1:ℝ) else 0)≤(∑ n∈I,F n)+2*((z:ℝ)+1)
  rw [sum_boole]
  apply b.trans
  linarith

/-- The number of ordered Goldbach pairs in any interval of Y possible
first summands is at most C Y S(N)/log(z)^2 plus explicit finite errors. -/
theorem prime_pairs_upper :
    ∃ C : ℝ, 0<C ∧ ∀ N z R A Y : ℕ, 0<N → Even N → 2≤z → z^8≤R → A+Y≤N+1 →
      primePairs N A Y≤C*Y*singularSeries N/(Real.log z)^2+2*(R:ℝ)^4+2*((z:ℝ)+1) := by
  obtain ⟨C,cp,prod⟩ := uniform_product
  refine ⟨2*C,by positivity,?_⟩
  intro N z R A Y np ev zz hr inc
  apply (small_ends N z A Y inc).trans
  apply add_le_add _ le_rfl
  apply (sifted_le N z R A Y ev zz hr inc).trans
  apply add_le_add _ le_rfl
  exact (mul_le_mul_of_nonneg_left (prod N z np ev zz) (show 0≤2*(Y:ℝ) by positivity)).trans_eq (by ring)

#print axioms prime_pairs_upper
end GoldbachSpectral435.GoldbachSieve
