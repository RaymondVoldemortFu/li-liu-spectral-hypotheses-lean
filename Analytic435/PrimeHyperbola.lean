module
public import PowerRemoval

/-! Bounds for the part of the signed prime-pair form below a multiplicative
threshold. They hold separately at every modulus. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset Complex Filter
open scoped Topology ComplexConjugate
namespace GoldbachSpectral435.PrimeHyperbola
open GoldbachSpectral435.SquareResidues GoldbachSpectral435.PerronApproximation

def weight (N j : ℕ) (r : ZMod N) : ℝ :=
  if N≤2*j ∧ (j:ZMod N)=r then (j:ℝ)⁻¹ else 0

private lemma weight_nonneg (N j : ℕ) (r : ZMod N) : 0≤weight N j r := by
  unfold weight; split <;> positivity

/-- Uniform harmonic mass of a single residue class above half the modulus. -/
theorem progression_harmonic {N X : ℕ} (hp : 0<N) (I : Finset ℕ) (sub : I ⊆ Icc 1 X)
    (r : ZMod N) : ∑ j ∈ I, weight N j r ≤ 3/(N:ℝ)*(1+Real.log (X+1:ℕ)) := by
  classical
  let J := I.filter (fun j : ℕ => N≤2*j ∧ (j:ZMod N)=r)
  let g (j : ℕ) := j/N+1
  have reindex : Set.InjOn g J := by
    intro j hj k hk eq
    obtain ⟨_,_,a⟩ := mem_filter.mp hj
    obtain ⟨_,_,b⟩ := mem_filter.mp hk
    have e := (ZMod.natCast_eq_natCast_iff' j k N).mp (a.trans b.symm)
    have q : j/N=k/N := Nat.add_right_cancel eq
    have d := Nat.mod_add_div j N
    rw [e,q,Nat.mod_add_div] at d
    exact d.symm
  have img : J.image g ⊆ Icc 1 (X+1) := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
    obtain ⟨_,u⟩ := mem_Icc.mp (sub (mem_filter.mp hj).1)
    exact mem_Icc.mpr ⟨Nat.le_add_left 1 _,Nat.add_le_add_right ((Nat.div_le_self ..).trans u) 1⟩
  have cap (j : ℕ) (hj : j∈J) : (j:ℝ)⁻¹ ≤ 3/(N:ℝ)*(g j:ℝ)⁻¹ := by
    obtain ⟨hI,h,_⟩ := mem_filter.mp hj
    have jp : 0<(j:ℝ) := by exact_mod_cast (mem_Icc.mp (sub hI)).1
    have np : 0<(N:ℝ) := by exact_mod_cast hp
    have gp : 0<(g j:ℝ) := by dsimp [g]; positivity
    have prod : N*g j ≤ 3*j := by
      dsimp [g]; rw [Nat.mul_add,Nat.mul_one]
      have := Nat.div_mul_le_self j N
      rw [Nat.mul_comm] at this
      omega
    have pr : (N:ℝ)*(g j:ℝ) ≤ 3*(j:ℝ) := by exact_mod_cast prod
    field_simp
    linarith only [pr]
  simp only [weight,← sum_filter]
  change ∑ j ∈ J, (j:ℝ)⁻¹ ≤ _
  calc
    _ ≤ ∑ j ∈ J, (3/(N:ℝ))*(g j:ℝ)⁻¹ := sum_le_sum cap
    _ = (3/(N:ℝ))*∑ k ∈ J.image g, (k:ℝ)⁻¹ := by rw [sum_image reindex,mul_sum]
    _ ≤ (3/(N:ℝ))*∑ k ∈ Ico 1 ((X+1)+1), (k:ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
      intro n hm
      obtain ⟨a,b⟩ := mem_Icc.mp (img hm)
      exact mem_Ico.mpr ⟨a,by omega⟩
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [one_div] using harmonic_interval (Y:=1) (R:=X+1) (by decide)) (by positivity)

private def row (N n j : ℕ) : ℝ :=
  (n:ℝ)⁻¹*(2*weight N j (n:ZMod N)+weight N j (-(n:ZMod N)))

private lemma row_nonneg (N n j : ℕ) : 0≤row N n j :=
  mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by norm_num) (weight_nonneg ..)) (weight_nonneg ..))

private lemma same_sign (N n j : ℕ) : offDiagonalSign N n j = offDiagonalSign N j n := by
  have neg : (n:ZMod N)=-(j:ZMod N) ↔ (j:ZMod N)=-(n:ZMod N) := by
    constructor <;> intro h <;> simpa using (congrArg Neg.neg h).symm
  by_cases e : n=j
  · subst j; rfl
  · simp only [offDiagonalSign,residueSign,Nat.mul_comm n j,neg,e,Ne.symm e,false_and,ite_false,
      show ((n:ZMod N)=j) ↔ (j:ZMod N)=n from eq_comm]

private lemma short_sign {N n j : ℕ} (np : 0<n) (jp : 0<j) (nj : n≤j) (small : 2*j<N) :
    offDiagonalSign N n j=0 := by
  obtain ⟨a,b⟩ := residue_diagonals (by omega : 0<N) np (by omega : n<N) jp (by omega : j<N)
  unfold offDiagonalSign residueSign
  simp only [a,b]
  have no : n+j≠N := by omega
  by_cases eq : n=j
  · subst j; simp [no,Nat.coprime_mul_iff_left]
  · simp [eq,no]

private lemma off_majorant {N n j : ℕ} (np : 0<n) (jp : 0<j) (nj : n≤j) :
    (n:ℝ)⁻¹*(j:ℝ)⁻¹*‖offDiagonalSign N n j‖ ≤ row N n j := by
  by_cases h : N≤2*j
  · have neg : (n:ZMod N)=-(j:ZMod N) ↔ (j:ZMod N)=-(n:ZMod N) := by
      constructor <;> intro v <;> simpa using (congrArg Neg.neg v).symm
    unfold offDiagonalSign residueSign row weight
    simp only [h,true_and,neg,show ((n:ZMod N)=j) ↔ (j:ZMod N)=n from eq_comm]
    by_cases e : n=j
    · subst j
      simp only [true_and,ite_true,Nat.coprime_mul_iff_left,and_self]
      split_ifs <;> norm_num <;> nlinarith only [sq_nonneg ((n:ℝ)⁻¹)]
    · simp only [e,false_and,ite_false,sub_zero]
      split_ifs <;> norm_num <;> nlinarith only [mul_nonneg (by positivity : 0≤(n:ℝ)⁻¹) (by positivity : 0≤(j:ℝ)⁻¹)]
  · rw [short_sign np jp nj (lt_of_not_ge h),norm_zero,mul_zero]
    exact row_nonneg ..

private lemma sum_rows {N X : ℕ} (hp : 0<N) (I : Finset ℕ) (sub : I⊆Icc 1 X) :
    ∑ n ∈ I, ∑ j ∈ I, row N n j ≤ 9/(N:ℝ)*(1+Real.log (X+1:ℕ))^2 := by
  let H := 1+Real.log (X+1:ℕ)
  let cap : ℝ := 3/N*H
  have h0 : 0≤H := by
    have := Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 X) : (1:ℝ)≤(X+1:ℕ))
    dsimp [H]; linarith
  have cap0 : 0≤cap := by dsimp [cap]; positivity
  have total : ∑ n ∈ I, (n:ℝ)⁻¹ ≤ H := by
    apply le_trans _ (by simpa only [one_div] using harmonic_interval (Y:=1) (R:=X+1) (by decide))
    apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
    intro n hn
    have ⟨lo,hi⟩ := mem_Icc.mp (sub hn)
    exact mem_Ico.mpr ⟨lo,by omega⟩
  calc
    _ ≤ ∑ n ∈ I, (n:ℝ)⁻¹*(2*cap+cap) := by
      apply sum_le_sum
      intro n _
      simp only [row,← mul_sum,sum_add_distrib]
      gcongr <;> exact progression_harmonic hp I sub _
    _ = (∑ n ∈ I, (n:ℝ)⁻¹)*(2*cap+cap) := (sum_mul ..).symm
    _ ≤ H*(2*cap+cap) := mul_le_mul_of_nonneg_right total (by positivity)
    _ = _ := by dsimp [cap,H]; ring

private lemma product_bound {n j : ℕ} (hn : 0<n) (hj : 0<j) (Q B : ℝ)
    (hB : 0≤B) {c d : ℂ} (hc : ‖c‖ ≤ B*(n:ℝ)^(-(1/2:ℝ)))
    (hd : ‖d‖ ≤ B*(j:ℝ)^(-(1/2:ℝ))) (cut : Real.sqrt ((n:ℝ)*j) ≤ Q) :
    ‖c‖*‖d‖ ≤ B^2*Q*((n:ℝ)⁻¹*(j:ℝ)⁻¹) := by
  have id (v : ℝ) (vp : 0<v) : v^(-(1/2:ℝ))=Real.sqrt v*v⁻¹ := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_neg_one,← Real.rpow_add vp]; norm_num
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have jp : 0<(j:ℝ) := by exact_mod_cast hj
  rw [id _ np] at hc
  rw [id _ jp] at hd
  apply (mul_le_mul hc hd (norm_nonneg _) (by positivity)).trans
  calc
    _ = B^2*Real.sqrt ((n:ℝ)*j)*((n:ℝ)⁻¹*(j:ℝ)⁻¹) := by rw [Real.sqrt_mul np.le]; ring
    _ ≤ _ := by gcongr

def pairTerm (N n j : ℕ) (c : ℕ→ℂ) := c n*conj (c j)*offDiagonalSign N n j

/-- Absolute contribution below the hyperbola n j ≤ Q². No hypothesis on
the distribution of primes or the factorization of the modulus is needed. -/
theorem hyperbola_bound {N X : ℕ} (hp : 0<N) (I : Finset ℕ) (sub : I⊆Icc 1 X)
    (c : ℕ→ℂ) {Q B : ℝ} (qp : 0≤Q) (hB : 0≤B)
    (cap : ∀ n ∈ I, ‖c n‖≤B*(n:ℝ)^(-(1/2:ℝ))) :
    (∑ n ∈ I, ∑ j ∈ I, if Real.sqrt ((n:ℝ)*j) ≤ Q then ‖pairTerm N n j c‖ else 0) ≤
      18*B^2*(Q/N)*(1+Real.log (X+1:ℕ))^2 := by
  have pos {n} (h : n∈I) : 0<n := (mem_Icc.mp (sub h)).1
  have major {n j} (a : n∈I) (b : j∈I) (nj : n≤j) (cut : Real.sqrt ((n:ℝ)*j)≤Q) :
      ‖pairTerm N n j c‖ ≤ B^2*Q*row N n j := by
    simp only [pairTerm,norm_mul,RCLike.norm_conj]
    apply (mul_le_mul_of_nonneg_right (product_bound (pos a) (pos b) Q B hB (cap _ a) (cap _ b) cut)
      (norm_nonneg _)).trans
    rw [mul_assoc (B^2*Q)]
    exact mul_le_mul_of_nonneg_left (off_majorant (pos a) (pos b) nj) (by positivity)
  have symm (n j : ℕ) : ‖pairTerm N n j c‖=‖pairTerm N j n c‖ := by
    simp only [pairTerm,norm_mul,RCLike.norm_conj,same_sign N n j,mul_comm ‖c n‖ ‖c j‖]
  have each (n : ℕ) (hn : n∈I) (j : ℕ) (hj : j∈I) :
      (if Real.sqrt ((n:ℝ)*j)≤Q then ‖pairTerm N n j c‖ else 0) ≤
        B^2*Q*(row N n j+row N j n) := by
    split_ifs with cut
    · rcases le_total n j with bound | bound
      · exact (major hn hj bound cut).trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (row_nonneg ..)) (by positivity))
      · rw [symm]; rw [mul_comm] at cut
        exact (major hj hn bound cut).trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (row_nonneg ..)) (by positivity))
    · exact mul_nonneg (by positivity) (add_nonneg (row_nonneg ..) (row_nonneg ..))
  apply (sum_le_sum (fun n hn => sum_le_sum (each n hn))).trans
  simp only [← mul_sum,sum_add_distrib]
  rw [sum_comm (f:=fun n j => row N j n)]
  apply (mul_le_mul_of_nonneg_left (add_le_add (sum_rows hp I sub) (sum_rows hp I sub)) (by positivity : 0≤B^2*Q)).trans_eq
  ring

private lemma sum_skip_zero {M : Type*} [AddCommMonoid M] (I : Finset ℕ) (g : ℕ→M) (hz : g 0=0) :
    ∑ n ∈ I, g n = ∑ n ∈ I.erase 0, g n := by
  by_cases mem : 0∈I
  · simpa only [hz,add_zero] using (sum_erase_add I g mem).symm
  · rw [erase_eq_of_notMem mem]

private lemma original_small {N : ℕ} (big : Real.exp 10<(N:ℝ)) (I : Finset ℕ) (sub : I⊆allIndices N)
    (f : HardySpace (alpha N) beta) (hf : ‖f‖≤1) :
    let c := fun n => testCoefficient N (exponent N) n f
    let Q : ℝ := N/(Real.log N)^24
    (∑ n ∈ I, ∑ j ∈ I, if Real.sqrt ((n:ℝ)*j)≤Q then ‖pairTerm N n j c‖ else 0) ≤
      (18*612^2*206^2:ℝ)/(Real.log N)^16 := by
  intro c Q
  let L := Real.log N
  let R := baseEnd N
  let B := 6*Real.log R
  obtain ⟨rp,xp,rl⟩ := parameters N big
  have np : 0<N := by have := (large_parameters big).1; omega
  have nr : 0<(N:ℝ) := by exact_mod_cast np
  have l1 : 1≤L := by dsimp [L]; linarith [(Real.lt_log_iff_exp_lt nr).mpr big]
  have lp : 0<L := zero_lt_one.trans_le l1
  have l2 : 1≤L^2 := one_le_pow₀ l1
  have rs : 1≤R^2 := one_le_pow₀ rp
  have logr : 0≤Real.log R := Real.log_nonneg (by exact_mod_cast rp)
  have B0 : 0≤B := by dsimp [B]; positivity
  have bound (n : ℕ) (hn : n∈I) : n≤R^2 := by
    have cut : cutoff N (exponent N) = ((R^2:ℕ):ℝ) := by simp [R,cutoff,baseEnd]
    simpa only [allIndices,cut,Nat.floor_natCast,mem_range,Nat.lt_succ_iff] using sub hn
  have Jsub : I.erase 0 ⊆ Icc 1 (R^2) := by
    intro n hn
    exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero (mem_erase.mp hn).1,bound n (mem_erase.mp hn).2⟩
  let G (n j : ℕ) : ℝ := if Real.sqrt ((n:ℝ)*j)≤Q then ‖pairTerm N n j c‖ else 0
  have cz : c 0=0 := by simp [c,testCoefficient,mangoldt]
  have ij (n : ℕ) : G n 0=0 := by simp [G,pairTerm,cz]
  have ji (j : ℕ) : G 0 j=0 := by simp [G,pairTerm,cz]
  change (∑ n ∈ I, ∑ j ∈ I, G n j) ≤ _
  rw [sum_skip_zero I _ (by simp [ji] : (∑ j ∈ I, G 0 j)=0)]
  simp_rw [sum_skip_zero I _ (ij _)]
  have h := hyperbola_bound np (I.erase 0) Jsub c (Q:=Q) (by dsimp [Q]; positivity) B0
    (fun n hn => coefficient_decay N _ n R big xp (mem_Icc.mp (Jsub hn)).1 (mem_Icc.mp (Jsub hn)).2 f hf)
  apply h.trans
  have lr : Real.log R ≤ 102*L^2 := rl
  have b : B≤612*L^2 := by dsimp [B]; linarith only [lr]
  have log2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have rhs : 1+Real.log (R^2+1:ℕ) ≤ 206*L^2 := by
    have arg : ((R^2+1:ℕ):ℝ) ≤ 2*(R:ℝ)^2 := by exact_mod_cast (by omega : R^2+1≤2*R^2)
    have rr : 0<(R:ℝ) := by exact_mod_cast (show 0<R from rp)
    have e := Real.log_le_log (by positivity) arg
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at e
    norm_num only [Nat.cast_ofNat] at e
    linarith
  have lower : 0≤1+Real.log (R^2+1:ℕ) := by
    have := Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 (R^2)) : (1:ℝ)≤(R^2+1:ℕ))
    linarith
  calc
    _ ≤ 18*(612*L^2)^2*(Q/N)*(206*L^2)^2 := by gcongr
    _ = _ := by dsimp [Q,L]; field_simp

private lemma signed_sum (N : ℕ) [NeZero N] (he : Even N) (four : 4≤N) (I : Finset ℕ) (c : ℕ→ℂ) :
    (finiteForm N I c:ℂ) = ∑ n ∈ I, ∑ j ∈ I, pairTerm N n j c := by
  classical
  have gram : (meanEnergy N (amplitude I c):ℂ) =
    ∑ n ∈ I, ∑ j ∈ I, c n*conj (c j)*residueSign N n j := odd_character_quadratic_complex N he four I c
  have diag (n : ℕ) (hn : n∈I) :
      (∑ j ∈ I, c n*conj (c j)*(if n=j ∧ n.Coprime N then 1 else 0)) =
      ((if n.Coprime N then ‖c n‖^2 else 0:ℝ):ℂ) := by
    by_cases cp : n.Coprime N
    · simp only [mul_ite,mul_one,mul_zero]
      rw [sum_eq_single n]
      · simp only [true_and,ite_eq_left cp,Complex.mul_conj,Complex.sq_norm]
      · intro j _ h
        simp [Ne.symm h]
      · simp [hn]
    · simp [cp]
  rw [finiteForm,Complex.ofReal_sub,gram,diagonalEnergy,Complex.ofReal_sum,← sum_congr rfl diag,← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  rw [← sum_sub_distrib]
  simp only [pairTerm,offDiagonalSign,mul_sub]

/-- The surviving signed arithmetic pairs use the paper's test coefficients.
Both the prime-power and multiplicative cutoffs depend only on the modulus. -/
def remaining (N : ℕ) (f : HardySpace (alpha N) beta) : ℂ :=
  let I := (allIndices N).filter (fun n => n.Prime ∨ n<(squareFloor N)^2)
  let c := fun n => testCoefficient N (exponent N) n f
  ∑ n ∈ I, ∑ j ∈ I, if N/(Real.log N)^24 < Real.sqrt ((n:ℝ)*j) then pairTerm N n j c else 0

theorem remaining_error :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ (_ : NeZero N), Even N →
      Real.exp 10<(N:ℝ) → GRH N → ∀ (ha : alpha N<beta) (f : HardySpace (alpha N) beta),
      ‖f‖≤1 → ‖inner ℂ f (residualOperator ha N f) -
        (remaining N f-inner ℂ f (modelOperator ha N f))‖ ≤ C/(Real.log N)^16 := by
  obtain ⟨B,bp,unif⟩ := prime_power_trim_error
  let D : ℝ := 18*612^2*206^2
  refine ⟨B+D,add_pos bp (by norm_num [D]),?_⟩
  filter_upwards [unif] with N hN
  intro inst he big g ha f hf
  let I := (allIndices N).filter (fun n => n.Prime ∨ n<(squareFloor N)^2)
  let c := fun n => testCoefficient N (exponent N) n f
  let Q : ℝ := N/(Real.log N)^24
  let discardedSum := ∑ n ∈ I, ∑ j ∈ I,
    if Real.sqrt ((n:ℝ)*j)≤Q then pairTerm N n j c else 0
  have sum_id : (finiteForm N I c:ℂ) = discardedSum+remaining N f := by
    rw [signed_sum N he (large_parameters big).1,remaining]
    change _ = (∑ n ∈ I, ∑ j ∈ I, _)+(∑ n ∈ I, ∑ j ∈ I, _)
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    change _ = (if Real.sqrt ((n:ℝ)*j)≤Q then _ else 0)+(if Q<Real.sqrt ((n:ℝ)*j) then _ else 0)
    by_cases h : Real.sqrt ((n:ℝ)*j)≤Q
    · rw [ite_eq_left h,ite_eq_right (not_lt.mpr h),add_zero]
    · rw [ite_eq_right h,ite_eq_left (lt_of_not_ge h),zero_add]
  have d : ‖discardedSum‖ ≤ D/(Real.log N)^16 := by
    apply (norm_sum_le _ _).trans
    apply le_trans _ (original_small big I (filter_subset ..) f hf)
    apply sum_le_sum
    intro n _
    apply (norm_sum_le _ _).trans_eq
    apply sum_congr rfl
    intro j _
    split_ifs <;> first | rfl | exact norm_zero
  have e := hN inst he big g ha f hf
  change ‖inner ℂ f (residualOperator ha N f)-((finiteForm N I c:ℂ)-inner ℂ f (modelOperator ha N f))‖ ≤ _ at e
  rw [sum_id] at e
  have eq (x y z w : ℂ) : x-(y-z)=(x-((w+y)-z))+w := by ring
  rw [eq _ _ _ discardedSum,add_div]
  exact (norm_add_le _ _).trans (add_le_add e d)

#print axioms remaining_error
#print axioms hyperbola_bound
end GoldbachSpectral435.PrimeHyperbola
