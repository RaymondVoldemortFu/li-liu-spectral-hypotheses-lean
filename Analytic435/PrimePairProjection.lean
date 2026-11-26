module
public import PrimeClassLimit

/-! The congruence projection of two genuine prime weights, for both the
sum and difference lines. The projected count weights each surviving
pair of invertible classes by the two actual prime sums in those classes. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Finset
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open PhysicalTests
open MathlibNt.SieveTheory.MertensTheorem (primeProduct)

def partner {q : ℕ} (sumLine : Bool) (H : ℕ) (t : ZMod q) :=
  if sumLine then H-t else t-H

lemma units_of_allowed {q H : ℕ} [NeZero q] {t : ZMod q} (h : t∈allowed H q)
    (sign : Bool) : IsUnit t ∧ IsUnit (partner sign H t) := by
  obtain ⟨a,b⟩ := (Commute.all _ _).isUnit_mul_iff.mp ((mem_allowed ..).mp h)
  cases sign
  · exact ⟨a,b⟩
  · exact ⟨a,by simpa only [partner,ite_true,neg_sub] using b.neg⟩

def projectedPairs (H z M L : ℕ) (sign : Bool) (f g : ℝ→ℝ) : ℝ :=
  ∑ t∈allowed H (primorial z),
    classMass (primorial z) M t f*classMass (primorial z) L (partner sign H t) g

/-- The congruence projection is an actual double von Mangoldt sum. -/
theorem projected_pairs_sum (H z M L : ℕ) (sign : Bool) (f g : ℝ→ℝ) :
    projectedPairs H z M L sign f g=
    ∑ n∈range M, ∑ j∈range L, if (n:ZMod (primorial z))∈allowed H (primorial z) ∧
      (j:ZMod (primorial z))=partner sign H n then weightedMangoldt M n f*weightedMangoldt L j g else 0 := by
  classical
  unfold projectedPairs classMass
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  let Q := primorial z
  have eq (t : ZMod Q) : (if (n:ZMod Q)=t then weightedMangoldt M n f else 0)*
      (∑ j∈range L, if (j:ZMod Q)=partner sign H t then weightedMangoldt L j g else 0)=
      if (n:ZMod Q)=t then ∑ j∈range L, if (j:ZMod Q)=partner sign H n then
        weightedMangoldt M n f*weightedMangoldt L j g else 0 else 0 := by
    by_cases h : (n:ZMod Q)=t
    · subst t
      simp only [ite_true,mul_sum,mul_ite,mul_zero]
    · simp [h]
  simp_rw [eq]
  rw [sum_ite_eq]
  split_ifs with h <;> simp [h]

private lemma rescaled (H z M L : ℕ) (hp : 0<H) (ev : Even H) (zz : 2≤z)
    (f g : ℝ→ℝ) (sign : Bool) :
    let Q := primorial z
    let E := allowed H Q
    (Q:ℝ)*projectedPairs H z M L sign f g/((M:ℝ)*L*singularSeries H)=
    (truncatedSeries H z/singularSeries H)*
      ((∑ t∈E,classAverage Q M t f*classAverage Q L (partner sign H t) g)/E.card) := by
  intro Q E
  let W := primeProduct z
  have qp : 0<(Q:ℝ) := Nat.cast_pos.mpr (primorial_pos _)
  have fp : 0<(Q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (primorial_pos _))
  have phi : (Q.totient:ℝ)=(Q:ℝ)*W := primorial_totient z
  have wp : 0<W := pos_of_mul_pos_right (phi ▸ fp) qp.le
  have vp : 0<survivingDensity H z := prod_pos (fun p h => sub_pos.mpr (density_range H p ev (mem_filter.mp h).2).2)
  have v : survivingDensity H z=W^2*truncatedSeries H z := density_identity H z hp ev zz
  have tp : 0<truncatedSeries H z := pos_of_mul_pos_right (v ▸ vp) (sq_nonneg W)
  have card : (E.card:ℝ)=(Q:ℝ)*(W^2*truncatedSeries H z) :=
    (allowed_count H z).trans (congrArg ((Q:ℝ)*·) v)
  have eq : (∑ t∈E,classAverage Q M t f*classAverage Q L (partner sign H t) g)=
      ((Q.totient:ℝ)^2/((M:ℝ)*L))*projectedPairs H z M L sign f g := by
    rw [projectedPairs,mul_sum]
    apply sum_congr rfl
    intro t _
    unfold classAverage
    ring
  rw [eq,phi,card]
  field_simp

private lemma average_error {α : Type*} (E : Finset α) (ne : E.Nonempty) (A B : α→ℝ)
    (x y δ : ℝ) (δp : 0≤δ) (δ1 : δ≤1)
    (a : ∀ t∈E, |A t-x|≤δ) (b : ∀ t∈E, |B t-y|≤δ) :
    |(∑ t∈E,A t*B t)/E.card-x*y|≤δ*(|x|+|y|+1) := by
  have dp : 0<(E.card:ℝ) := by exact_mod_cast card_pos.mpr ne
  have per (t : α) (ht : t∈E) : |A t*B t-x*y|≤δ*(|x|+|y|+1) := by
    have uv := abs_add_le (B t-y) y
    rw [sub_add_cancel] at uv
    have cap : |B t|≤|y|+1 := by linarith only [uv,b t ht,δ1]
    rw [show A t*B t-x*y=(A t-x)*B t+x*(B t-y) by ring]
    have sum := abs_add_le ((A t-x)*B t) (x*(B t-y))
    simp only [abs_mul] at sum
    linarith only [sum,mul_le_mul (a t ht) cap (abs_nonneg _) δp,
      mul_le_mul_of_nonneg_left (b t ht) (abs_nonneg x)]
  have e : (∑ t∈E, A t*B t)/E.card-x*y=(∑ t∈E,(A t*B t-x*y))/E.card := by
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul]
    field_simp
  rw [e,abs_div,abs_of_pos dp,div_le_iff₀ dp]
  apply (abs_sum_le_sum_abs ..).trans ((sum_le_sum per).trans_eq _)
  rw [sum_const,nsmul_eq_mul,mul_comm]

theorem prime_pair_projection_limit (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g)
    (ε : ℝ) (ep : 0<ε) : ∀ᶠ N : ℕ in atTop, ∀ M L H : ℕ, N≤M → N≤L → 0<H → Even H →
      H≤2*scale N*N → GRH (primorial (localCutoff N)) → ∀ sign : Bool,
      |(primorial (localCutoff N):ℝ)*projectedPairs H (localCutoff N) M L sign f g/
        ((M:ℝ)*L*singularSeries H)-(∫ u in (0:ℝ)..1,f u)*(∫ u in (0:ℝ)..1,g u)|≤ε := by
  let x := ∫ u in (0:ℝ)..1,f u
  let y := ∫ u in (0:ℝ)..1,g u
  let D := 2*(|x|+|y|+1)+|x*y|+1
  let δ := min 1 (ε/D)
  have dp : 0<D := by dsimp [D]; positivity
  have pp : 0<δ := lt_min zero_lt_one (div_pos ep dp)
  have δ1 : δ≤1 := min_le_left ..
  have pay : δ*D≤ε := (le_div_iff₀ dp).mp (min_le_right ..)
  filter_upwards [class_average_limit f hf δ pp,class_average_limit g hg δ pp,
    cutoff_grows.eventually_ge_atTop 2,all_horizon_factors δ pp] with N left right zz cap
  intro M L H nm nl hp ev hh grh sign
  let z := localCutoff N
  let Q := primorial z
  let E := allowed H Q
  let R := truncatedSeries H z/singularSeries H
  let A := fun t => classAverage Q M t f
  let B := fun t => classAverage Q L (partner sign H t) g
  let V := (∑ t∈E,A t*B t)/E.card
  have qp : 0<(Q:ℝ) := Nat.cast_pos.mpr (primorial_pos _)
  have vp : 0<survivingDensity H z := prod_pos (fun p h => sub_pos.mpr (density_range H p ev (mem_filter.mp h).2).2)
  have ec : 0<(E.card:ℝ) := (allowed_count H z).symm ▸ mul_pos qp vp
  have ne : E.Nonempty := card_pos.mp (Nat.cast_pos.mp ec)
  have avg : |V-x*y|≤δ*(|x|+|y|+1) := average_error E ne A B x y δ pp.le δ1
    (fun t h => left M nm grh t (units_of_allowed h sign).1)
    (fun t h => right L nl grh _ (units_of_allowed h sign).2)
  have rr : |R-1|≤δ := cap.2 H hp hh
  have rb : |R|≤2 := by
    have s := abs_add_le (R-1) 1
    rw [sub_add_cancel,abs_one] at s
    linarith
  rw [rescaled H z M L hp ev zz f g sign]
  change |R*V-x*y|≤ε
  rw [show R*V-x*y=R*(V-x*y)+(R-1)*(x*y) by ring]
  have s := abs_add_le (R*(V-x*y)) ((R-1)*(x*y))
  simp only [abs_mul R,abs_mul (R-1)] at s
  have p1 := mul_le_mul rb avg (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  have p2 := mul_le_mul_of_nonneg_right rr (abs_nonneg (x*y))
  dsimp only [D] at pay
  linarith only [s,p1,p2,pay,pp]

#print axioms projected_pairs_sum
#print axioms prime_pair_projection_limit
end GoldbachSpectral435.GoldbachSieve
