module
public import LineTailCriterion
public import GoldbachPrimeCounts

/-! The frequency tail on the first Goldbach line and its relation to
the original residual form and the ordinary ordered-prime count. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Finset MeasureTheory
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open FirstLineLimits GoldbachPrimitive

def reflectedProduct (f g : ℝ→ℝ) (u : ℝ) := f u*g (1-u)

private def reflectedWeight {f g : ℝ→ℝ} (hf : FiniteModelWeight f) (hg : FiniteModelWeight g) :
    FiniteModelWeight (reflectedProduct f g) where
  smooth := hf.smooth.mul (hg.smooth.comp (contDiff_const.sub contDiff_id))
  lower := hf.lower
  upper := hf.upper
  lower_pos := hf.lower_pos
  upper_lt_one := hf.upper_lt_one
  lower_le_upper := hf.lower_le_upper
  support_subset := fun _ h => hf.mem_support_interval (left_ne_zero_of_mul h)

private lemma reflection_cutoff (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ g : ℝ→ℝ, Nonempty (FiniteModelWeight g) ∧ reflectedProduct f g=f := by
  let d := min hf.lower (1-hf.upper)/4
  have dp : 0<d := div_pos (lt_min hf.lower_pos (sub_pos.mpr hf.upper_lt_one)) (by norm_num)
  have l : 2*d≤hf.lower := by dsimp [d]; linarith [hf.lower_pos,min_le_left hf.lower (1-hf.upper)]
  have r : hf.upper≤1-2*d := by dsimp [d]; linarith [hf.upper_lt_one,min_le_right hf.lower (1-hf.upper)]
  have ends := hf.lower_le_upper
  refine ⟨cutoff d,⟨⟨cutoff_smooth d,d,1-d,dp,by linarith,by linarith,cutoff_support dp⟩⟩,?_⟩
  funext u
  by_cases z : f u=0
  · simp [reflectedProduct,z]
  obtain ⟨left,right⟩ := hf.mem_support_interval z
  rw [reflectedProduct,cutoff_one dp (by linarith) (by linarith),mul_one]

theorem observed_as_line (N : ℕ) (np : 0<N) (f g : ℝ→ℝ) :
    exactLine N N N true (siftedWeight N N f) (siftedWeight N N g)/((N:ℝ)*singularSeries N)=
      observed N (reflectedProduct f g) := by
  unfold observed exactLine
  rw [← div_div,sum_div]
  congr 1
  apply sum_congr rfl
  intro n hn
  have small := mem_range.mp hn
  have nr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr np.ne'
  by_cases zero : n=0
  · subst n
    simp [siftedWeight,weightedMangoldt,mass,mangoldt,reflectedProduct]
  have inside : N-n∈range N := mem_range.mpr (by omega)
  rw [sum_eq_single_of_mem (N-n) inside]
  · have yes : lineCoordinate true n (N-n)=N := by simp [lineCoordinate]; omega
    have cop : (N-n).Coprime N ↔ n.Coprime N := by
      calc
        _ ↔ (N-n).Coprime ((N-n)+n) := by rw [Nat.sub_add_cancel small.le]
        _ ↔ (N-n).Coprime n := Nat.coprime_self_add_right
        _ ↔ N.Coprime n := Nat.coprime_sub_self_left small.le
        _ ↔ _ := Nat.coprime_comm
    have arg : ((N-n:ℕ):ℝ)/N=1-(n:ℝ)/N := by rw [Nat.cast_sub small.le,sub_div,div_self nr]
    by_cases c : n.Coprime N
    · simp only [yes,ite_true,siftedWeight,weightedMangoldt,mass,reflectedProduct,cop,ite_eq_left c,arg]
      ring
    · simp only [yes,ite_true,siftedWeight,weightedMangoldt,mass,reflectedProduct,cop,ite_eq_right c,zero_mul,zero_div]
  · intro m _ ne
    apply ite_eq_right
    intro eq
    simp only [lineCoordinate,ite_true] at eq
    omega

namespace LineSequence

def GoldbachTail (D : LineSequence) : Prop := ∀ (f g : ℝ→ℝ),
  FiniteModelWeight f → FiniteModelWeight g → ∀ ε : ℝ, 0<ε →
    ∀ᶠ B : ℝ in atTop, ∀ᶠ i in atTop, |D.tailIntegral true f g (angular B) i|≤ε

/-- On the first line the whole family of signed frequency tails is
equivalent to uniform decay of the residual form in its exact energy norm. -/
theorem first_scale_iff_tail (D : LineSequence) (first : D.shift=D.length)
    (grh : ∀ i, GRH (D.length i)) : FirstScaleDecay D.length ↔ D.GoldbachTail := by
  have pos (i : ℕ) : 0<D.length i := first ▸ D.positive i
  let (i : ℕ) : NeZero (D.length i) := ⟨(pos i).ne'⟩
  have ev (i : ℕ) : Even (D.length i) := first ▸ D.even_shift i
  have growth := tendsto_atTop_mono D.base_le D.growing
  have ord : Tendsto D.ordinate atTop (𝓝 1) := by
    have eq : D.ordinate=fun _ => (1:ℝ) := by funext i; simp [ordinate,first,(pos i).ne']
    rw [eq]; exact tendsto_const_nhds
  have equivalence (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g) :
      Tendsto (fun i => observed (D.length i) (reflectedProduct f g)) atTop (𝓝 (mean (reflectedProduct f g))) ↔
      ∀ ε : ℝ, 0<ε → ∀ᶠ B : ℝ in atTop, ∀ᶠ i in atTop, |D.tailIntegral true f g (angular B) i|≤ε := by
    let v := mean (reflectedProduct f g)
    let obs := fun i => observed (D.length i) (reflectedProduct f g)
    let exact := D.exactMass true f g
    have diff : Tendsto (fun i => exact i-obs i) atTop (𝓝 0) := by
      have heq (i : ℕ) : D.siftedMassAt (D.length i) true f g i=obs i := by
        unfold siftedMassAt; rw [first]; exact observed_as_line _ (pos i) f g
      simpa only [heq] using D.sifting_limit_at D.length pos (fun _ => le_rfl) true f g hf hg
    have bridge : Tendsto obs atTop (𝓝 v) ↔ Tendsto exact atTop (𝓝 v) := by
      constructor <;> intro h
      · simpa only [sub_add_cancel,zero_add] using diff.add h
      · simpa only [sub_sub_cancel,sub_zero] using h.sub diff
    exact bridge.trans (D.exact_line_iff_tail true f g hf hg 1 ord)
  constructor
  · intro cap f g hf hg
    exact (equivalence f g hf hg).mp (smooth_limit cap growth ev grh _ (reflectedWeight hf hg))
  · intro tails
    apply (first_scale_iff_sharp growth ev grh).mpr
    apply uniform_sharp_of_pointwise
    apply sharp_limit_of_smooth growth ev
    intro f hf
    obtain ⟨g,⟨hg⟩,eq⟩ := reflection_cutoff f hf
    simpa only [eq] using (equivalence f g hf hg).mpr (tails f g hf hg)

theorem prime_counts_iff_tail (D : LineSequence) (first : D.shift=D.length)
    (grh : ∀ i, GRH (D.length i)) : PrimeCountDecay D.length ↔ D.GoldbachTail := by
  have pos (i : ℕ) : 0<D.length i := first ▸ D.positive i
  let (i : ℕ) : NeZero (D.length i) := ⟨(pos i).ne'⟩
  exact (first_scale_iff_prime (tendsto_atTop_mono D.base_le D.growing) (fun i => first ▸ D.even_shift i) grh).symm.trans
    (D.first_scale_iff_tail first grh)

theorem goldbach_tail_of_exists (D : LineSequence) (first : D.shift=D.length)
    (grh : ∀ i, GRH (D.length i)) (h : ∃ h,HypothesisS h) : D.GoldbachTail := by
  have pos (i : ℕ) : 0<D.length i := first ▸ D.positive i
  let (i : ℕ) : NeZero (D.length i) := ⟨(pos i).ne'⟩
  apply (D.first_scale_iff_tail first grh).mp
  exact first_scale_of_exists h (tendsto_atTop_mono D.base_le D.growing) (fun i => first ▸ D.even_shift i) grh

#print axioms first_scale_iff_tail
#print axioms prime_counts_iff_tail
#print axioms goldbach_tail_of_exists
end LineSequence
end GoldbachSpectral435.GoldbachSieve
