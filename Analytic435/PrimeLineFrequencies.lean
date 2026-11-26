module
public import LineFrequencyInversion
public import PairLineTransforms
public import SharpNearLineLimit

/-! The Fourier integrand of an individual prime line at fixed physical frequency. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Finset MeasureTheory
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open PhysicalTests

def cosTest (t : ℝ) (f : ℝ→ℝ) (u : ℝ) := f u*Real.cos (t*u)
def sinTest (t : ℝ) (f : ℝ→ℝ) (u : ℝ) := f u*Real.sin (t*u)

def modulated {f : ℝ→ℝ} (hf : FiniteModelWeight f) (h : ℝ→ℝ) (hh : ContDiff ℝ 6 h) :
    FiniteModelWeight (fun u => f u*h u) where
  smooth := hf.smooth.mul hh
  lower := hf.lower
  upper := hf.upper
  lower_pos := hf.lower_pos
  upper_lt_one := hf.upper_lt_one
  lower_le_upper := hf.lower_le_upper
  support_subset := fun u hu => hf.support_subset (fun z => hu (by simp [z]))

def cosWeight {f : ℝ→ℝ} (hf : FiniteModelWeight f) (t : ℝ) : FiniteModelWeight (cosTest t f) :=
  modulated hf _ (by fun_prop)
def sinWeight {f : ℝ→ℝ} (hf : FiniteModelWeight f) (t : ℝ) : FiniteModelWeight (sinTest t f) :=
  modulated hf _ (by fun_prop)

def phaseMix (sign : Bool) (v cc ss sc cs : ℝ) :=
  let e : ℝ := if sign then 1 else -1
  Real.cos v*(cc-e*ss)+Real.sin v*(sc+e*cs)

private def grid (q M : ℕ) (d : ℤ) (sign : Bool) : (ℕ→ℕ→ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∑ n∈range M,∑ m∈range M,if (q:ℤ)∣lineCoordinate sign n m-d then F n m else 0
  map_add' F G := by
    simp only [Pi.add_apply,← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro m _
    split <;> simp
  map_smul' c F := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_sum]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro m _
    split <;> simp

private def pairFunction (q M : ℕ) (f g : ℝ→ℝ) (n m : ℕ) : ℝ :=
  siftedWeight q M f n*siftedWeight q M g m

private lemma grid_pair (q M H : ℕ) [NeZero q] (sign : Bool) (f g : ℝ→ℝ) :
    grid q M H sign (pairFunction q M f g)=classPairs q H M M sign f g := by
  rw [class_pairs_lines]
  rfl

theorem prime_frequency_expansion (q M H : ℕ) [NeZero q] (sign : Bool) (f g : ℝ→ℝ) (t : ℝ) :
    frequencySlice q M H sign (siftedWeight q M f) (siftedWeight q M g) t=
      phaseMix sign (t*(H/(M:ℝ)))
        (classPairs q H M M sign (cosTest t f) (cosTest t g))
        (classPairs q H M M sign (sinTest t f) (sinTest t g))
        (classPairs q H M M sign (sinTest t f) (cosTest t g))
        (classPairs q H M M sign (cosTest t f) (sinTest t g)) := by
  let P := pairFunction q M
  let A := grid q M H sign
  let F := fun n m : ℕ => P f g n m*Real.cos (t*(((lineCoordinate sign n m-(H:ℤ):ℤ):ℝ)/M))
  let v := t*(H/(M:ℝ))
  let e : ℝ := if sign then 1 else -1
  have eq : F=Real.cos v • (P (cosTest t f) (cosTest t g)-e • P (sinTest t f) (sinTest t g))+
      Real.sin v • (P (sinTest t f) (cosTest t g)+e • P (cosTest t f) (sinTest t g)) := by
    funext n m
    let x := t*(n/(M:ℝ))
    let y := t*(m/(M:ℝ))
    have trig : Real.cos (t*(((lineCoordinate sign n m-(H:ℤ):ℤ):ℝ)/M))=
        phaseMix sign v (Real.cos x*Real.cos y) (Real.sin x*Real.sin y)
          (Real.sin x*Real.cos y) (Real.cos x*Real.sin y) := by
      cases sign
      · have arg : t*(((lineCoordinate false n m-(H:ℤ):ℤ):ℝ)/M)=x-y-v := by
          simp only [lineCoordinate,Bool.false_eq_true,ite_false,Int.cast_sub,Int.cast_natCast,x,y,v]; ring
        rw [arg,Real.cos_sub (x-y) v,Real.cos_sub,Real.sin_sub]
        simp only [phaseMix,Bool.false_eq_true,ite_false]
        ring
      · have arg : t*(((lineCoordinate true n m-(H:ℤ):ℤ):ℝ)/M)=x+y-v := by
          simp only [lineCoordinate,ite_true,Int.cast_sub,Int.cast_add,Int.cast_natCast,x,y,v]; ring
        rw [arg,Real.cos_sub (x+y) v,Real.cos_add,Real.sin_add]
        simp only [phaseMix,ite_true]
        ring
    dsimp only [F]
    rw [trig]
    simp only [P,pairFunction,phaseMix,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      siftedWeight,weightedMangoldt,cosTest,sinTest,x,y,e]
    split_ifs <;> ring
  change A F=_
  rw [eq,map_add,map_smul,map_smul,map_sub,map_add,map_smul,map_smul]
  simp only [A,P,grid_pair,smul_eq_mul,phaseMix,v,e]

def unitIntegral (f : ℝ→ℝ) := ∫ u in (0:ℝ)..1,f u

def frequencyProfile (sign : Bool) (v t : ℝ) (f g : ℝ→ℝ) :=
  phaseMix sign v
    (unitIntegral (cosTest t f)*unitIntegral (cosTest t g)) (unitIntegral (sinTest t f)*unitIntegral (sinTest t g))
    (unitIntegral (sinTest t f)*unitIntegral (cosTest t g)) (unitIntegral (cosTest t f)*unitIntegral (sinTest t g))

private lemma phase_stable (sign : Bool) (v ε : ℝ) {a b c d A B C D : ℝ}
    (ha : |a-A|≤ε) (hb : |b-B|≤ε) (hc : |c-C|≤ε) (hd : |d-D|≤ε) :
    |phaseMix sign v a b c d-phaseMix sign v A B C D|≤4*ε := by
  let s : ℝ := if sign then 1 else -1
  have ab : |s|=1 := by cases sign <;> norm_num [s]
  have comb (x y : ℝ) (hx : |x|≤ε) (hy : |y|≤ε) : |x+s*y|≤2*ε := by
    have tr := abs_add_le x (s*y)
    rw [abs_mul,ab,one_mul] at tr
    linarith only [tr,hx,hy]
  have first := comb (a-A) (-(b-B)) ha (by simpa only [abs_neg] using hb)
  have second := comb (c-C) (d-D) hc hd
  let x := (a-A)+s*(-(b-B))
  let y := (c-C)+s*(d-D)
  have eq : phaseMix sign v a b c d-phaseMix sign v A B C D=Real.cos v*x+Real.sin v*y := by
    dsimp only [phaseMix,x,y,s]; ring
  rw [eq]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  have u := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one v) (abs_nonneg x)
  have z := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one v) (abs_nonneg y)
  change |x|≤2*ε at first
  change |y|≤2*ε at second
  linarith only [u,z,first,second]

/-- For each fixed physical frequency the original two-prime integral
agrees with the Fourier transform of its continuous line profile, uniformly
in the location of the specified line over the full spectral horizon. -/
theorem prime_frequency_limit (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g)
    (t ε : ℝ) (ep : 0<ε) :
    ∃ η : ℝ, 0<η ∧ ∀ᶠ N : ℕ in atTop, ∀ M H j : ℕ, N≤M → 0<H → Even H → H≤2*scale N*N →
      let q := liftedModulus (localCutoff N) j
      q≤M → (q:ℝ)*(6+Real.log q)^2≤η^2*M → GRH q → ∀ sign : Bool,
      |(q:ℝ)*frequencySlice q M H sign (siftedWeight q M f) (siftedWeight q M g) t/
        ((M:ℝ)^2*singularSeries H)-frequencyProfile sign (t*(H/(M:ℝ))) t f g|≤ε := by
  let δ := ε/4
  have dp : 0<δ := by dsimp [δ]; positivity
  obtain ⟨a,ap,A⟩ := sharp_near_line_limit _ _ (cosWeight hf t) (cosWeight hg t) δ dp
  obtain ⟨b,bp,B⟩ := sharp_near_line_limit _ _ (sinWeight hf t) (sinWeight hg t) δ dp
  obtain ⟨c,cp,C⟩ := sharp_near_line_limit _ _ (sinWeight hf t) (cosWeight hg t) δ dp
  obtain ⟨d,dup,D⟩ := sharp_near_line_limit _ _ (cosWeight hf t) (sinWeight hg t) δ dp
  let η := min (min a b) (min c d)
  have hp : 0<η := lt_min (lt_min ap bp) (lt_min cp dup)
  refine ⟨η,hp,?_⟩
  filter_upwards [A,B,C,D] with N aa bb cc dd
  intro M H j nm hn ev hh q qm cap grh sign
  have cap' (u : ℝ) (le : η≤u) : (q:ℝ)*(6+Real.log q)^2≤u^2*M :=
    cap.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp.le le 2) (Nat.cast_nonneg _))
  have p := aa M H j nm hn ev hh qm (cap' a ((min_le_left ..).trans (min_le_left ..))) grh sign
  have r := bb M H j nm hn ev hh qm (cap' b ((min_le_left ..).trans (min_le_right ..))) grh sign
  have s := cc M H j nm hn ev hh qm (cap' c ((min_le_right ..).trans (min_le_left ..))) grh sign
  have w := dd M H j nm hn ev hh qm (cap' d ((min_le_right ..).trans (min_le_right ..))) grh sign
  let v := t*(H/(M:ℝ))
  have result := phase_stable sign v δ p r s w
  rw [prime_frequency_expansion]
  unfold frequencyProfile
  have scal (x y z w k : ℝ) : k*phaseMix sign v x y z w=phaseMix sign v (k*x) (k*y) (k*z) (k*w) := by
    dsimp [phaseMix]; ring
  have rearrange (x : ℝ) : (q:ℝ)*x/((M:ℝ)^2*singularSeries H)=((q:ℝ)/((M:ℝ)^2*singularSeries H))*x := by ring
  rw [rearrange,scal]
  dsimp only [q] at rearrange
  simp_rw [rearrange] at result
  exact result.trans_eq (by dsimp [δ]; ring)

#print axioms prime_frequency_limit
#print axioms prime_frequency_expansion
end GoldbachSpectral435.GoldbachSieve
