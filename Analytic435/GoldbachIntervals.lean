module
public import WindowTightness

/-! Interval masses of the precise measure occurring on the first
Goldbach line of the original operator. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset Filter
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open GoldbachPrimitive

def distribution (N : ℕ) (u : ℝ) : ℝ := (∑ n∈range N, if (n:ℝ)/N<u then mass N n else 0)/singularSeries N

lemma distribution_eq (N : ℕ) (u : ℝ) : primitive N u=singularSeries N*(distribution N u-u) := by
  unfold primitive distribution
  field_simp [(singularSeries_pos N).ne']

private lemma mass_bounds (N n : ℕ) : 0≤mass N n ∧ mass N n≤mangoldt n*mangoldt (N-n)/N := by
  have z : 0≤mangoldt n*mangoldt (N-n)/N := div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg) (Nat.cast_nonneg (α:=ℝ) N)
  unfold mass
  split_ifs <;> simp [z]

lemma window_mass :
    ∃ C : ℝ, 0<C ∧ ∀ N A Y : ℕ, 2^64≤N → Even N → A+Y≤N+1 →
      (∑ n∈Ico A (A+Y), mass N n)/singularSeries N≤
        C*((Y:ℝ)/N+(Real.log N)^2/Real.sqrt N) := by
  obtain ⟨C,cp,h⟩ := mangoldt_window
  refine ⟨C,cp,?_⟩
  intro N A Y big ev inc
  have np : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have sp := singularSeries_pos N
  have ss := (singularSeries_gt_one N).le
  have s := sum_le_sum (s:=Ico A (A+Y)) (fun n _ => (mass_bounds N n).2)
  rw [← sum_div] at s
  have root := Real.sqrt_pos.mpr np
  have rn := Real.sq_sqrt np.le
  have lift : Real.sqrt N*(Real.log N)^2≤Real.sqrt N*(Real.log N)^2*singularSeries N :=
    le_mul_of_one_le_right (by positivity) ss
  apply (div_le_iff₀ sp).mpr
  apply s.trans
  apply (div_le_iff₀ np).mpr
  apply (h N A Y big ev inc).trans
  calc
    _ ≤ C*(Y*singularSeries N+Real.sqrt N*(Real.log N)^2*singularSeries N) := by gcongr
    _ = _ := by field_simp; ring_nf; rw [rn]; ring

private lemma distribution_index (N : ℕ) (np : 0<N) {u : ℝ} (upper : u≤1) :
    distribution N u=(∑ n∈range ⌈u*N⌉₊, mass N n)/singularSeries N := by
  have pos : 0<(N:ℝ) := by exact_mod_cast np
  have c : ⌈u*N⌉₊≤N := Nat.ceil_le.mpr (by simpa using mul_le_mul_of_nonneg_right upper pos.le)
  have eq : (range N).filter (fun n : ℕ => (n:ℝ)/N<u)=range ⌈u*N⌉₊ := by
    ext n
    simp only [mem_filter,mem_range,div_lt_iff₀ pos,← Nat.lt_ceil]
    omega
  unfold distribution
  rw [← sum_filter,eq]

/-- A bound independent of both endpoints. The additive term tends to zero
uniformly in every even modulus, with no assumption on its L-functions. -/
theorem distribution_increment :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 2^64≤N → Even N → ∀ s t : ℝ, 0≤s → s≤t → t≤1 →
      0≤distribution N t-distribution N s ∧
      distribution N t-distribution N s≤C*(t-s+1/N+(Real.log N)^2/Real.sqrt N) := by
  obtain ⟨C,cp,h⟩ := window_mass
  refine ⟨C,cp,?_⟩
  intro N big ev s t s0 st t1
  have np : 0<N := by omega
  have nr : 0<(N:ℝ) := by exact_mod_cast np
  let A := ⌈s*N⌉₊
  let B := ⌈t*N⌉₊
  have ab : A≤B := Nat.ceil_mono (mul_le_mul_of_nonneg_right st nr.le)
  have bn : B≤N := Nat.ceil_le.mpr (by simpa using mul_le_mul_of_nonneg_right t1 nr.le)
  have bv : A+(B-A)=B := Nat.add_sub_of_le ab
  have exactMass : distribution N t-distribution N s=(∑ n∈Ico A B, mass N n)/singularSeries N := by
    rw [distribution_index N np t1,distribution_index N np (st.trans t1),← sub_div,sum_Ico_eq_sub _ ab]
  have width : ((B-A:ℕ):ℝ)/N≤t-s+1/N := by
    have ac : s*N≤(A:ℝ) := Nat.le_ceil _
    have bc : (B:ℝ)<t*N+1 := Nat.ceil_lt_add_one (mul_nonneg (s0.trans st) nr.le)
    rw [Nat.cast_sub ab]
    apply (div_le_iff₀ nr).mpr
    rw [add_mul,div_mul_cancel₀ _ nr.ne']
    linarith
  rw [exactMass]
  refine ⟨div_nonneg (sum_nonneg (fun n _ => (mass_bounds N n).1)) (singularSeries_pos N).le,?_⟩
  have b := h N A (B-A) big ev (by omega)
  rw [bv] at b
  exact b.trans (mul_le_mul_of_nonneg_left (add_le_add width le_rfl) cp.le)

#print axioms distribution_increment
end GoldbachSpectral435.GoldbachSieve
