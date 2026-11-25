module
public import PositiveWidth

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral Filter
open scoped Topology
namespace GoldbachSpectral435

/-- A predicate using only a finite opposite-shift sum and smooth test functions. -/
def arithmeticGain (d N : ℕ) : Prop :=
  ∃ H P b, ShiftTest N H P b ∧ P^2*Real.log N^d < H*(oppositeSum N b)^2

theorem arbitrarily_large_test (g : ∀ N, GRH N) (d K : ℕ) :
    ∃ N≥K, Even N ∧ arithmeticGain d N := by
  classical
  by_contra! none
  let m (N : ℕ) := Real.sqrt (Real.log N^d / N)
  have identity (N : ℕ) (hn : 0<N) : (N:ℝ)*(m N)^2=Real.log N^d := by
    have pos : 0<(N:ℝ) := by exact_mod_cast hn
    have lg := Real.log_nonneg (show 1≤(N:ℝ) by exact_mod_cast hn)
    dsimp only [m]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have transfer : ShiftTransfer m GRH := by
    refine ⟨1,one_pos,max K 1,?_⟩
    intro N hn ev _ H P b test
    have bound : H*(oppositeSum N b)^2 ≤ P^2*Real.log N^d := by
      by_contra! large
      exact none N (by omega) ev ⟨H,P,b,test,large⟩
    simpa only [one_mul,mul_assoc,identity N (by omega)] using bound
  obtain ⟨N,hn,_,high⟩ := growth_from_shift_transfer g transfer d 1
  exact (not_lt_of_ge (identity N (by omega)).le) (high (g N))

/-- A record is selected using only arithmetic and the prescribed elementary
functions h_j. The definition can be evaluated as a logical predicate without
any hypothesis about an operator or any of its zeros. -/
def arithmeticRecordAt (j K N : ℕ) : Prop :=
  K<N ∧ Even N ∧ (∀ n≥N, (j:ℝ)≤prescribedH j n) ∧ arithmeticGain (j+8) N

private theorem next_exists (g : ∀ N, GRH N) (j K : ℕ) :
    ∃ N, arithmeticRecordAt j K N := by
  obtain ⟨F,large⟩ := eventually_atTop.mp ((prescribed_admissible j).2.1.eventually_ge_atTop (j:ℝ))
  obtain ⟨N,hn,ev,gain⟩ := arbitrarily_large_test g (j+8) (max F (K+1))
  exact ⟨N,by omega,ev,fun n h => large n (by omega),gain⟩

def nextRecord (j K : ℕ) : ℕ := sInf {N | arithmeticRecordAt j K N}

def recordIndex : ℕ → ℕ
  | 0 => nextRecord 0 2
  | j+1 => nextRecord (j+1) (recordIndex j)

private theorem next_spec (g : ∀ N, GRH N) (j K : ℕ) :
    arithmeticRecordAt j K (nextRecord j K) := Nat.sInf_mem (next_exists g j K)

private theorem record_increases (g : ∀ N, GRH N) : StrictMono recordIndex :=
  strictMono_nat_of_lt_succ fun j => (next_spec g (j+1) (recordIndex j)).1

private theorem record_data (g : ∀ N, GRH N) (j : ℕ) :
    Even (recordIndex j) ∧ (∀ n≥recordIndex j, (j:ℝ)≤prescribedH j n) ∧
      arithmeticGain (j+8) (recordIndex j) := by
  cases j with
  | zero => exact (next_spec g 0 2).2
  | succ j => exact (next_spec g (j+1) (recordIndex j)).2

def recordStage (N : ℕ) : ℕ := Nat.findGreatest (fun j => recordIndex j≤N) N

def arithmeticH (N : ℕ) : ℝ := prescribedH (recordStage N) N

private theorem stage_at (g : ∀ N, GRH N) (j : ℕ) : recordStage (recordIndex j)=j := by
  apply Nat.findGreatest_eq_iff.mpr
  exact ⟨(record_increases g).id_le j,fun _ => le_rfl,fun {_} hi _ => not_le_of_gt (record_increases g hi)⟩

private theorem stage_grows (g : ∀ N, GRH N) : Tendsto recordStage atTop atTop := by
  apply tendsto_atTop.mpr
  intro j
  filter_upwards [eventually_ge_atTop (recordIndex j)] with N hn
  exact Nat.le_findGreatest ((record_increases g).id_le j |>.trans hn) hn

private theorem stage_lower (N : ℕ) (h : recordIndex 0≤N) : recordIndex (recordStage N)≤N :=
  Nat.findGreatest_spec (P := fun j => recordIndex j≤N) (Nat.zero_le N) h

private theorem width_stage (N : ℕ) (hn : 1<N) :
    zeroFreeWidth N arithmeticH=logWidth (recordStage N) N := by
  change GoldbachSpectral.width N (singularSeries N) (prescribedH (recordStage N) N)=_
  rw [original_series,prescribed_width _ N hn]

theorem arithmeticH_admissible (g : ∀ N, GRH N) : IsAdmissible arithmeticH := by
  refine ⟨fun N _ _ => (prescribed_admissible (recordStage N)).1 N,?_,?_⟩
  · intro B
    obtain ⟨K,large⟩ := eventually_atTop.mp
      (((tendsto_natCast_atTop_atTop (R := ℝ)).comp (stage_grows g)).eventually_ge_atTop B)
    refine ⟨max K (recordIndex 0),fun N hn _ => ?_⟩
    exact (large N (by omega)).trans ((record_data g (recordStage N)).2.1 N (stage_lower _ (by omega)))
  · obtain ⟨K,large⟩ := eventually_atTop.mp eventually_small_series
    refine ⟨max 2 K,fun N hn _ => ?_⟩
    change zeroFreeWidth N arithmeticH≤1/4
    rw [width_stage N (by omega),logWidth]
    have lg := (large N (by omega)).1
    have pow := one_le_pow₀ (by linarith : 1≤Real.log N) (n := recordStage N)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith

theorem arithmetic_width_decay (g : ∀ N, GRH N) (j : ℕ) :
    Tendsto (fun N : ℕ => Real.log N^j*zeroFreeWidth N arithmeticH) atTop (𝓝 0) := by
  have logs := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have decay : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp logs
  apply squeeze_zero' _ _ decay
  · filter_upwards [eventually_ge_atTop (2:ℕ),logs.eventually_ge_atTop 1] with N hn lg
    change 1≤Real.log N at lg
    rw [width_stage N (by omega),logWidth]
    positivity
  · filter_upwards [eventually_ge_atTop (2:ℕ),logs.eventually_ge_atTop 1,
      (stage_grows g).eventually_ge_atTop (j+1)] with N hn lg big
    change 1≤Real.log N at lg
    rw [width_stage N (by omega),logWidth,mul_one_div,← one_div,
      div_le_div_iff₀ (by positivity) (by positivity),one_mul]
    have pow := pow_le_pow_right₀ lg big
    rw [pow_succ] at pow
    nlinarith only [pow,pow_nonneg (zero_le_one.trans lg) (recordStage N)]

/-- Failure for one prescribed width smaller than every fixed inverse power of
log N. Its stage changes at arithmetic records, independently of the spectrum. -/
theorem arithmetic_width_refuted (g : ∀ N, GRH N) : ¬HypothesisS arithmeticH := by
  intro S
  obtain ⟨C,cp,F,transfer⟩ := shiftTransfer_original
  obtain ⟨K,claim⟩ := S.2.and evenEventually_large
  obtain ⟨L,cap⟩ := eventually_atTop.mp eventually_small_series
  have logs := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨V,coefficient⟩ := eventually_atTop.mp (logs.eventually_ge_atTop C)
  let j := max (max F K) (max L V)
  let N := recordIndex j
  have nj : j≤N := (record_increases g).id_le j
  obtain ⟨ev,_,H,P,b,test,hit⟩ := record_data g j
  change Even N at ev
  obtain ⟨free,lar⟩ := claim N (by dsimp [j] at nj; omega) ev
  obtain ⟨four,lp,ha⟩ := large_parameters lar
  let : NeZero N := ⟨by omega⟩
  obtain ⟨lg,small⟩ := cap N (by dsimp [j] at nj; omega)
  have cN : C≤Real.log N := coefficient N (by dsimp [j] at nj; omega)
  have C2 : C≤(Real.log N)^2 := cN.trans (by nlinarith only [lg,sq_nonneg (Real.log N-1)])
  have est := transfer N (by dsimp [j] at nj; omega) ev (g N) H P b test
  have posP : 0<P := lt_of_lt_of_le zero_lt_one (test.one_le.trans test.width_le)
  have normalized : (Real.log N)^(j+8)<C*((N:ℝ)*(eligibleNorm N)^2) := by
    apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos posP)).mp
    exact hit.trans_le (est.trans_eq (by ring))
  have scaled := mul_le_mul_of_nonneg_right C2
    (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg (eligibleNorm N)))
  have gain := normalized.trans_le (scaled.trans_eq (mul_comm _ _))
  rw [show j+8=(j+6)+2 by omega,pow_add] at gain
  have large := (mul_lt_mul_iff_left₀ (sq_pos_of_pos lp)).mp gain
  have f := free (g N) inferInstance ha
  rw [width_stage N (by omega),show recordStage N=j from stage_at g j] at f
  exact (logWidth_fails (by omega : 0<N) lg small large)
    (squared_bound_of_exclusion j ev lar (g N) ha lg f)

#print axioms arbitrarily_large_test
#print axioms arithmeticH_admissible
#print axioms arithmetic_width_decay
#print axioms arithmetic_width_refuted
end GoldbachSpectral435

