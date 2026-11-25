module
public import PaperPremise

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral Filter Set
open scoped Topology
namespace GoldbachSpectral435

/-- A thinning of the records selected using opposite-shift sums. -/
def recordSet (p : ℕ → ℕ) : Set ℕ := Set.range (fun j => recordIndex (p j))

attribute [local instance] Classical.propDecidable

def patchedH (p : ℕ → ℕ) (base : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n ∈ recordSet p then arithmeticH n else base n

theorem patched_eq_off (p : ℕ → ℕ) (base : ℕ → ℝ) {n : ℕ} (hn : n ∉ recordSet p) :
    patchedH p base n = base n := ite_eq_right hn

private theorem patch_width (p : ℕ → ℕ) (base : ℕ → ℝ) (n : ℕ) :
    zeroFreeWidth n (patchedH p base) =
      if n ∈ recordSet p then zeroFreeWidth n arithmeticH else zeroFreeWidth n base := by
  by_cases h : n ∈ recordSet p <;> simp [zeroFreeWidth,patchedH,h]

theorem sparse_failure (G : EvenEventually GRH) (p : ℕ → ℕ) (hp : StrictMono p)
    (base : ℕ → ℝ) (hb : IsAdmissible base) :
    IsAdmissible (patchedH p base) ∧ ¬HypothesisS (patchedH p base) := by
  have g := paper_GRH_iff.mp G
  have ha := arithmeticH_admissible g
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro n he hn
      by_cases mem : n ∈ recordSet p <;> simp only [patchedH,mem,ite_true,ite_false]
      exacts [ha.1 n he hn,hb.1 n he hn]
    · intro B
      obtain ⟨K,large⟩ := (ha.2.1 B).and (hb.2.1 B)
      refine ⟨K,fun n hn he => ?_⟩
      obtain ⟨a,b⟩ := large n hn he
      by_cases mem : n ∈ recordSet p <;> simp only [patchedH,mem,ite_true,ite_false] <;> assumption
    · obtain ⟨K,small⟩ := ha.2.2.and hb.2.2
      refine ⟨K,fun n hn he => ?_⟩
      obtain ⟨a,b⟩ := small n hn he
      rw [patch_width]
      split <;> assumption
  · rintro ⟨_,K,free⟩
    obtain ⟨J,late⟩ := eventually_atTop.mp (record_exclusions_fail g)
    let j := max K J
    let n := recordIndex (p j)
    have pj : j ≤ p j := hp.id_le j
    have pn : p j ≤ n := (record_increases g).id_le _
    have mem : n ∈ recordSet p := ⟨j,rfl⟩
    obtain ⟨he,inst,hstrip,fail⟩ := late (p j) ((le_max_right ..).trans pj)
    have yes := free n ((le_max_left ..).trans (pj.trans pn)) he (g n) inst hstrip
    rw [patch_width,ite_eq_left mem] at yes
    exact fail yes

/-- The count includes all natural indices up to and including X. -/
theorem sparse_count (G : EvenEventually GRH) (p : ℕ → ℕ) (hp : ∀ j, 2^j ≤ p j) (X : ℕ) :
    ((Finset.range (X+1)).filter (fun n => n ∈ recordSet p)).card ≤ Nat.log 2 X + 1 := by
  let r := fun j => recordIndex (p j)
  have subs : (Finset.range (X+1)).filter (fun n => n ∈ recordSet p) ⊆
      (Finset.range (Nat.log 2 X + 1)).image r := by
    intro n hn
    obtain ⟨small,j,rfl⟩ := Finset.mem_filter.mp hn
    have bound := Finset.mem_range.mp small
    change recordIndex (p j) < X + 1 at bound
    have exp := (hp j).trans ((record_increases (paper_GRH_iff.mp G)).id_le (p j))
    have log := Nat.le_log_of_pow_le (by decide : 1 < 2) (exp.trans (by omega : recordIndex (p j) ≤ X))
    exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),rfl⟩
  exact (Finset.card_le_card subs).trans (Finset.card_image_le.trans_eq (Finset.card_range _))

private theorem log_width_decay (d : ℕ) :
    Tendsto (fun n : ℕ => Real.log n^d * zeroFreeWidth n (fun i => Real.log i)) atTop (𝓝 0) := by
  have small := (Real.isLittleO_pow_log_id_atTop (n := d+5)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero' _ _ small
  · filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    have l := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : 1 ≤ (n:ℝ))
    unfold zeroFreeWidth
    have s := singularSeries_pos n
    positivity
  · filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    have np : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    have l := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : 1 ≤ (n:ℝ))
    have s : 1 ≤ singularSeries n := by rw [original_series]; exact singular_lower n
    change _ ≤ Real.log n^(d+5)/(n:ℝ)
    unfold zeroFreeWidth
    rw [← mul_div_assoc,show Real.log n^d * (Real.log n^2 * Real.log n^3) = Real.log n^(d+5) by rw [pow_add]; ring]
    apply div_le_div_of_nonneg_left (pow_nonneg l _) np
    simpa using mul_le_mul_of_nonneg_left s np.le

theorem sparse_log_decay (G : EvenEventually GRH) (p : ℕ → ℕ) (d : ℕ) :
    Tendsto (fun n : ℕ => Real.log n^d * zeroFreeWidth n (patchedH p (fun i => Real.log i)))
      atTop (𝓝 0) := by
  simp_rw [patch_width,mul_ite]
  exact (arithmetic_width_decay (paper_GRH_iff.mp G) d).if' (log_width_decay d)

theorem sparse_log_failure (G : EvenEventually GRH) (p : ℕ → ℕ) (hp : StrictMono p) :
    IsAdmissible (patchedH p (fun i => Real.log i)) ∧ ¬HypothesisS (patchedH p (fun i => Real.log i)) :=
  sparse_failure G p hp _ isAdmissible_log

#print axioms sparse_failure
#print axioms sparse_count
#print axioms sparse_log_decay
end GoldbachSpectral435
