module
public import RowMean

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral GoldbachSpectral.BandSieve Finset
namespace GoldbachSpectral435

theorem center_count {M q a : ℕ} (qp : 0<q) (small : q≤M) :
    (((range M).filter (fun n : ℕ => (n:ZMod q)=(a:ZMod q))).card:ℝ) ≤ 2*(M:ℝ)/q := by
  let S := (range M).filter (fun n : ℕ => (n:ZMod q)=(a:ZMod q))
  have ct := card_le_card_of_injOn (s := S) (t := range (M/q+1)) (fun n => n/q)
    (fun n hn => mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.div_le_div_right (mem_range.mp (mem_filter.mp hn).1).le)))
    (fun n hn m hm eqn => by
      have modn := (ZMod.natCast_eq_natCast_iff n a q).mp (mem_filter.mp hn).2
      have modm := (ZMod.natCast_eq_natCast_iff m a q).mp (mem_filter.mp hm).2
      have r : n%q=m%q := modn.trans modm.symm
      have idn := Nat.mod_add_div n q
      have idm := Nat.mod_add_div m q
      change n/q=m/q at eqn
      rw [r,eqn] at idn
      omega)
  rw [card_range] at ct
  have h := Nat.mul_le_mul_right q ct
  rw [Nat.add_mul,one_mul] at h
  have d := Nat.div_mul_le_self M q
  apply (le_div_iff₀ (by exact_mod_cast qp)).mpr
  exact_mod_cast (show S.card*q≤2*M by omega)

theorem band_to_test {P H a N : ℕ} (pp : 0<P) (cut : 2*P<N) (D : ℝ) :
    oppositeSum N (fun x => shape a H P x/D) = bandObservable P H a N/D := by
  classical
  have include' : Icc P (2*P) ⊆ range N := fun m hm => mem_range.mpr ((mem_Icc.mp hm).2.trans_lt cut)
  have zero (m : ℕ) (outside : m∉Icc P (2*P)) : shape a H P m=0 := by
    have op : outer ((m:ℝ)/P)=0 := by
      by_contra nz
      change (m:ℝ)/P ∈ Function.support outer at nz
      rw [outer.support_eq,Metric.mem_ball,Real.dist_eq,abs_lt] at nz
      change -(1/2:ℝ)<(m:ℝ)/P-3/2 ∧ (m:ℝ)/P-3/2<1/2 at nz
      have pr : 0<(P:ℝ) := by exact_mod_cast pp
      have l := (lt_div_iff₀ pr).mp (by linarith [nz.1] : 1<(m:ℝ)/P)
      have u := (div_lt_iff₀ pr).mp (by linarith [nz.2] : (m:ℝ)/P<2)
      exact outside (mem_Icc.mpr ⟨by exact_mod_cast (by linarith : (P:ℝ)≤m),by exact_mod_cast u.le⟩)
    simp [shape,op]
  unfold oppositeSum bandObservable
  rw [← Finset.sum_subset include' (fun m _ no => by simp [zero m no]),Finset.sum_div]
  apply sum_congr rfl
  intro m _
  split_ifs <;> ring

/-- A positive weighted row mean detects one genuine large even target.
The progression need not have an invertible central residue. -/
theorem modulus_witness (M q P H a : ℕ) (qp : 0<q) (small : q≤M) (eq : Even q) (ea : Even a)
    (B : ℝ) (bp : 0<B) (signal : (2*(M:ℝ)/q)*B < rowMean q M P H a) :
    ∃ N<M, Even N ∧ M<4*N ∧ B<bandObservable P H a N := by
  classical
  let S := (range M).filter (fun n : ℕ => (n:ZMod q)=(a:ZMod q))
  have mr : 0<(M:ℝ) := by exact_mod_cast qp.trans_le small
  have total : rowMean q M P H a=∑ n∈S,broad (n/(M:ℝ))*bandObservable P H a n := by
    simp only [S,rowMean,sum_filter]
  by_contra! none
  have point (n : ℕ) (hn : n∈S) : broad (n/(M:ℝ))*bandObservable P H a n≤B := by
    by_cases nz : broad (n/(M:ℝ))=0
    · simp [nz,bp.le]
    · have ar := (mem_filter.mp hn).2
      have modN := (ZMod.natCast_eq_natCast_iff n a q).mp ar
      have par := modN.of_dvd (even_iff_two_dvd.mp eq)
      have eqn : Even n := (Nat.even_iff).mpr (Eq.trans (show n%2=a%2 from par) (Nat.even_iff.mp ea))
      have supp := (broad_support nz).1
      have h := (lt_div_iff₀ mr).mp supp
      have large : M<4*n := by exact_mod_cast (by linarith : (M:ℝ)<4*n)
      have v := none n (mem_range.mp (mem_filter.mp hn).1) eqn large
      exact (mul_le_mul_of_nonneg_left v broad.nonneg).trans (mul_le_of_le_one_left bp.le broad.le_one)
  have ub := Finset.sum_le_sum point
  rw [← total,sum_const,nsmul_eq_mul] at ub
  exact (not_le_of_gt signal) (ub.trans (mul_le_mul_of_nonneg_right (center_count qp small) bp.le))

#print axioms modulus_witness
end GoldbachSpectral435

