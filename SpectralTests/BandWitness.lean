module
public import SpectralTests.RowShape
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
noncomputable section
namespace GoldbachSpectral.BandSieve
open Finset ArithmeticFunction Filter
open scoped Topology

/-- A row in the difference of the two reduced-residue densities, with the
same real smooth function that occurs in the operator test. -/
def row (q a H P : ℕ) : ℝ :=
  ∑ m∈Finset.Icc P (2*P),vonMangoldt m*shape a H P m*
    ((if (Int.natAbs ((a:ℤ)-m)).Coprime q then (1:ℝ) else 0)-
      (if (a+m).Coprime q then 1 else 0))

theorem row_identity (s : Finset ℕ) (a H P : ℕ) (he : Even a) (hp : 0<H) :
    (∑ m∈Finset.Icc P (2*P), if a≤m ∧ m-a<4*H+1 then
      vfun P m*wfun H (m-a)*((if (m-a).Coprime (wheel s) then (1:ℝ) else 0)-
        (if (a+m).Coprime (wheel s) then 1 else 0)) else 0) = row (wheel s) a H P := by
  apply Finset.sum_congr rfl
  intro m _
  have hh : 0<(H:ℝ) := by exact_mod_cast hp
  by_cases range : a≤m ∧ m-a<4*H+1
  · rw [ite_eq_left range]
    have natabs : Int.natAbs ((a:ℤ)-m)=m-a := by omega
    rw [natabs]
    by_cases odd : Odd m
    · simp only [wfun,vfun,ite_eq_left odd,shape,Nat.cast_sub range.1]
      ring
    · have em := Nat.not_odd_iff_even.mp odd
      have ed : Even (m-a) := by
        obtain ⟨i,hi⟩ := em
        obtain ⟨j,hj⟩ := he
        exact ⟨i-j,by omega⟩
      have es : Even (a+m) := he.add em
      have notunit {n : ℕ} (even : Even n) : ¬n.Coprime (wheel s) := by
        intro u
        exact (Nat.not_odd_iff_even.mpr even) (Nat.coprime_two_right.mp (Nat.coprime_mul_iff_right.mp u).1)
      simp [vfun,odd,notunit ed,notunit es]
  · rw [ite_eq_right range]
    have zero : inner (((m:ℝ)-a)/H)=0 := by
      by_contra z
      change ((m:ℝ)-a)/H ∈ Function.support inner at z
      rw [inner.support_eq,Metric.mem_ball,Real.dist_eq,abs_lt] at z
      change -(3/2:ℝ)<((m:ℝ)-a)/H-5/2 ∧ ((m:ℝ)-a)/H-5/2<3/2 at z
      have lo := (lt_div_iff₀ hh).mp (by linarith [z.1] : 1<((m:ℝ)-a)/H)
      have hi := (div_lt_iff₀ hh).mp (by linarith [z.2] : ((m:ℝ)-a)/H<4)
      have l : a+H<m := by exact_mod_cast (by linarith : (a:ℝ)+H<m)
      have r : m<a+4*H := by exact_mod_cast (by linarith : (m:ℝ)<a+4*H)
      exact range ⟨by omega,by omega⟩
    simp [shape,zero]

/-- For fixed ratio H/P and odd sieve depth, the only error from all
lower layers is proportional to k(s+1)^(k-1) times P log(2P). -/
theorem row_signal (ρ : ℝ) (rp : 0<ρ) :
    ∃ X V : ℝ, 0<V ∧ ∀ (s : Finset ℕ) (z k H P : ℕ),
      X≤P → 4≤P → 0<H → 2≤z → Odd k → (∀ p∈s,p.Prime) → (∀ p∈s,z<p) →
      4*H+1≤z^k → 4*H+1≤P → 4*P<z^(k+1) → 32*H≤P → ρ*P≤H →
      (∀ t∈s.powersetCard k, 32*(∏ p∈t,p)≤P) →
      ∃ a≤2*P, Even a ∧
        ((s.card.choose k:ℕ):ℝ)*(H/4:ℝ) -
          ((k*(s.card+1)^(k-1):ℕ):ℝ)*V*((P+1:ℝ)*Real.log (2*P)) ≤
            (2*P+1:ℝ)*max 0 (row (wheel s) a H P) := by
  obtain ⟨X,M⟩ := signed_matrix_lower ρ rp
  obtain ⟨V,vp,W⟩ := variation_bound
  refine ⟨X,V,vp,?_⟩
  intro s z k H P hX pp hp hz od pr band top left maxN len ratio bound
  obtain ⟨wp,np,plat,prime,mass⟩ := sample_data pp hp
  have lower := M s z k H (4*H+1) P (wfun H) (vfun P) hX hz od pr band top left maxN len ratio
    (by omega) bound wp np plat prime
  rw [transpose s pr P (4*H+1) left (wfun H) (vfun P) (fun m no => by simp [vfun,no])] at lower
  let A := (Finset.range (2*P+1)).filter Even
  have tab : (∑ a∈A, ∑ m∈Finset.Icc P (2*P), if a≤m ∧ m-a<4*H+1 then
      vfun P m*wfun H (m-a)*((if (m-a).Coprime (wheel s) then (1:ℝ) else 0)-
        (if (a+m).Coprime (wheel s) then 1 else 0)) else 0) =
      ∑ a∈A,row (wheel s) a H P := by
    exact sum_congr rfl (fun a ha => row_identity s a H P (mem_filter.mp ha).2 hp)
  rw [tab] at lower
  have large := Finset.exists_max_image A (fun a => row (wheel s) a H P)
    (show A.Nonempty from ⟨0,mem_filter.mpr ⟨mem_range.mpr (by omega),(by decide : Even (0:ℕ))⟩⟩)
  obtain ⟨a,ha,biggest⟩ := large
  obtain ⟨ra,ea⟩ := mem_filter.mp ha
  refine ⟨a, Nat.lt_succ_iff.mp (mem_range.mp ra),ea,?_⟩
  have m := mul_le_mul (mul_le_mul_of_nonneg_left (W H hp) (Nat.cast_nonneg (k*(s.card+1)^(k-1)))) mass
    (sum_nonneg (fun m _ => np m)) (mul_nonneg (Nat.cast_nonneg _) vp.le)
  apply (sub_le_sub_left m _).trans (lower.trans ?_)
  have h := sum_le_sum (s := A) (fun i hi => (biggest i hi).trans (le_max_right 0 _))
  simp only [sum_const,nsmul_eq_mul] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (le_max_left _ _)
  have ca := (Finset.card_le_card (Finset.filter_subset Even (range (2*P+1)))).trans (card_range _).le
  exact_mod_cast ca

end GoldbachSpectral.BandSieve

