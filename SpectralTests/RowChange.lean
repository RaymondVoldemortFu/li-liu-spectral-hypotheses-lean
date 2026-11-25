module
public import SpectralTests.BandMass
public import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section
namespace GoldbachSpectral.BandSieve
open Finset

def wheel (s : Finset ℕ) := 2*∏ p∈s,p

private theorem free_indicator (s : Finset ℕ) (n : ℕ) (pr : ∀ p∈s,p.Prime) :
    free s n = if n.Coprime (∏ p∈s,p) then 1 else 0 := by
  classical
  by_cases h : n.Coprime (∏ p∈s,p)
  · rw [ite_eq_left h,free]
    apply Finset.prod_eq_one
    intro p hp
    have c := Nat.coprime_prod_right_iff.mp h p hp
    exact ite_eq_right ((pr p hp).coprime_iff_not_dvd.mp c.symm)
  · rw [ite_eq_right h,free]
    have hn : ¬∀ p ∈ s, n.Coprime p := fun all => h (Nat.coprime_prod_right_iff.mpr all)
    push Not at hn
    obtain ⟨p,hp,hc⟩ := hn
    apply Finset.prod_eq_zero hp
    apply ite_eq_left
    by_contra no
    exact hc ((pr p hp).coprime_iff_not_dvd.mpr no).symm

/-- The parity factor and all the divisors are precisely the coprimality
conditions at both arithmetic offsets. -/
theorem wheel_at (s : Finset ℕ) (pr : ∀ p∈s,p.Prime) (m h : ℕ) (le : h≤m) :
    diffFree s m h = (if h.Coprime (wheel s) then (1:ℝ) else 0) -
        (if (2*m-h).Coprime (wheel s) then 1 else 0) := by
  have same : Odd (2*m-h) ↔ Odd h := by
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨m-t-1,by omega⟩
    · rintro ⟨t,ht⟩
      exact ⟨m-t-1,by omega⟩
  simp only [wheel,Nat.coprime_mul_iff_right,Nat.coprime_two_right,same,diffFree,free_indicator s _ pr]
  split_ifs <;> norm_num <;> tauto

private theorem reverse_short_sum {m L R : ℕ} (hr : m≤R) (hl : L≤m) (F : ℕ → ℕ → ℝ) :
    ∑ h∈range L, F (m-h) h =
      ∑ a∈range (R+1), if a≤m ∧ m-a<L then F a (m-a) else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun h _ => m-h)
  · intro h hh
    have hlt := mem_range.mp hh
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega⟩
  · intro h hh k hk eqn
    have := mem_range.mp hh
    have := mem_range.mp hk
    omega
  · intro a ha
    obtain ⟨_,l,r⟩ := mem_filter.mp ha
    exact ⟨m-a,mem_range.mpr r,by omega⟩
  · intro h hh
    congr 1
    have := mem_range.mp hh
    omega

/-- Transpose the actual finite matrix to the even residues a=m-h.
Both factors are retained in the row weight. -/
theorem transpose (s : Finset ℕ) (pr : ∀ p∈s,p.Prime) (P L : ℕ) (left : L≤P)
    (w v : ℕ → ℝ) (vo : ∀ m, ¬Odd m → v m=0) :
    (∑ m∈Icc P (2*P), v m*∑ h∈range L,diffFree s m h*w h) =
      ∑ a∈(range (2*P+1)).filter Even, ∑ m∈Icc P (2*P),
        if a≤m ∧ m-a<L then v m*w (m-a)*((if (m-a).Coprime (wheel s) then (1:ℝ) else 0) -
          (if (a+m).Coprime (wheel s) then 1 else 0)) else 0 := by
  classical
  rw [Finset.sum_comm (s := (range (2*P+1)).filter Even)]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases om : Odd m
  · let F := fun a h : ℕ => if Even a then v m*w h*((if h.Coprime (wheel s) then (1:ℝ) else 0) -
      (if (a+m).Coprime (wheel s) then 1 else 0)) else 0
    have ml := (mem_Icc.mp hm).1
    have mu := (mem_Icc.mp hm).2
    have pt (h : ℕ) (hh : h∈range L) : v m*(diffFree s m h*w h) = F (m-h) h := by
      have lt := mem_range.mp hh
      have eqn : m-h+m = 2*m-h := by omega
      by_cases ea : Even (m-h)
      · rw [wheel_at s pr m h (by omega)]
        simp [F,ea,eqn,mul_comm,mul_left_comm,mul_assoc]
      · have eh : ¬Odd h := by
          rintro ⟨j,hj⟩
          obtain ⟨i,hi⟩ := om
          exact ea ⟨i-j,by omega⟩
        simp [diffFree,eh,F,ea]
    rw [Finset.mul_sum,Finset.sum_congr rfl pt,reverse_short_sum mu (left.trans ml),Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [F]; split_ifs <;> rfl
  · simp [vo m om]

end GoldbachSpectral.BandSieve

