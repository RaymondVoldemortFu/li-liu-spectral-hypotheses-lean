module
public import SpectralTests.BandRows

@[expose] public section
namespace GoldbachSpectral.BandSieve
open Finset

private noncomputable def lowHit (d m h : ℕ) : ℝ :=
  (if Odd h ∧ d ∣ h then 1 else 0) - (if Odd h ∧ d ∣ 2*m-h then 1 else 0)
noncomputable def plusHit (d m h : ℕ) : ℝ := if Odd h ∧ d ∣ 2*m-h then 1 else 0
noncomputable def diffFree (s : Finset ℕ) (m h : ℕ) : ℝ :=
  if Odd h then (free s h:ℝ) - (free s (2*m-h):ℝ) else 0

private theorem split_at (s : Finset ℕ) (k m h z : ℕ) (hz : 1≤z) (odd : Odd k)
    (prime : ∀ p∈s,p.Prime) (band : ∀ p∈s,z≤p)
    (small : h<z^k) (low : h<2*m) (high : 2*m<z^(k+1)) :
    diffFree s m h =
      (∑ t ∈ s.powerset.filter (fun t => t.card<k), (-1:ℝ)^t.card*lowHit (∏ p∈t,p) m h) +
      ∑ t ∈ s.powersetCard k, plusHit (∏ p∈t,p) m h := by
  classical
  rw [Finset.sum_filter,Finset.powersetCard_eq_filter,Finset.sum_filter]
  by_cases oh : Odd h
  · have hp : 0<h := by obtain ⟨j,hj⟩ := oh; omega
    have eqn := congrArg (Int.cast : ℤ → ℝ) (extra_layer hz odd prime band hp small (by omega : 0<2*m-h) (by omega : 2*m-h<z^(k+1)))
    unfold below hit at eqn
    push_cast at eqn
    simpa [diffFree,oh,lowHit,plusHit] using eqn
  · simp [diffFree,lowHit,plusHit,oh]

private theorem low_round (d m L : ℕ) (hd : 0<d) (od : Odd d) (left : L≤2*m) (w : ℕ → ℝ) :
    |∑ h ∈ range L, lowHit d m h*w h| ≤ 2*(|w L|+∑ h ∈ range L, |w h-w (h+1)|) := by
  have od' : Odd (d:ℤ) := by exact_mod_cast od
  have bound := rounded_weight (by exact_mod_cast hd : (0:ℤ)<d) od' (m:ℤ) L w
  suffices eqn : (∑ h ∈ range L, lowHit d m h*w h) =
     ∑ h ∈ range L, ((if Odd (h:ℤ) ∧ (d:ℤ) ∣ (h:ℤ) then (1:ℝ) else 0) -
       (if Odd (h:ℤ) ∧ (d:ℤ) ∣ 2*(m:ℤ)-(h:ℤ) then 1 else 0))*w h by
    rw [eqn]; exact bound
  apply Finset.sum_congr rfl
  intro h hh
  have le : h ≤ 2*m := (Finset.mem_range.mp hh).le.trans left
  have odd' : Odd (h:ℤ) ↔ Odd h := by exact_mod_cast Iff.rfl
  have cast' : ((2*m-h:ℕ):ℤ) = 2*(m:ℤ)-(h:ℤ) := by push_cast [le]; rfl
  simp only [← cast',odd',Int.natCast_dvd_natCast,lowHit]

/-- One full weighted column of the sieve matrix, before summing over
the von Mangoldt weights. Each lower subset is charged only once. -/
theorem signed_column (s : Finset ℕ) (z k L m : ℕ) (w : ℕ → ℝ)
    (hz : 2≤z) (odd : Odd k) (prime : ∀ p∈s,p.Prime) (band : ∀ p∈s,z<p)
    (small : L≤z^k) (left : L≤2*m) (high : 2*m<z^(k+1)) :
    (∑ t ∈ s.powersetCard k, ∑ h ∈ range L, plusHit (∏ p∈t,p) m h*w h) -
        ((s.powerset.filter (fun t => t.card<k)).card:ℝ)*
          (2*(|w L|+∑ h ∈ range L, |w h-w (h+1)|)) ≤
      ∑ h ∈ range L, diffFree s m h*w h := by
  classical
  let V := 2*(|w L|+∑ h ∈ range L, |w h-w (h+1)|)
  let S := s.powerset.filter (fun t => t.card<k)
  let A := fun (t : Finset ℕ) h => (-1:ℝ)^t.card*lowHit (∏ p∈t,p) m h*w h
  let B := fun (t : Finset ℕ) h => plusHit (∏ p∈t,p) m h*w h
  have identity (h : ℕ) (hh : h ∈ range L) : diffFree s m h*w h =
      (∑ t ∈ S,A t h) + ∑ t ∈ s.powersetCard k,B t h := by
    have bounds := Finset.mem_range.mp hh
    rw [split_at s k m h z (by omega) odd prime (fun p hp => (band p hp).le) (by omega) (by omega) high,
      add_mul,Finset.sum_mul,Finset.sum_mul]
  rw [Finset.sum_congr rfl identity,Finset.sum_add_distrib,Finset.sum_comm (s := range L) (t := S),
    Finset.sum_comm (s := range L) (t := s.powersetCard k)]
  have each (t : Finset ℕ) (ht : t ∈ S) : -V ≤ ∑ h ∈ range L, A t h := by
    have sub := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have od : Odd (∏ p∈t,p) := by
      apply Finset.prod_induction (fun p : ℕ => p) (fun n : ℕ => Odd n) (fun _ _ h g => h.mul g) (by decide)
      intro p hp
      exact (prime p (sub hp)).odd_of_ne_two (by have := band p (sub hp); omega)
    have hd : 0 < ∏ p∈t,p := Finset.prod_pos (fun p hp => (prime p (sub hp)).pos)
    have r := low_round (∏ p∈t,p) m L hd od left w
    have eqn : (∑ h ∈ range L, A t h) = (-1:ℝ)^t.card * ∑ h ∈ range L, lowHit (∏ p∈t,p) m h*w h := by
      simp [A,Finset.mul_sum,mul_assoc]
    have absbd : |∑ h ∈ range L, A t h| ≤ V := by rw [eqn,abs_mul,abs_pow]; simpa [V] using r
    exact (abs_le.mp absbd).1
  have total := Finset.sum_le_sum each
  simp only [Finset.sum_const,nsmul_eq_mul,mul_neg] at total
  change _ - (S.card:ℝ)*V ≤ (∑ t ∈ S,∑ h ∈ range L,A t h) + ∑ t ∈ s.powersetCard k,∑ h ∈ range L,B t h
  dsimp only [B]
  linarith only [total]

end GoldbachSpectral.BandSieve

