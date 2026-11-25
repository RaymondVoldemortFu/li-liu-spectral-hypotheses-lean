module
public import SpectralTests.BandMatrix

@[expose] public section
namespace GoldbachSpectral.BandSieve
open Finset Chebyshev

/-- A product of k band primes contributes a positive prime-mass interval
uniformly in the product. The relative length H/P is fixed before P grows. -/
theorem top_divisor_mass (ρ : ℝ) (rp : 0<ρ) :
    ∃ X : ℝ, ∀ P H L d : ℕ, X ≤ P → 32*H≤P → ρ*P≤H → 3*H<L → 0<d → 32*d≤P → Odd d →
      ∀ w v : ℕ → ℝ, (∀ i, 0≤w i) → (∀ m, 0≤v m) →
        (∀ i, 2*H ≤ i → i ≤ 3*H → 1≤w i) →
        (∀ m, m.Prime → 7*P≤5*m → 5*m≤8*P → Real.log m≤v m) →
      (H:ℝ)/4 ≤ ∑ m ∈ Icc P (2*P), v m * ∑ h ∈ range L, plusHit d m h*w h := by
  obtain ⟨X,hX⟩ := prime_mass_windows (c := ρ/2) (C := 2) (by positivity) (by norm_num)
  refine ⟨max X 4,?_⟩
  intro P H L d hp hP frac hL dp dsmall dOdd w v wp vp plateau prime
  obtain ⟨t,od,dvd,low,high⟩ := odd_multiple_near d (3*P) dp dOdd
  let a : ℝ := ((t:ℝ)+2*H)/2
  let b : ℝ := ((t:ℝ)+3*H)/2
  have pn : 4 ≤ P := by exact_mod_cast (le_trans (le_max_right X 4) hp)
  have ar : (P:ℝ)≤a := by
    dsimp [a]
    have la : 2*(P:ℝ)≤t+2*H := by exact_mod_cast (by omega : 2*P≤t+2*H)
    linarith
  have ab : a ≤ b := by dsimp [a,b]; linarith [Nat.cast_nonneg (α := ℝ) H]
  have br : b≤2*P := by
    change ((t:ℝ)+3*H)/2 ≤ 2*P
    have eq : (t:ℝ)+3*H≤4*P := by exact_mod_cast (by omega : t+3*H≤4*P)
    linarith
  have mass := hX P ((le_max_left X 4).trans hp) a b ar ab br (by dsimp [a,b]; linarith)
  have sdiff : Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊b⌋₊ := by
    intro p hh
    obtain ⟨half,prime'⟩ := Nat.mem_primesLE.mp hh
    exact Nat.mem_primesLE.mpr ⟨half.trans (Nat.floor_mono ab),prime'⟩
  let I := Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊
  have massI : (H:ℝ)/4 ≤ ∑ m ∈ I, Real.log m := by
    have diff : ∑ m ∈ I, Real.log m = theta b-theta a := by
      rw [theta_eq_sum_primesLE,theta_eq_sum_primesLE,eq_sub_iff_add_eq]
      exact Finset.sum_sdiff sdiff
    rw [diff]
    dsimp only [a,b] at mass
    linarith
  have info {m : ℕ} (hm : m∈I) : m.Prime ∧ t+2*H≤2*m ∧ 2*m≤t+3*H := by
    obtain ⟨hb,ha⟩ := Finset.mem_sdiff.mp hm
    obtain ⟨ub,pm⟩ := Nat.mem_primesLE.mp hb
    have lb : ⌊a⌋₊ < m := lt_of_not_ge (fun h => ha (Nat.mem_primesLE.mpr ⟨h,pm⟩))
    have above : a < (m:ℝ) := (Nat.floor_lt (by linarith [ar, Nat.cast_nonneg (α := ℝ) P])).mp lb
    have below : (m:ℝ) ≤ b := (Nat.le_floor_iff (by linarith [ar,ab,Nat.cast_nonneg (α := ℝ) P])).mp ub
    dsimp [a] at above
    dsimp [b] at below
    exact ⟨pm,by exact_mod_cast (by linarith : (t:ℝ)+2*H≤2*m),by exact_mod_cast (by linarith : 2*(m:ℝ)≤t+3*H)⟩
  have region {m : ℕ} (hm : m∈I) : 7*P≤5*m ∧ 5*m≤8*P := by
    obtain ⟨_,a1,a2⟩ := info hm
    omega
  have contained : I ⊆ Icc P (2*P) := by
    intro m hm
    have ⟨_,l,r⟩ := info hm
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have plus_non (m h : ℕ) : 0≤plusHit d m h*w h := by
    unfold plusHit
    split <;> simp [wp]
  apply massI.trans
  apply (Finset.sum_le_sum (g := fun m => v m * ∑ h ∈ range L, plusHit d m h*w h) ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg contained (fun m _ _ => mul_nonneg (vp _) (Finset.sum_nonneg (fun h _ => plus_non m h))))
  intro m hm
  obtain ⟨pm,ml,mu⟩ := info hm
  have reg := region hm
  have mo := pm.odd_of_ne_two (by omega)
  obtain ⟨hl,hu,ho,_,_,_,_,_,_,eid⟩ := positive_layer_geometry hP dsmall low high ml mu od mo
  let j := 2*m-t
  have hit : plusHit d m j = 1 := by
    unfold plusHit
    exact ite_eq_left ⟨ho,eid.symm ▸ dvd⟩
  have htop : 1 ≤ ∑ h ∈ range L, plusHit d m h*w h := by
    apply le_trans _ (Finset.single_le_sum (fun h _ => plus_non m h) (show j ∈ range L from mem_range.mpr (by dsimp [j]; omega)))
    rw [hit,one_mul]
    exact plateau j hl hu
  exact (prime m pm reg.1 reg.2).trans (le_mul_of_one_le_right (vp m) htop)

theorem lower_layer_card (s : Finset ℕ) (k : ℕ) :
    (s.powerset.filter (fun t => t.card<k)).card ≤ k*(s.card+1)^(k-1) := by
  classical
  have sub : s.powerset.filter (fun t => t.card<k) ⊆ (range k).biUnion (fun j => s.powersetCard j) := by
    intro t ht
    obtain ⟨h,hk⟩ := mem_filter.mp ht
    exact mem_biUnion.mpr ⟨t.card,mem_range.mpr hk,mem_powersetCard.mpr ⟨mem_powerset.mp h,rfl⟩⟩
  apply (card_le_card sub).trans (card_biUnion_le.trans ?_)
  calc
    _ ≤ ∑ _ ∈ range k,(s.card+1)^(k-1) := by
      apply sum_le_sum
      intro j hj
      rw [card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (by omega : s.card≤s.card+1) _).trans
        (Nat.pow_le_pow_right (by omega) (by have := mem_range.mp hj; omega)))
    _ = _ := by simp

/-- Sum the complete inclusion-exclusion formula over the prime-weighted
columns and pay the rounding errors for every subset smaller than k. -/
theorem signed_matrix_lower (ρ : ℝ) (rp : 0<ρ) :
    ∃ X : ℝ, ∀ (s : Finset ℕ) (z k H L P : ℕ) (w v : ℕ → ℝ),
      X≤P → 2≤z → Odd k → (∀ p∈s,p.Prime) → (∀ p∈s,z<p) →
      L≤z^k → L≤P → 4*P<z^(k+1) → 32*H≤P → ρ*P≤H → 3*H<L →
      (∀ t∈s.powersetCard k, 32*(∏ p∈t,p)≤P) →
      (∀ i,0≤w i) → (∀ m,0≤v m) → (∀ i, 2*H ≤ i → i ≤ 3*H → 1≤w i) →
      (∀ m, m.Prime → 7*P≤5*m → 5*m≤8*P → Real.log m≤v m) →
      ((s.card.choose k:ℕ):ℝ)*(H/4:ℝ) -
        ((k*(s.card+1)^(k-1):ℕ):ℝ)*(2*(|w L|+∑ h∈range L, |w h-w (h+1)|))*(∑ m∈Icc P (2*P),v m)
        ≤ ∑ m∈Icc P (2*P), v m*(∑ h ∈ range L,diffFree s m h*w h) := by
  obtain ⟨X,pos⟩ := top_divisor_mass ρ rp
  refine ⟨X,?_⟩
  intro s z k H L P w v x hz od pr band sl left top hr ratio span dmax wp vp flat vprime
  let V := 2*(|w L|+∑ h∈range L, |w h-w (h+1)|)
  let T := s.powersetCard k
  let C := Icc P (2*P)
  let B := fun (m : ℕ) (t : Finset ℕ) => ∑ h ∈ range L,plusHit (∏ p∈t,p) m h*w h
  let e : ℝ := ((s.powerset.filter (fun t=>t.card<k)).card:ℝ)*V
  have high (t : Finset ℕ) (ht : t∈T) : (H:ℝ)/4 ≤ ∑ m∈C,v m*B m t := by
    have sub := (mem_powersetCard.mp ht).1
    have dpos := Finset.prod_pos (s := t) (f := id) (fun p hp => (pr p (sub hp)).pos)
    have dOdd : Odd (∏ p∈t,p) := Finset.prod_induction id Odd (fun _ _ a b => a.mul b) (by decide)
      (fun p hp => (pr p (sub hp)).odd_of_ne_two (by have := band p (sub hp); omega))
    exact pos P H L (∏ p∈t,p) x hr ratio span dpos (dmax t ht) dOdd w v wp vp flat vprime
  have mass := Finset.sum_le_sum high
  simp only [Finset.sum_const,nsmul_eq_mul] at mass
  rw [Finset.sum_comm] at mass
  have row (m : ℕ) (hm : m∈C) : v m*((∑ t∈T,B m t)-e) ≤ v m*(∑ h∈range L,diffFree s m h*w h) := by
    obtain ⟨ml,mu⟩ := mem_Icc.mp hm
    exact mul_le_mul_of_nonneg_left (signed_column s z k L m w hz od pr band sl (by omega) (by omega)) (vp m)
  have all := Finset.sum_le_sum row
  have paid : ∑ m∈C,v m*((∑ t∈T,B m t)-e) = (∑ m∈C,∑ t∈T,v m*B m t)-e*∑ m∈C,v m := by
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    simp_rw [mul_comm (v _) e]
  rw [paid] at all
  have nn : 0≤V := by dsimp [V]; positivity
  have vv : 0 ≤ ∑ m∈C,v m := sum_nonneg (fun m _ => vp m)
  have comp : e ≤ ((k*(s.card+1)^(k-1):ℕ):ℝ)*V :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast lower_layer_card s k) nn
  have ecomp := mul_le_mul_of_nonneg_right comp vv
  have tc : T.card=s.card.choose k := card_powersetCard _ _
  rw [tc] at mass
  exact (sub_le_sub mass ecomp).trans all

end GoldbachSpectral.BandSieve

