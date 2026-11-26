module
public import SiftedPeriods

/-! A uniform arithmetic realization of the exact local factors on both
types of affine line in the finite spectral criterion. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset Filter
namespace GoldbachSpectral435.GoldbachSieve
open GoldbachSpectral PhysicalTests
open MathlibNt.SieveTheory.MertensTheorem (primeProduct)

private def atTwo (p : ℕ) : ℝ := if p=2 then 2 else 1
private def atDivisor (H p : ℕ) : ℝ := if 2<p ∧ p∣H then primeCorrection p else 1

private lemma local_factor (H p : ℕ) (ev : Even H) (pp : p.Prime) :
    1-localDensity H p=(1-1/(p:ℝ))^2*(atTwo p*twinFactor p*atDivisor H p) := by
  by_cases two : p=2
  · subst p
    norm_num [localDensity,atTwo,twinFactor,atDivisor,even_iff_two_dvd.mp ev]
  have more : 2<p := by have := pp.two_le; omega
  have pr : (2:ℝ)<p := by exact_mod_cast more
  have nz : (p:ℝ)≠0 := by linarith
  have o : (p:ℝ)-1≠0 := by linarith
  have t : (p:ℝ)-2≠0 := by linarith
  by_cases d : p∣H <;> simp [localDensity,atTwo,atDivisor,twinFactor,primeCorrection,two,more,pp,d] <;>
    field_simp <;> ring

theorem density_identity (H z : ℕ) (hp : 0<H) (ev : Even H) (zz : 2≤z) :
    survivingDensity H z=(primeProduct z)^2*truncatedSeries H z := by
  classical
  let P := smallPrimes z
  have two : 2∈P := mem_filter.mpr ⟨mem_range.mpr (by omega),Nat.prime_two⟩
  have tw : (∏ p∈P, atTwo p)=2 := by simp [atTwo,prod_ite_eq',two]
  have same : P.filter (fun p => 2<p ∧ p∣H)=H.primeFactors.filter (fun p => 2<p ∧ p≤z) := by
    ext p
    simp only [P,smallPrimes,mem_filter,mem_range,Nat.mem_primeFactors]
    grind
  have factors : (∏ p∈P,atDivisor H p)=∏ p∈H.primeFactors.filter (fun p => 2<p ∧ p≤z),primeCorrection p := by
    unfold atDivisor
    rw [← prod_filter,same]
  have twin : (∏ p∈P,twinFactor p)=∏ n∈range (z+1),twinFactor n := by
    apply prod_subset (filter_subset ..)
    intro n hn outside
    have no : ¬n.Prime := fun q => outside (mem_filter.mpr ⟨hn,q⟩)
    simp [twinFactor,no]
  have one : (∏ p∈P,(1-1/(p:ℝ)))=primeProduct z := rfl
  unfold survivingDensity
  change (∏ p∈P, _)=_
  have atP (p : ℕ) (h : p∈P) := local_factor H p ev (mem_filter.mp h).2
  rw [prod_congr rfl atP,prod_mul_distrib,
    prod_mul_distrib,prod_mul_distrib,prod_pow,one,tw,twin,factors,truncatedSeries]

private lemma reciprocal_period (z : ℕ) :
    (1:ℝ)/(primorial z)≤primeProduct z := by
  let P := smallPrimes z
  have e : (∏ p∈P,(1/(p:ℝ)))=1/(primorial z:ℝ) := by
    rw [prod_div_distrib,prod_const_one,← Nat.cast_prod]
    rfl
  rw [← e]
  change _≤∏ p∈P,(1-1/(p:ℝ))
  apply prod_le_prod₀ (fun p _ => by positivity)
  intro p h
  have q := (mem_filter.mp h).2
  have pr : (2:ℝ)≤p := by exact_mod_cast q.two_le
  rw [le_sub_iff_add_le,← add_div,div_le_one (by linarith)]
  linarith

private lemma density_lower (H z : ℕ) (ev : Even H) :
    (1:ℝ)/(primorial z)≤survivingDensity H z := by
  let P := smallPrimes z
  have e : (∏ p∈P,(1/(p:ℝ)))=1/(primorial z:ℝ) := by
    rw [prod_div_distrib,prod_const_one,← Nat.cast_prod]
    rfl
  rw [← e]
  apply prod_le_prod₀ (fun p _ => by positivity)
  intro p h
  have pp : p.Prime := (mem_filter.mp h).2
  have pr : (2:ℝ)≤p := by exact_mod_cast pp.two_le
  have nz : 0<(p:ℝ) := by linarith
  unfold localDensity
  split_ifs with d
  · rw [le_sub_iff_add_le,← add_div,div_le_one nz]
    linarith
  · have ne : p≠2 := by rintro rfl; exact d (even_iff_two_dvd.mp ev)
    have t : (3:ℝ)≤p := by exact_mod_cast (show 3≤p by have := pp.two_le; omega)
    rw [le_sub_iff_add_le,← add_div,div_le_one nz]
    linarith

def roughCount (H z A Y : ℕ) := intervalCount (allowed H (primorial z)) A Y

/-- Normalization by the square of the one-prime density approximates
the original series simultaneously on every translated interval. -/
theorem rough_horizon (ε : ℝ) (ep : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ H : ℕ, 0<H → Even H → H≤2*scale N*N → ∀ A Y : ℕ,
    |(roughCount H (localCutoff N) A Y:ℝ)/(primeProduct (localCutoff N))^2-
      Y*singularSeries H|≤Real.sqrt N+ε*Y*singularSeries H := by
  filter_upwards [all_horizon_factors ε ep,cutoff_grows.eventually_ge_atTop 2] with N cap zz
  intro H hp ev hh A Y
  let z := localCutoff N
  let Q : ℝ := primorial z
  let W := primeProduct z
  let S := singularSeries H
  let T := truncatedSeries H z
  let C : ℝ := roughCount H z A Y
  have qp : 0<Q := Nat.cast_pos.mpr (primorial_pos z)
  have wb : 1/Q≤W := reciprocal_period z
  have wp : 0<W := (one_div_pos.mpr qp).trans_le wb
  have wq : 1≤Q*W := by simpa only [mul_comm] using (div_le_iff₀ qp).mp wb
  have wq2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) wq 2
  have qbound : Q/W^2≤Q^3 := (div_le_iff₀ (pow_pos wp _)).mpr (by
    calc Q = Q*1^2 := by ring
         _ ≤ Q*(Q*W)^2 := mul_le_mul_of_nonneg_left wq2 qp.le
         _ = _ := by ring)
  have disc : |C-Y*(W^2*T)|≤Q := by
    dsimp only [C,Q,W,T,roughCount]
    rw [← density_identity H z hp ev zz]
    exact sifted_interval H z A Y
  have weighted : |C/W^2-Y*T|≤Real.sqrt N := by
    calc
      _ = |C-Y*(W^2*T)|/W^2 := by
        rw [show C/W^2-Y*T=(C-Y*(W^2*T))/W^2 by field_simp,abs_div,abs_of_nonneg (sq_nonneg W)]
      _ ≤ Q/W^2 := div_le_div_of_nonneg_right disc (sq_nonneg _)
      _ ≤ _ := qbound.trans cap.1
  have sp : 0<S := singularSeries_pos H
  have near : |T/S-1|≤ε := cap.2 H hp hh
  have err : |T-S|≤ε*S := by
    rwa [show T/S-1=(T-S)/S by field_simp,abs_div,abs_of_pos sp,div_le_iff₀ sp] at near
  change |C/W^2-Y*S|≤_
  calc
    _ = |(C/W^2-Y*T)+(Y:ℝ)*(T-S)| := by congr 1; ring
    _ ≤ |C/W^2-Y*T|+(Y:ℝ)*|T-S| := by
      simpa only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) Y)] using abs_add_le (C/W^2-Y*T) ((Y:ℝ)*(T-S))
    _ ≤ _ := by nlinarith only [weighted,mul_le_mul_of_nonneg_left err (Nat.cast_nonneg (α:=ℝ) Y)]

/-- With the exact normalization there is no relative bias even when many
lines are summed. The discrepancy is independent of the length and offset. -/
theorem exact_rough_error (H z A Y : ℕ) (ev : Even H) :
    |(roughCount H z A Y:ℝ)*(singularSeries H/survivingDensity H z)-Y*singularSeries H| ≤
      (primorial z:ℝ)^2*singularSeries H := by
  let Q : ℝ := primorial z
  let V := survivingDensity H z
  let S := singularSeries H
  let C : ℝ := roughCount H z A Y
  have qp : 0<Q := Nat.cast_pos.mpr (primorial_pos z)
  have b : 1/Q≤V := density_lower H z ev
  have vp := (one_div_pos.mpr qp).trans_le b
  have sp := singularSeries_pos H
  have iv : 1/V≤Q := (div_le_iff₀ vp).mpr (by simpa only [mul_comm] using (div_le_iff₀ qp).mp b)
  have err : |C-Y*V|≤Q := sifted_interval H z A Y
  change |C*(S/V)-Y*S|≤Q^2*S
  calc
    _ = |C-Y*V| * (S*(1/V)) := by
      rw [show C*(S/V)-Y*S=(C-Y*V)*(S*(1/V)) by field_simp,abs_mul,
        abs_of_nonneg (mul_nonneg sp.le (one_div_pos.mpr vp).le)]
    _ ≤ Q*(S*Q) := mul_le_mul err (mul_le_mul_of_nonneg_left iv sp.le) (by positivity) qp.le
    _ = _ := by ring

#print axioms rough_horizon
#print axioms exact_rough_error
end GoldbachSpectral435.GoldbachSieve
