module
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section
namespace GoldbachSpectral
open Finset

/-- The constant C₂ and the finite local factors in Li–Liu (1.2).
Factors at indices other than odd primes are one. -/
noncomputable def twinFactor (n : ℕ) : ℝ :=
  if n.Prime ∧ 2 < n then 1 - 1/((n:ℝ)-1)^2 else 1

noncomputable def singular (N : ℕ) : ℝ :=
  2 * (∏' n : ℕ, twinFactor n) *
    ∏ p ∈ N.primeFactors.filter (2 < ·), (((p:ℝ)-1)/((p:ℝ)-2))

theorem twinFactor_unit (n : ℕ) : 0 ≤ twinFactor n ∧ twinFactor n ≤ 1 := by
  unfold twinFactor
  split_ifs with h
  · have hh : 2 < (n:ℝ) := by exact_mod_cast h.2
    constructor
    · have hpos : 0 < ((n:ℝ)-1)^2 := sq_pos_of_pos (by linarith)
      have hle : 1 / ((n:ℝ)-1)^2 ≤ 1 := (div_le_iff₀ hpos).mpr (by nlinarith)
      linarith
    · have := sq_nonneg ((n:ℝ)-1)
      linarith [one_div_nonneg.mpr this]
  · norm_num

/-- Telescoping against all integers, rather than just the odd primes. -/
private theorem range_lower (k : ℕ) :
    ((k:ℝ)+2)/(2*((k:ℝ)+1)) ≤ ∏ n ∈ range (k+3), twinFactor n := by
  induction k with
  | zero => norm_num [Finset.prod_range_succ, twinFactor]
  | succ k ih =>
    rw [show k+1+3 = (k+3)+1 by omega, prod_range_succ]
    have kp : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
    let a : ℝ := (k:ℝ)+2
    have ap : 0 < a := by dsimp [a]; linarith
    have lo : 1-1/a^2 ≤ twinFactor (k+3) := by
      unfold twinFactor
      split_ifs
      · push_cast
        have eqn : (k:ℝ)+3-1 = a := by dsimp [a]; ring
        rw [eqn]
      · linarith [one_div_nonneg.mpr (sq_nonneg a)]
    have first : 0 ≤ ((k:ℝ)+2)/(2*((k:ℝ)+1)) := by positivity
    have factor : 0 ≤ 1-1/a^2 := by
      have h1 : 1 ≤ a^2 := by dsimp [a]; nlinarith [sq_nonneg (k:ℝ)]
      linarith [(div_le_iff₀ (sq_pos_of_pos ap)).mpr (by linarith : (1:ℝ) ≤ 1*a^2)]
    calc
      _ = (((k:ℝ)+2)/(2*((k:ℝ)+1))) * (1-1/a^2) := by
        dsimp [a]
        push_cast
        field_simp
        ring
      _ ≤ _ := mul_le_mul ih lo factor (first.trans ih)
 
theorem twin_convergence :
    Multipliable twinFactor ∧ (1/2:ℝ) ≤ ∏' n, twinFactor n := by
  let F := fun (s : Finset ℕ) => ∏ i ∈ s, twinFactor i
  have anti : Antitone F := Finset.prod_anti_set_of_le_one₀
    (fun n => (twinFactor_unit n).1) (fun n => (twinFactor_unit n).2)
  have lower (s : Finset ℕ) : (1/2:ℝ) ≤ F s := by
    let k := s.sup id
    have inc : s ⊆ range (k+3) := by
      intro n hn
      have hk : n ≤ k := Finset.le_sup (f := id) hn
      exact mem_range.mpr (by omega)
    have hfrac : (1/2:ℝ) ≤ ((k:ℝ)+2)/(2*((k:ℝ)+1)) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    exact hfrac.trans ((range_lower k).trans (anti inc))
  have bd : BddBelow (Set.range F) := ⟨1/2,fun _ ⟨s,hs⟩ => hs ▸ lower s⟩
  have hprod : HasProd twinFactor (⨅ s, F s) := tendsto_atTop_ciInf anti bd
  exact ⟨hprod.multipliable, hprod.tprod_eq ▸ le_ciInf lower⟩

theorem singular_lower (N : ℕ) : 1 ≤ singular N := by
  have hf : 1 ≤ ∏ p ∈ N.primeFactors.filter (2 < ·), (((p:ℝ)-1)/((p:ℝ)-2)) := by
    apply Finset.one_le_prod₀
    intro p hp
    have hh : 2 < (p:ℝ) := by exact_mod_cast (mem_filter.mp hp).2
    rw [le_div_iff₀ (by linarith)]; linarith
  unfold singular
  nlinarith [mul_nonneg (sub_nonneg.mpr twin_convergence.2) (sub_nonneg.mpr hf),
    twin_convergence.2]

private theorem correction_le (F : Finset ℕ) (h : ∀ p ∈ F, 2 < p) :
    (∏ p ∈ F, (((p:ℝ)-1)/((p:ℝ)-2))) ≤ (F.card:ℝ)+1 := by
  induction F using Finset.induction_on_max with
  | empty => simp
  | insert a F ha ih =>
    have ha' : 2 < a := h a (mem_insert_self _ _)
    have haR : 2 < (a:ℝ) := by exact_mod_cast ha'
    have sub : F ⊆ Ico 3 a := fun p hp =>
      mem_Ico.mpr ⟨h p (mem_insert_of_mem hp), ha p hp⟩
    have card := Finset.card_le_card sub
    rw [Nat.card_Ico] at card
    have cr : (F.card:ℝ)+3 ≤ a := by exact_mod_cast (show F.card+3 ≤ a by omega)
    have hm : a ∉ F := fun haF => (ha a haF).false
    rw [prod_insert hm, card_insert_of_notMem hm, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ (((a:ℝ)-1)/((a:ℝ)-2)) * (F.card+1) :=
        mul_le_mul_of_nonneg_left (ih (fun p hp => h p (mem_insert_of_mem hp))) (div_nonneg (by linarith) (by linarith))
      _ ≤ _ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

/-- An elementary logarithmic majorant; this avoids Mertens' theorem. -/
theorem singular_le (N : ℕ) (hN : 0 < N) :
    singular N ≤ 2 * (Real.log N / Real.log 2 + 1) := by
  let F := N.primeFactors.filter (2 < ·)
  have sub : F ⊆ N.primeFactors := Finset.filter_subset _ _
  have hF : ∀ p ∈ F, 2 < p := fun _ hp => (mem_filter.mp hp).2
  have hc : 2^N.primeFactors.card ≤ N :=
    (N.primeFactors.pow_card_le_prod id 2 (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)).trans
      (Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N))
  have hc' : (2:ℝ)^N.primeFactors.card ≤ N := by exact_mod_cast hc
  have hl := Real.log_le_log (by positivity) hc'
  rw [Real.log_pow] at hl
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (F.card:ℝ) ≤ Real.log N / Real.log 2 :=
    (show (F.card:ℝ) ≤ N.primeFactors.card by exact_mod_cast Finset.card_le_card sub).trans
      ((le_div_iff₀ hlog).mpr hl)
  have hprod : (∏' n : ℕ, twinFactor n) ≤ 1 :=
    tprod_le_of_prod_le' le_rfl (fun S => Finset.prod_le_one₀
      (fun n _ => (twinFactor_unit n).1) (fun n _ => (twinFactor_unit n).2))
  have hpos : 0 ≤ ∏ p ∈ F, (((p:ℝ)-1)/((p:ℝ)-2)) := by
    apply Finset.prod_nonneg
    intro p hp
    have : 2 < (p:ℝ) := by exact_mod_cast hF p hp
    exact div_nonneg (by linarith) (by linarith)
  unfold singular
  change 2 * _ * (∏ p ∈ F, _) ≤ _
  calc
    _ ≤ (2*1) * (∏ p ∈ F, (((p:ℝ)-1)/((p:ℝ)-2))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num)) hpos
    _ ≤ _ := by linarith [correction_le F hF]

end GoldbachSpectral

