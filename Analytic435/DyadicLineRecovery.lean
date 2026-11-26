module
public import PairLineTransforms
public import NearLineLimit

/-! Recovering the individual prime line from the known, coarser
congruence by the signed differences of its two lifts. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset Filter
namespace GoldbachSpectral435.GoldbachSieve

def lineContrast (q M L : ℕ) (H : ℤ) (sign : Bool) (a b : ℕ→ℝ) :=
  lineSum (2*q) M L H sign a b-lineSum (2*q) M L (H+q) sign a b

theorem dyadic_line_identity (q M L : ℕ) (qp : 0<q) (r : ℕ) (H : ℤ) (sign : Bool) (a b : ℕ→ℝ) :
    (2:ℝ)^r*lineSum (2^r*q) M L H sign a b=
      lineSum q M L H sign a b+∑ i∈range r,(2:ℝ)^i*lineContrast (2^i*q) M L H sign a b := by
  induction r with
  | zero => simp
  | succ r ih =>
    let u : ℕ := 2^r*q
    have up : 0<u := Nat.mul_pos (by positivity) qp
    have eq : (2:ℕ)^(r+1)*q=2*u := by dsimp [u]; rw [pow_succ]; ring
    have s := split_line u M L up H sign a b
    rw [Finset.sum_range_succ (fun i => (2:ℝ)^i*lineContrast (2^i*q) M L H sign a b) r,← add_assoc,← ih,eq,pow_succ]
    change 2^r*2*lineSum (2*u) M L H sign a b=
      2^r*lineSum u M L H sign a b+2^r*(lineSum (2*u) M L H sign a b-lineSum (2*u) M L (H+u) sign a b)
    rw [s]
    ring

/-- The base and top moduli are independent of H and of the weights.
There are at most log₂(12 log⁸ M) doublings. -/
theorem recovery_moduli : ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, N≤M → ∃ j r : ℕ,
    let q := liftedModulus (localCutoff N) j
    let L := Real.log (M:ℝ)
    (q:ℝ)*L^8≤M ∧ (M:ℝ)<2*q*L^8 ∧ (2:ℝ)^r≤12*L^8 ∧ 3*M<2^r*q := by
  have growth := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨K,k⟩ := eventually_atTop.mp (growth.eventually_ge_atTop 1)
  filter_upwards [near_line_modulus,eventually_ge_atTop K] with N near nk
  intro M nm
  obtain ⟨j,lo,hi⟩ := near M nm
  let q := liftedModulus (localCutoff N) j
  let L := Real.log (M:ℝ)
  have l1 : 1≤L := k M (nk.trans nm)
  have qp : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have large : 1≤6*L^8 := by linarith only [one_le_pow₀ l1 (n:=8)]
  obtain ⟨b,low,up⟩ := exists_nat_pow_near large (by norm_num : (1:ℝ)<2)
  refine ⟨j,b+1,lo,hi,?_,?_⟩
  · rw [pow_succ]
    linarith only [low]
  · have e : (3:ℝ)*M<2^(b+1)*q := by
      change (M:ℝ)<2*q*L^8 at hi
      linarith only [hi,mul_lt_mul_of_pos_right up qp]
    exact_mod_cast e

/-- An identity on a single, specified line for arbitrary real weights,
with the true two-variable prime congruence at the initial modulus. -/
theorem prime_line_recovery {q M H : ℕ} [NeZero q] (r : ℕ) (hh : H≤2*M) (cap : 3*M<2^r*q)
    (sign : Bool) (f g : ℝ→ℝ) :
    let a := siftedWeight q M f
    let b := siftedWeight q M g
    (2:ℝ)^r*exactLine M M H sign a b=
      classPairs q H M M sign f g+∑ i∈range r,(2:ℝ)^i*lineContrast (2^i*q) M M H sign a b := by
  intro a b
  have bound (n : ℕ) (hn : n<M) (m : ℕ) (hm : m<M) :
      |lineCoordinate sign n m-(H:ℤ)|<((2^r*q:ℕ):ℤ) := by
    have t : (3:ℤ)*M<((2^r*q:ℕ):ℤ) := by exact_mod_cast cap
    cases sign <;> simp only [lineCoordinate,ite_false,ite_true,Bool.false_eq_true,abs_lt] <;> omega
  rw [class_pairs_lines,← exact_line_recovery H sign a b bound]
  exact dyadic_line_identity q M M (NeZero.pos q) r H sign a b

#print axioms prime_line_recovery
#print axioms recovery_moduli
end GoldbachSpectral435.GoldbachSieve
