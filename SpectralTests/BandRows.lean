module
public import SpectralTests.Lattice
public import SpectralTests.BandPrimes

@[expose] public section
namespace GoldbachSpectral.BandSieve
open Finset

private theorem odd_divisor_class {d h : ℤ} (odd : Odd d) :
    Odd h ∧ d ∣ h ↔ h ≡ d [ZMOD 2*d] := by
  rw [Int.modEq_iff_dvd]
  constructor
  · rintro ⟨ho,j,rfl⟩
    obtain ⟨k,hk⟩ := (Int.odd_mul.mp ho).2
    exact ⟨-k,by rw [hk]; ring⟩
  · rintro ⟨k,hk⟩
    have e : h=d*(2*(-k)+1) := by linarith only [hk,show d*(2*(-k)+1)=d-2*d*k by ring]
    rw [e]
    exact ⟨odd.mul ⟨-k,rfl⟩,dvd_mul_right _ _⟩

theorem opposite_class {d : ℤ} (odd : Odd d) (m h : ℤ) :
    Odd h ∧ d ∣ (2*m-h) ↔ h ≡ 2*m-d [ZMOD 2*d] := by
  have parity : Odd h ↔ Odd (2*m-h) := by
    constructor
    · rintro ⟨j,hj⟩; exact ⟨m-j-1,by omega⟩
    · rintro ⟨j,hj⟩; exact ⟨m-j-1,by omega⟩
  rw [parity,odd_divisor_class odd,Int.modEq_iff_dvd,Int.modEq_iff_dvd]
  rw [show d-(2*m-h) = -(2*m-d-h) by ring,dvd_neg]

/-- The O(1) rounding error in one pair of lower-layer divisor counts.
The moving endpoints and parity restrictions are both included. -/
theorem odd_class_discrepancy {d : ℤ} (hd : 0 < d) (od : Odd d) (m A B : ℤ) (le : A ≤ B) :
    |(((Ioc A B).filter (fun h => Odd h ∧ d ∣ h)).card:ℤ) -
      (((Ioc A B).filter (fun h => Odd h ∧ d ∣ 2*m-h)).card:ℤ)| ≤ 2 := by
  simp only [odd_divisor_class od,opposite_class od]
  exact residue_discrepancy (by positivity : 0 < 2*d) d (2*m-d) A B le

private theorem card_prefix (k : ℕ) (S : ℤ → Prop) [DecidablePred S] :
    ((range k).filter (fun i : ℕ => S i)).card =
      ((Ioc (-1:ℤ) ((k:ℤ)-1)).filter S).card := by
  have matchSets : (((range k).filter (fun i : ℕ => S i)).map Nat.castEmbedding) =
      ((Ioc (-1:ℤ) ((k:ℤ)-1)).filter S) := by
    ext i
    simp only [mem_map,mem_filter,mem_range,mem_Ioc,Nat.castEmbedding_apply]
    constructor
    · rintro ⟨n,⟨hn,ps⟩,rfl⟩
      exact ⟨⟨by omega,by omega⟩,ps⟩
    · rintro ⟨⟨i0,ik⟩,ps⟩
      lift i to ℕ using (by omega)
      exact ⟨i,⟨by omega,ps⟩,rfl⟩
  rw [← matchSets,Finset.card_map]

/-- The weighted lower-layer bound including the parity test. The last
term is the variation of the sampled smooth test. -/
theorem rounded_weight {d : ℤ} (hd : 0 < d) (odd : Odd d) (m : ℤ) (n : ℕ) (w : ℕ → ℝ) :
    |∑ i ∈ range n,
      ((if Odd (i:ℤ) ∧ d ∣ (i:ℤ) then (1:ℝ) else 0) -
       (if Odd (i:ℤ) ∧ d ∣ 2*m-(i:ℤ) then (1:ℝ) else 0))*w i| ≤
      2*(|w n|+∑ i ∈ range n, |w i-w (i+1)|) := by
  apply weighted_discrepancy
  intro k _
  let U := fun i : ℤ => Odd i ∧ d ∣ i
  let V := fun i : ℤ => Odd i ∧ d ∣ 2*m-i
  have eq (S : ℤ → Prop) [DecidablePred S] :
      (∑ i ∈ range k, if S (i:ℤ) then (1:ℝ) else 0) =
        (((Ioc (-1:ℤ) ((k:ℤ)-1)).filter S).card:ℝ) := by
    simpa only [Finset.sum_boole] using congrArg (Nat.cast : ℕ → ℝ) (card_prefix k S)
  change |∑ i ∈ range k, ((if U i then (1:ℝ) else 0) - (if V i then (1:ℝ) else 0))| ≤ 2
  rw [sum_sub_distrib,eq U,eq V]
  exact_mod_cast odd_class_discrepancy hd odd m (-1) (k-1) (by omega)

/-- The odd multiple closest to the centre of the broad interval is within
one divisor of that centre, uniformly for every product from the band. -/
theorem odd_multiple_near (d A : ℕ) (hd : 0 < d) (odd : Odd d) :
    ∃ t : ℕ, Odd t ∧ d ∣ t ∧ A ≤ t+d ∧ t ≤ A+d := by
  let j := A/(2*d)
  have rem := Nat.mod_add_div A (2*d)
  have lt := Nat.mod_lt A (show 0<2*d by omega)
  refine ⟨d*(2*j+1),odd.mul ⟨j,rfl⟩,dvd_mul_right _ _,?_,?_⟩ <;>
    dsimp [j] <;> nlinarith only [rem,lt,Nat.zero_le (A%(2*d))]

/-- Geometry of the positive layer, with all endpoints integral and no
rounding assumptions at the ends of the prime-counting interval. -/
theorem positive_layer_geometry {H P d m t : ℕ} (hp : 32*H ≤ P) (hd : 32*d ≤ P)
    (l : 3*P ≤ t+d) (u : t ≤ 3*P+d) (lower : t+2*H ≤ 2*m) (upper : 2*m ≤ t+3*H)
    (od : Odd t) (om : Odd m) :
    let h := 2*m-t
    let a := t-m
    2*H ≤ h ∧ h ≤ 3*H ∧ Odd h ∧ Even a ∧ P ≤ a ∧ 4*a ≤ 7*P ∧
      P ≤ m ∧ m ≤ 2*P ∧ m=a+h ∧ 2*m-h=t := by
  obtain ⟨i,oi⟩ := od
  obtain ⟨j,oj⟩ := om
  dsimp
  refine ⟨by omega,by omega,⟨2*j-i,by omega⟩,⟨i-j,by omega⟩,?_⟩
  omega

end GoldbachSpectral.BandSieve

