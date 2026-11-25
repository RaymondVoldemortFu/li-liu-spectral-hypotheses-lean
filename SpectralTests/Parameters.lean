module
public import SpectralTests.LayerGrowth

@[expose] public section
noncomputable section
namespace GoldbachSpectral.BandSieve
open Finset Filter
open scoped Topology

/-- Polynomial arguments inside logarithms cost less than t at infinity. -/
theorem log_polynomial (A : ℝ) (ap : 0<A) (d : ℕ) :
    ∀ᶠ t : ℕ in atTop, Real.log (A*(t:ℝ)^d) ≤ t := by
  let e := 1/(2*((d:ℝ)+1))
  have ep : 0<e := by dsimp [e]; positivity
  have asym := ((Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).bound ep)
  filter_upwards [asym, eventually_ge_atTop (1:ℕ),
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2*Real.log A))] with t small one big
  have tp : 0<(t:ℝ) := by exact_mod_cast one
  have lg : 0≤Real.log (t:ℝ) := Real.log_nonneg (by exact_mod_cast one)
  change ‖Real.log (t:ℝ)‖≤e*‖(t:ℝ)‖ at small
  rw [Real.norm_eq_abs,abs_of_nonneg lg,Real.norm_eq_abs,abs_of_pos tp] at small
  rw [Real.log_mul ap.ne' (pow_pos tp _).ne',Real.log_pow]
  have scaled := mul_le_mul_of_nonneg_left small (Nat.cast_nonneg d)
  have de : (d:ℝ)*e≤1/2 := by
    dsimp [e]; rw [mul_one_div,div_le_iff₀ (by positivity)]; linarith
  have side := mul_le_mul_of_nonneg_right de tp.le
  linarith only [big,scaled,side,show (d:ℝ)*(e*t)=d*e*t by ring]

def amplification (k : ℕ) := 32*16^k
def sieveHeight (t k : ℕ) := t^(4*k)
def sieveBand (t : ℕ) := 8*t^4

theorem band_grows : ∀ᶠ t : ℕ in atTop, t^3 ≤ (bandPrimes (sieveBand t)).card := by
  obtain ⟨Z,pop⟩ := band_population
  filter_upwards [eventually_ge_atTop (max Z 2), log_polynomial 16 (by norm_num) 4] with t far small
  have t1 : 1≤t := by omega
  have tp : 0<(t:ℝ) := by exact_mod_cast t1
  have pow : t≤t^4 := Nat.le_self_pow (by decide) _
  let z := sieveBand t
  have p := pop z (by dsimp [z,sieveBand]; omega)
  have idn : 2*(z:ℝ)=16*(t:ℝ)^4 := by dsimp [z,sieveBand]; push_cast; ring
  rw [idn] at p
  have h := p.trans (mul_le_mul_of_nonneg_left small (Nat.cast_nonneg _))
  have rz : (z:ℝ)=8*(t:ℝ)^4 := by dsimp [z,sieveBand]; push_cast; ring
  rw [rz] at h
  have rr : (t:ℝ)^3*t ≤ ((bandPrimes z).card:ℝ)*t := by nlinarith only [h,pow_nonneg tp.le 4]
  exact_mod_cast (mul_le_mul_iff_left₀ tp).mp rr

theorem band_product (t k : ℕ) (T : Finset ℕ) (h : T∈(bandPrimes (sieveBand t)).powersetCard k) :
    32*(∏ p∈T,p) ≤ amplification k*sieveHeight t k := by
  obtain ⟨sub,card⟩ := mem_powersetCard.mp h
  have b := Finset.prod_le_prod (s := T) (fun p hp => (mem_band.mp (sub hp)).2.2)
  rw [Finset.prod_const,card] at b
  apply (Nat.mul_le_mul_left 32 b).trans_eq
  dsimp [sieveBand,amplification,sieveHeight]
  rw [← Nat.mul_assoc 2 8 _,mul_pow,← pow_mul]
  ring

/-- A cofinal family of even residue rows. For each fixed odd k, the
signed reduced-class bias grows at least as t^(3k). -/
theorem growing_rows (k : ℕ) (od : Odd k) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ t : ℕ in atTop,
      let H := sieveHeight t k
      let P := amplification k*H
      ∃ a≤2*P, Even a ∧ (t:ℝ)^(3*k) ≤ C*row (wheel (bandPrimes (sieveBand t))) a H P := by
  have kp : 0<k := by obtain ⟨u,hu⟩ := od; omega
  let D := amplification k
  have dn : 32≤D := by
    have p := (show 1≤16^k from Nat.one_le_pow k 16 (by decide))
    dsimp [D,amplification]; omega
  have dp : 0<(D:ℝ) := by exact_mod_cast (show 0<D by omega)
  obtain ⟨X,V,vp,rows⟩ := row_signal (1/(D:ℝ)) (by positivity)
  let A := 16*((k:ℝ)*2^(k-1)*V)*layerCost k*D
  have cost : 0<layerCost k := by unfold layerCost; positivity
  have ap : 0≤A := by dsimp [A]; positivity
  refine ⟨24*layerCost k*D,by positivity,?_⟩
  filter_upwards [band_grows, eventually_ge_atTop (max (4*D+1) (2*k)),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (max X A),
    log_polynomial (2*(D:ℝ)) (by positivity) (4*k)] with t pop far big logB
  let H := sieveHeight t k
  let P := D*H
  let z := sieveBand t
  let s := bandPrimes z
  have tp : 0<t := by omega
  have hp : 0<H := pow_pos tp _
  have tH : t≤H := Nat.le_self_pow (by omega : 4*k≠0) _
  have ht3 : t≤t^3 := Nat.le_self_pow (by decide) _
  have ht4 : t≤t^4 := Nat.le_self_pow (by decide) _
  have sp : 0<s.card := tp.trans_le (ht3.trans pop)
  have hP : H≤P := Nat.le_mul_of_pos_left H (by omega)
  have height : (P:ℝ)=(D:ℝ)*H := by dsimp [P]; push_cast; rfl
  have wide : 32*H≤P := Nat.mul_le_mul_right H dn
  have zpow : z^k=8^k*H := by dsimp [z,sieveBand,H,sieveHeight]; rw [mul_pow,← pow_mul]
  have big8 : 8≤8^k := Nat.le_self_pow kp.ne' _
  have slab : 4*H+1≤z^k := by rw [zpow]; have := Nat.mul_le_mul_right H big8; omega
  have top : 4*P<z^(k+1) := by
    have comp : 4*D<z := by dsimp [z,sieveBand]; omega
    have l := Nat.mul_lt_mul_of_pos_right comp hp
    have b : H≤z^k := by omega
    rw [pow_succ]
    dsimp [P]
    calc
      _ = (4*D)*H := by ring
      _ < z*H := l
      _ ≤ z^k*z := (Nat.mul_le_mul_left z b).trans_eq (Nat.mul_comm ..)
  have hs : X≤(P:ℝ) := (le_max_left X A).trans (big.trans (by exact_mod_cast tH.trans hP))
  have hratio : 1/(D:ℝ)*P≤H := by rw [height]; exact le_of_eq (by field_simp)
  have p4 : 4≤P := by omega
  obtain ⟨a,ar,ev,sig⟩ := rows s z k H P hs p4 hp (by dsimp [z,sieveBand]; omega) od
    (fun p h => (mem_band.mp h).1) (fun p h => (mem_band.mp h).2.1) slab (by omega) top wide hratio
    (fun b hb => band_product t k b hb)
  have idp : 2*(P:ℝ)=(2*(D:ℝ))*t^(4*k) := by rw [height]; dsimp [H,sieveHeight]; push_cast; ring
  rw [← idp] at logB
  have rt : 1≤(t:ℝ) := by exact_mod_cast tp
  have at' : A≤(t:ℝ) := (le_max_right X A).trans big
  have room : A*Real.log (2*P)≤s.card := by
    have h₁ := mul_le_mul_of_nonneg_left logB ap
    have h₂ := mul_le_mul_of_nonneg_right at' (zero_le_one.trans rt)
    have h₃ : (t:ℝ)^3 ≤ s.card := by exact_mod_cast pop
    apply h₁.trans (h₂.trans ?_)
    exact (by nlinarith [mul_nonneg (by positivity : 0≤(t:ℝ)^2) (sub_nonneg.mpr rt)] : (t:ℝ)*t≤t^3).trans h₃
  have res := absorb k s.card P H D V (row (wheel s) a H P) kp sp hp (by exact_mod_cast (show 1≤D by omega))
    vp.le height (((le_max_right _ _).trans far).trans (ht3.trans pop)) room sig
  refine ⟨a,ar,ev,?_⟩
  apply le_trans _ res
  rw [pow_mul]
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast pop) k

end GoldbachSpectral.BandSieve

