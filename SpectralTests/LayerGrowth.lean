module
public import SpectralTests.BandWitness

@[expose] public section
noncomputable section
namespace GoldbachSpectral.BandSieve
open Finset Filter
open scoped Topology

def layerCost (k : ℕ) : ℝ := (2:ℝ)^k*k.factorial

theorem choose_scale (s k : ℕ) (many : 2*k≤s) :
    (s:ℝ)^k ≤ layerCost k*s.choose k := by
  have le : (s:ℝ) ≤ 2*((s+1-k:ℕ):ℝ) := by exact_mod_cast (show s≤2*(s+1-k) by omega)
  have pow := pow_le_pow_left₀ (by positivity) le k
  rw [mul_pow] at pow
  have b := Nat.pow_le_choose (α := ℝ) k s
  have fp : 0<(k.factorial:ℝ) := by positivity
  have z := (div_le_iff₀ fp).mp b
  calc
    _ ≤ _ := pow
    _ ≤ (2:ℝ)^k*((s.choose k:ℝ)*k.factorial) := mul_le_mul_of_nonneg_left z (by positivity)
    _ = _ := by unfold layerCost; ring

/-- Explicit absorption of the lower sieve layers. The band cardinality has to
dominate one logarithm, regardless of the fixed odd depth. -/
theorem absorb (k s P H : ℕ) (D V B : ℝ) (kp : 0<k) (sp : 0<s) (hp : 0<H)
    (dp : 1≤D) (vp : 0≤V) (height : (P:ℝ)=D*H) (many : 2*k≤s)
    (room : 16*((k:ℝ)*2^(k-1)*V)*layerCost k*D*Real.log (2*P) ≤ s)
    (signal : (s.choose k:ℝ)*(H/4:ℝ) - ((k*(s+1)^(k-1):ℕ):ℝ)*V*((P+1:ℝ)*Real.log (2*P)) ≤ (2*P+1:ℝ)*max 0 B) :
    (s:ℝ)^k ≤ (24*layerCost k*D)*B := by
  let J : ℝ := (k:ℝ)*2^(k-1)*V
  have sf : 1≤(s:ℝ) := by exact_mod_cast sp
  have hf : 1≤(H:ℝ) := by exact_mod_cast hp
  have hfpos : 0<(H:ℝ) := by positivity
  have pp : 1≤(P:ℝ) := height ▸ one_le_mul_of_one_le_of_one_le dp hf
  have lg := Real.log_nonneg (show 1≤2*(P:ℝ) by linarith)
  have cp : 0<layerCost k := by unfold layerCost; positivity
  have jp : 0≤J := by dsimp [J]; positivity
  have low : ((k*(s+1)^(k-1):ℕ):ℝ)*V ≤ J*s^(k-1) := by
    push_cast
    have p := pow_le_pow_left₀ (show 0≤(s:ℝ)+1 by positivity) (show (s:ℝ)+1≤2*s by linarith) (k-1)
    rw [mul_pow] at p
    dsimp [J]
    calc
      _ ≤ (k:ℝ)*((2:ℝ)^(k-1)*s^(k-1))*V := by gcongr
      _ = _ := by ring
  have paid := mul_le_mul low (mul_le_mul_of_nonneg_right (show (P:ℝ)+1≤2*(D*H) by linarith) lg)
    (mul_nonneg (by positivity) lg) (mul_nonneg jp (by positivity))
  have fuse := mul_le_mul_of_nonneg_right room (show 0≤(s:ℝ)^(k-1)*(H:ℝ) by positivity)
  have id : (s:ℝ)*s^(k-1)=(s:ℝ)^k := by rw [← pow_succ',Nat.sub_add_cancel kp]
  change 16*J*layerCost k*D*Real.log (2*P)*(s^(k-1)*H) ≤ _ at fuse
  rw [← mul_assoc (s:ℝ) _ _,id] at fuse
  have first := mul_le_mul_of_nonneg_right (choose_scale s k many) (show 0≤(H:ℝ) by positivity)
  have mg := mul_le_mul_of_nonneg_left signal cp.le
  have pay := mul_le_mul_of_nonneg_left paid cp.le
  have net : (s:ℝ)^k*H ≤ 8*layerCost k*(2*P+1)*max 0 B := by
    nlinarith only [first,mg,pay,fuse]
  have positive : 0<B := by
    by_contra! bad
    rw [max_eq_left bad,mul_zero] at net
    exact (not_le_of_gt (mul_pos (pow_pos (by positivity) _) hfpos)) net
  rw [max_eq_right positive.le] at net
  have denom : (2*P+1:ℝ)≤3*(D*H) := by linarith
  have ub := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left denom (by positivity : 0≤8*layerCost k)) positive.le
  apply (mul_le_mul_iff_left₀ hfpos).mp
  exact net.trans (ub.trans_eq (by ring))

end GoldbachSpectral.BandSieve

