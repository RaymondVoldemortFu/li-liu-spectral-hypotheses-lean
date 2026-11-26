module
public import PrimePairProjection

/-! Powers of two times an even primorial have exactly the same local
sieve factors after normalization. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset
namespace GoldbachSpectral435.GoldbachSieve
open MathlibNt.SieveTheory.MertensTheorem (primeProduct)

def liftedModulus (z j : ℕ) := 2^j*primorial z

instance liftedNeZero (z j : ℕ) : NeZero (liftedModulus z j) :=
  ⟨(Nat.mul_pos (by positivity) (primorial_pos z)).ne'⟩

private lemma cop_lift {z j n : ℕ} (zz : 2≤z) :
    n.Coprime (liftedModulus z j) ↔ n.Coprime (primorial z) := by
  rw [liftedModulus,Nat.coprime_mul_iff_right]
  exact ⟨And.right,fun h => ⟨(h.coprime_dvd_right (Nat.prime_two.dvd_primorial_iff.mpr zz)).pow_right j,h⟩⟩

theorem lifted_principal {z : ℕ} (zz : 2≤z) (j M : ℕ) (f : ℝ→ℝ) :
    principalMass (liftedModulus z j) M f=principalMass (primorial z) M f := by
  classical simp only [principalMass,cop_lift zz]

theorem lifted_totient {z : ℕ} (zz : 2≤z) (j : ℕ) :
    (liftedModulus z j).totient=2^j*(primorial z).totient := by
  induction j with
  | zero => simp [liftedModulus]
  | succ j ih =>
    have e : liftedModulus z (j+1)=2*liftedModulus z j := by simp [liftedModulus,pow_succ]; ring
    have dvd : 2∣liftedModulus z j := dvd_mul_of_dvd_right (Nat.prime_two.dvd_primorial_iff.mpr zz) _
    rw [e,Nat.totient_mul_of_prime_of_dvd Nat.prime_two dvd,ih,pow_succ]
    ring

theorem lifted_allowed {z : ℕ} (zz : 2≤z) (j H : ℕ) :
    (allowed H (liftedModulus z j)).card=2^j*(allowed H (primorial z)).card := by
  classical
  let q := liftedModulus z j
  let Q := primorial z
  let r := ZMod.castHom (show Q∣q from dvd_mul_left ..) (ZMod Q)
  have unit (x : ZMod q) : IsUnit x ↔ IsUnit (r x) := by
    obtain ⟨n,hn⟩ : ∃ n : ℕ,(n:ZMod q)=x := ⟨x.val,ZMod.natCast_zmod_val x⟩
    rw [← hn,map_natCast,ZMod.isUnit_iff_coprime,ZMod.isUnit_iff_coprime]
    exact cop_lift zz
  have compat (n : ℕ) : (n:ZMod q)∈allowed H q ↔ (n:ZMod Q)∈allowed H Q := by
    rw [mem_allowed,mem_allowed,unit,map_mul,map_sub,map_natCast,map_natCast]
  have periods : intervalCount (allowed H q) 0 q=intervalCount (allowed H Q) 0 q := by
    unfold intervalCount
    simp only [Nat.zero_add]
    congr 1
    exact filter_congr (fun n _ => compat n)
  have single := interval_multiples (allowed H q) 0 1
  rw [one_mul,one_mul] at single
  exact single.symm.trans (periods.trans (interval_multiples (allowed H Q) 0 (2^j)))

/-- The factor converting the product of the two principal-character
means to pair density is unchanged at every lift. -/
theorem lifted_density {z H : ℕ} (zz : 2≤z) (hp : 0<H) (ev : Even H) (j : ℕ) :
    let q := liftedModulus z j
    (q:ℝ)*(allowed H q).card/(q.totient:ℝ)^2=truncatedSeries H z := by
  intro q
  have phi := primorial_totient z
  have card := allowed_count H z
  rw [density_identity H z hp ev zz] at card
  have fp : 0<((primorial z).totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (primorial_pos z)
  have qp : 0<(primorial z:ℝ) := Nat.cast_pos.mpr (primorial_pos z)
  have wp : 0<primeProduct z := pos_of_mul_pos_right (phi ▸ fp) qp.le
  dsimp only [q]
  rw [lifted_totient zz,lifted_allowed zz,liftedModulus]
  push_cast
  rw [phi,card]
  field_simp

#print axioms lifted_density
end GoldbachSpectral435.GoldbachSieve
