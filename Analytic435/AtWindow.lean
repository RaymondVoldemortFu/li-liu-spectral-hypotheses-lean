module
public import ModulusWitness
public import SpectralTests.WindowSize

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral GoldbachSpectral.BandSieve Finset Filter
open scoped Topology
namespace GoldbachSpectral435

theorem error_absorbed {r M q P : ℕ} (C D : ℝ) (cp : 0<C) (dp : 0<D)
    (hr : 640≤r) (size : M=r^64) (qp : 0<q) (qcap : q≤r) (pp : 0<P) (pcap : P≤r)
    (cc : C≤r) (dc : D≤r) (logs : Real.log (2*M)≤r) :
    2*meanError C D q M P*((P+1:ℝ)*Real.log (2*P)) ≤ (M:ℝ)/(32*q) := by
  have hp : 1≤(r:ℝ) := by exact_mod_cast (show 1≤r by omega)
  have pr : 0<(P:ℝ) := by exact_mod_cast pp
  have qr : 0<(q:ℝ) := by exact_mod_cast qp
  have rc : (q:ℝ)≤r := by exact_mod_cast qcap
  have pc : (P:ℝ)≤r := by exact_mod_cast pcap
  have sz : (M:ℝ)=(r:ℝ)^64 := by exact_mod_cast size
  have mono (i j : ℕ) (le : i≤j) : (r:ℝ)^i≤(r:ℝ)^j := pow_le_pow_right₀ hp le
  have Mbig : r≤M := size ▸ Nat.le_self_pow (by decide) _
  have mp : 0<(M:ℝ) := by exact_mod_cast pp.trans_le (pcap.trans Mbig)
  have root : Real.sqrt (M:ℝ)=(r:ℝ)^32 := by
    rw [Real.sqrt_eq_rpow,sz,← Real.rpow_natCast_mul (by positivity)]; norm_num
  have fourth : (M:ℝ)^(1/4:ℝ)=(r:ℝ)^16 := by
    rw [sz,← Real.rpow_natCast_mul (by positivity)]; norm_num
  have lb := Real.log_nonneg (show 1≤(M:ℝ) by exact_mod_cast (pp.trans_le (pcap.trans Mbig)))
  have lm := (Real.log_le_log mp (by linarith : (M:ℝ)≤2*M)).trans logs
  have lp : Real.log (2*(P:ℝ))≤r := (Real.log_le_log (mul_pos (by norm_num : (0:ℝ)<2) pr)
    (by exact_mod_cast (show 2*P≤2*M by omega) : 2*(P:ℝ)≤2*M)).trans logs
  have l2 := Real.log_nonneg (show 1≤2*(P:ℝ) by exact_mod_cast (show 1≤2*P by omega))
  have lM2 : 0≤Real.log (2*(M:ℝ)) := lb.trans (Real.log_le_log mp (by linarith))
  have e : meanError C D q M P ≤ 5*(r:ℝ)^51 := by
    unfold meanError
    rw [root,fourth]
    calc
      _ ≤ (r:ℝ)^32*(r*r^16*r^2)+2*r^32*r+r*(2*r)*r := by gcongr
      _ = (r:ℝ)^51+2*r^33+2*r^3 := by ring
      _ ≤ _ := by linarith only [mono 33 51 (by decide),mono 3 51 (by decide)]
  have el : 0≤meanError C D q M P := by
    have l := Real.log_nonneg (show 1≤2*(M:ℝ) by linarith [show (1:ℝ)≤M by exact_mod_cast (pp.trans_le (pcap.trans Mbig))])
    unfold meanError; positivity
  apply (le_div_iff₀ (by positivity)).mpr
  rw [sz]
  calc
    _ ≤ 2*(5*(r:ℝ)^51)*((2*r)*r)*(32*r) := by gcongr; linarith
    _ = 640*(r:ℝ)^54 := by ring
    _ ≤ (r:ℝ)*(r:ℝ)^54 := mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (by positivity)
    _ = (r:ℝ)^55 := by ring
    _ ≤ _ := mono 55 64 (by decide)

/-- The dyadic sieve bias survives as an actual opposite-shift sum at a
large even target. The progression modulus used in the average is independent
of the large target on which the operator will be tested. -/
theorem large_shift (global : ∀ n, GRH n) (k : ℕ) (odd : Odd k) :
    ∃ L : ℝ, 0<L ∧ ∀ᶠ t : ℕ in atTop,
      let H := sieveHeight t k
      let P := amplification k*H
      ∃ N<window t, Even N ∧ window t<4*N ∧ ∃ b : ℝ → ℝ,
        ShiftTest N (3*H) P b ∧ (t:ℝ)^(3*k) ≤ L*oppositeSum N b := by
  obtain ⟨C,D,cp,dp,avg⟩ := mean_lower
  obtain ⟨V,vp,tests⟩ := row_tests
  obtain ⟨A,ap,rows⟩ := growing_rows k odd
  obtain ⟨K,principal⟩ := principal_lower
  have kp : 0<k := by obtain ⟨j,hj⟩ := odd; omega
  have root_inf : Tendsto windowRoot atTop atTop := tendsto_atTop.mpr (fun j =>
    (eventually_ge_atTop j).mono (fun t ht => ht.trans (large_root t)))
  have log_bound := root_inf.eventually (log_polynomial 2 (by norm_num) 64)
  refine ⟨A*128*V,by positivity,?_⟩
  filter_upwards [rows,band_grows,wheel_small,polynomial_le_root (amplification k) (4*k),log_bound,
    eventually_ge_atTop (max 640 K),(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (max (max C D) A)]
    with t row' many small Psmall logs far constants
  let r := windowRoot t
  let M := window t
  let H := sieveHeight t k
  let P := amplification k*H
  let q := wheel (bandPrimes (sieveBand t))
  have tr := large_root t
  have high : 640≤r := (le_max_left _ _).trans (far.trans tr)
  have tp : 0<t := by omega
  have rp : 0<r := by omega
  have pp : 0<P := Nat.mul_pos (by dsimp [amplification]; positivity) (pow_pos tp _)
  have smallq : q≤r := small
  have smallp : P≤r := Psmall
  have rm : r^2≤M := Nat.pow_le_pow_right rp (by decide : 2≤64)
  have cap : 81*r≤M := by
    have b := Nat.mul_le_mul_right r (by omega : 81≤r)
    exact b.trans (by simpa only [pow_two] using rm)
  have mp : 0<M := by omega
  have mq : q≤M := by omega
  have cut : 8*P≤M := by omega
  have qp := wheel_four (by omega : 1≤t) many
  change 4≤q at qp
  let : NeZero q := ⟨by omega⟩
  have Tle : (t:ℝ)≤r := by exact_mod_cast tr
  have err := error_absorbed C D cp dp high (rfl : M=r^64) (by omega : 0<q) smallq pp smallp
    (((le_max_left C D).trans (le_max_left _ _)).trans (constants.trans Tle))
    (((le_max_right C D).trans (le_max_left _ _)).trans (constants.trans Tle)) (by simpa [M,window,r] using logs)
  obtain ⟨a,_,ae,large⟩ := row'
  let B := row q a H P
  change (t:ℝ)^(3*k)≤A*B at large
  have tt : t≤t^(3*k) := Nat.le_self_pow (by omega) _
  have big : 1≤B := by
    have one : A≤(t:ℝ) := (le_max_right _ _).trans constants
    have lim : (t:ℝ)≤(t:ℝ)^(3*k) := by exact_mod_cast tt
    apply (mul_le_mul_iff_right₀ ap).mp
    simpa only [mul_one] using one.trans (lim.trans large)
  have pr := principal M (by omega) q (by omega) (by omega)
  have qpos : 0<(q:ℝ) := by exact_mod_cast (show 0<q by omega)
  have mpos : 0<(M:ℝ) := by exact_mod_cast mp
  have U : (M:ℝ)/(16*q)≤principalMass q M broad/q.totient := by
    rw [← div_div]
    exact (div_le_div_of_nonneg_right pr qpos.le).trans
      (div_le_div_of_nonneg_left (by linarith : 0≤principalMass q M broad)
        (by exact_mod_cast NeZero.pos q.totient) (by exact_mod_cast Nat.totient_le q))
  have sig := avg q qp (global q) M H P a mp (by omega) pp cut
  have bu := mul_le_mul_of_nonneg_right U (zero_le_one.trans big)
  have pn : 0<(M:ℝ)/q := div_pos mpos qpos
  have micro : (2*(M:ℝ)/q)*(B/128)<rowMean q M P H a := by
    apply lt_of_lt_of_le _ sig
    have e := sub_le_sub bu err
    apply lt_of_lt_of_le _ e
    have g := mul_le_mul_of_nonneg_left big pn.le
    calc
      _ = ((M:ℝ)/q)*B/64 := by ring
      _ < ((M:ℝ)/q)*B/16-((M:ℝ)/q)/32 := by nlinarith only [g,pn]
      _ = _ := by ring
  have eq : Even q := ⟨∏ p∈bandPrimes (sieveBand t),p,by dsimp [q,wheel]; ring⟩
  obtain ⟨N,nM,ne,low,bias⟩ := modulus_witness M q P H a (by omega) mq eq ae (B/128) (by positivity) micro
  let b := fun x : ℝ => shape a H P x/V
  have len : 3*H≤P := by
    have v : 1≤16^k := Nat.one_le_pow k 16 (by decide)
    have l : 3≤amplification k := by dsimp [amplification]; omega
    exact (Nat.mul_le_mul_right H l)
  have ht := tests N a H P (by exact_mod_cast (show 1≤H from pow_pos tp _))
    (by exact_mod_cast len) ((lt_div_iff₀ (by norm_num)).mpr (by exact_mod_cast (show P*20<N by omega)))
  refine ⟨N,nM,ne,low,b,ht,?_⟩
  rw [show oppositeSum N b=bandObservable P H a N/V from band_to_test pp (by omega) V]
  apply large.trans
  have rat := (div_lt_iff₀ (by norm_num : (0:ℝ)<128)).mp bias
  have factor := mul_le_mul_of_nonneg_left rat.le ap.le
  exact factor.trans_eq (by field_simp)

#print axioms large_shift
end GoldbachSpectral435

