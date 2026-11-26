module
public import CompactFrequencyBand
public import PrimeLineSifting

/-! Exact decomposition of the unrestricted Mangoldt correlation on a
given line into a compact frequency band, its complement, and the cost
of the unit conditions. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Finset MeasureTheory
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve.LineSequence

def bandwidth (D : LineSequence) (i : ℕ) : ℝ := Real.pi*D.length i/D.modulus i

def exactMass (D : LineSequence) (sign : Bool) (f g : ℝ→ℝ) (i : ℕ) :=
  exactLine (D.length i) (D.length i) (D.shift i) sign (fun n => weightedMangoldt (D.length i) n f)
    (fun n => weightedMangoldt (D.length i) n g)/((D.length i:ℝ)*singularSeries (D.shift i))

def siftedMassAt (D : LineSequence) (q : ℕ) (sign : Bool) (f g : ℝ→ℝ) (i : ℕ) :=
  exactLine (D.length i) (D.length i) (D.shift i) sign (siftedWeight q (D.length i) f)
    (siftedWeight q (D.length i) g)/((D.length i:ℝ)*singularSeries (D.shift i))

def siftedMass (D : LineSequence) (sign : Bool) (f g : ℝ→ℝ) (i : ℕ) :=
  D.siftedMassAt (D.modulus i) sign f g i

def tailIntegral (D : LineSequence) (sign : Bool) (f g : ℝ→ℝ) (B : ℝ) (i : ℕ) :=
  (∫ t in -(D.bandwidth i)..(-B),D.integrand sign f g i t)+
  (∫ t in B..D.bandwidth i,D.integrand sign f g i t)

theorem exact_band_identity (D : LineSequence) (sign : Bool) (f g : ℝ→ℝ) (B : ℝ) (i : ℕ) :
    2*Real.pi*D.siftedMass sign f g i=
      (∫ t in -B..B,D.integrand sign f g i t)+D.tailIntegral sign f g B i := by
  let M := D.length i
  let q := D.modulus i
  have qp : 0<q := NeZero.pos _
  have mp : 0<M := qp.trans_le (D.modulus_le i)
  have qr : (q:ℝ)≠0 := Nat.cast_ne_zero.mpr qp.ne'
  have mr : (M:ℝ)≠0 := Nat.cast_ne_zero.mpr mp.ne'
  have sp := (singularSeries_pos (D.shift i)).ne'
  have ct : Continuous (D.integrand sign f g i) := continuous_const.mul (continuous_frequencySlice ..)
  have intg (a b : ℝ) := ct.intervalIntegrable (μ:=volume) a b
  rw [tailIntegral,add_left_comm,← add_assoc,intervalIntegral.integral_add_adjacent_intervals (intg ..) (intg ..),
    intervalIntegral.integral_add_adjacent_intervals (intg ..) (intg ..)]
  unfold integrand
  rw [intervalIntegral.integral_const_mul]
  change _=D.normalization i*(∫ t in -(Real.pi*M/q)..(Real.pi*M/q),frequencySlice q M _ _ _ _ t)
  rw [frequency_recovers_line q M qp mp]
  unfold siftedMass siftedMassAt normalization
  dsimp only [M,q] at qr mr ⊢
  field_simp [qr,mr,sp]

private lemma log_exponent {M : ℕ} (mp : 0<M) : (Nat.log 2 M:ℝ)*Real.log 2≤Real.log M := by
  have first := Nat.pow_log_le_self 2 mp.ne'
  have e := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^Nat.log 2 M)
    (by exact_mod_cast first : (2:ℝ)^Nat.log 2 M≤M)
  rwa [Real.log_pow] at e

theorem sifting_limit_at (D : LineSequence) (Q : ℕ→ℕ) (positive : ∀ i, 0<Q i)
    (bound : ∀ i,Q i≤D.length i) (sign : Bool) (f g : ℝ→ℝ)
    (hf : FiniteModelWeight f) (hg : FiniteModelWeight g) :
    Tendsto (fun i => D.exactMass sign f g i-D.siftedMassAt (Q i) sign f g i) atTop (𝓝 0) := by
  obtain ⟨F,fb⟩ := hf.norm_bounded
  obtain ⟨G,gb⟩ := hg.norm_bounded
  have bp (x : ℝ) : |f x|≤F := by simpa only [Complex.norm_real,Real.norm_eq_abs] using fb x
  have gp (x : ℝ) : |g x|≤G := by simpa only [Complex.norm_real,Real.norm_eq_abs] using gb x
  have fp := (abs_nonneg _).trans (bp 0)
  have gp' := (abs_nonneg _).trans (gp 0)
  let C := 2*F*G/Real.log 2
  have l2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have growth : Tendsto D.length atTop atTop := tendsto_atTop_mono D.base_le D.growing
  have rate := (isLittleO_log_rpow_rpow_atTop 3 (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero.comp
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp growth)
  have lim : Tendsto (fun i => C*((Real.log (D.length i:ℝ))^3/D.length i)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.rpow_one,mul_zero] using rate.const_mul C
  apply squeeze_zero_norm' _ lim
  filter_upwards with i
  let M := D.length i
  let q := Q i
  have qp : 0<q := positive i
  have mp : 0<M := qp.trans_le (bound i)
  have mr : 0<(M:ℝ) := Nat.cast_pos.mpr mp
  let L := Real.log (M:ℝ)
  have lp : 0≤L := Real.log_nonneg (Nat.one_le_cast.mpr mp)
  have qlog := Real.log_le_log (Nat.cast_pos.mpr qp) (Nat.cast_le.mpr (bound i))
  have powlog := log_exponent mp
  have j : (Nat.log 2 M:ℝ)≤L/Real.log 2 := (le_div_iff₀ l2).mpr powlog
  have s := (singularSeries_gt_one (D.shift i)).le
  have z := exact_line_sifting q M qp mp (D.shift i) sign f g F G fp gp' (fun n _ => bp _) (fun n _ => gp _)
  rw [Real.norm_eq_abs,exactMass,siftedMassAt,← sub_div,abs_div,abs_of_pos (mul_pos mr (singularSeries_pos _))]
  apply (div_le_div_of_nonneg_right z (mul_nonneg mr.le (singularSeries_pos _).le)).trans
  have pay : 2*F*G*L*(Nat.log 2 M:ℝ)*Real.log q≤C*L^3 := calc
    _ ≤ 2*F*G*L*(Nat.log 2 M:ℝ)*L := mul_le_mul_of_nonneg_left qlog (by positivity)
    _ ≤ 2*F*G*L*(L/Real.log 2)*L := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left j (by positivity)) lp
    _ = _ := by dsimp only [C]; ring
  have w := div_le_div_of_nonneg_left (show 0≤C*L^3 by dsimp [C]; positivity) mr
    (le_mul_of_one_le_right mr.le s)
  exact (div_le_div_of_nonneg_right pay (mul_nonneg mr.le (singularSeries_pos _).le)).trans
    (w.trans_eq (by ring))

theorem exact_sifted_limit (D : LineSequence) (sign : Bool) (f g : ℝ→ℝ)
    (hf : FiniteModelWeight f) (hg : FiniteModelWeight g) :
    Tendsto (fun i => D.exactMass sign f g i-D.siftedMass sign f g i) atTop (𝓝 0) :=
  D.sifting_limit_at D.modulus (fun i => NeZero.pos (D.modulus i)) D.modulus_le sign f g hf hg

#print axioms exact_band_identity
#print axioms exact_sifted_limit
end GoldbachSpectral435.GoldbachSieve.LineSequence
