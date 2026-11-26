module
public import LineProfileInversion
public import LineRemainder

/-! A signed high-frequency criterion for the actual prime-power
correlation on a specified line. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve

private lemma limit_remainder (total : ℕ→ℝ) (band tail : ℝ→ℕ→ℝ) (central : ℝ→ℝ) (target : ℝ)
    (split : ∀ B i,total i=band B i+tail B i)
    (fixed : ∀ B,Tendsto (band B) atTop (𝓝 (central B)))
    (exhaust : Tendsto central atTop (𝓝 target)) :
    Tendsto total atTop (𝓝 target) ↔
      ∀ ε : ℝ, 0<ε → ∀ᶠ B in atTop, ∀ᶠ i in atTop, |tail B i|≤ε := by
  constructor
  · intro h ε ep
    filter_upwards [Metric.tendsto_nhds.mp exhaust (ε/3) (by positivity)] with B e
    filter_upwards [Metric.tendsto_nhds.mp (fixed B) (ε/3) (by positivity),
      Metric.tendsto_nhds.mp h (ε/3) (by positivity)] with i b m
    rw [Real.dist_eq,abs_lt] at e b m
    rw [abs_le]
    have s := split B i
    constructor <;> linarith
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    obtain ⟨B,t,e⟩ := ((h (ε/4) (by positivity)).and
      (Metric.tendsto_nhds.mp exhaust (ε/4) (by positivity))).exists
    filter_upwards [t,Metric.tendsto_nhds.mp (fixed B) (ε/4) (by positivity)] with i ti b
    rw [Real.dist_eq,abs_lt] at e b ⊢
    rw [abs_le] at ti
    have s := split B i
    constructor <;> linarith

theorem profile_band_limit (sign : Bool) (f g : ℝ→ℝ) (hf : FiniteModelWeight f)
    (hg : FiniteModelWeight g) (x : ℝ) :
    Tendsto (fun B : ℝ => ∫ t in -angular B..angular B,frequencyProfile sign (t*x) t f g)
      atTop (𝓝 (2*Real.pi*archimedeanLine sign x f g)) := by
  let F := fun t => frequencyProfile sign (t*x) t f g
  obtain ⟨integ,inv⟩ := profile_inversion sign f g hf hg x
  have lim := intervalIntegral_tendsto_integral integ
    (tendsto_neg_atTop_atBot : Tendsto (fun y : ℝ => -y) atTop atBot)
    (tendsto_id : Tendsto (fun y : ℝ => y) atTop atTop)
  rw [inv] at lim
  apply (lim.const_mul (2*Real.pi)).congr
  intro B
  simpa only [angular,mul_neg,smul_eq_mul,F,id_eq] using
    (intervalIntegral.smul_integral_comp_mul_left (a := -B) (b := B) F (2*Real.pi))

namespace LineSequence

/-- The iterated tail limit is equivalent to the sharp individual-line
asymptotic. Both factors in the count carry the original Mangoldt weights. -/
theorem exact_line_iff_tail (D : LineSequence) (sign : Bool) (f g : ℝ→ℝ)
    (hf : FiniteModelWeight f) (hg : FiniteModelWeight g) (x : ℝ)
    (hx : Tendsto D.ordinate atTop (𝓝 x)) :
    Tendsto (D.exactMass sign f g) atTop (𝓝 (archimedeanLine sign x f g)) ↔
      ∀ ε : ℝ, 0<ε → ∀ᶠ B : ℝ in atTop, ∀ᶠ i in atTop,
        |D.tailIntegral sign f g (angular B) i|≤ε := by
  let c := 2*Real.pi
  have cn : c≠0 := (mul_pos (by norm_num) Real.pi_pos).ne'
  let v := archimedeanLine sign x f g
  let s := D.siftedMass sign f g
  let u := D.exactMass sign f g
  have close : Tendsto (fun i => u i-s i) atTop (𝓝 0) := D.exact_sifted_limit sign f g hf hg
  have bridge : Tendsto u atTop (𝓝 v) ↔ Tendsto (fun i => c*s i) atTop (𝓝 (c*v)) := by
    constructor
    · intro h
      have h' : Tendsto (fun i => u i-(u i-s i)) atTop (𝓝 (v-0)) := h.sub close
      have hs : Tendsto s atTop (𝓝 v) := by simpa only [sub_sub_cancel,sub_zero] using h'
      exact hs.const_mul c
    · intro h
      have hs : Tendsto s atTop (𝓝 v) := by
        simpa only [← mul_assoc,inv_mul_cancel₀ cn,one_mul] using h.const_mul c⁻¹
      simpa only [sub_add_cancel,zero_add] using close.add hs
  exact bridge.trans (limit_remainder _ _ _ _ _ (fun B i => D.exact_band_identity sign f g (angular B) i)
    (fun B => D.compact_band f g hf hg sign (-angular B) (angular B) x hx)
    (profile_band_limit sign f g hf hg x))

#print axioms exact_line_iff_tail
end LineSequence
end GoldbachSpectral435.GoldbachSieve
