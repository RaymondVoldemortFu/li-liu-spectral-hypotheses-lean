module
public import ConditionalGoldbach.Proofs.DictionaryApplication
public import ConditionalGoldbach.Proofs.SpectralQuantitative
public import ConditionalGoldbach.Proofs.Asymptotics

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach
namespace GoldbachSpectral435

/-- A total scalar sequence for the norm on the moduli covered by the
spectral hypotheses. No assertion of GRH is made by this definition. -/
def eligibleNorm (N : ℕ) : ℝ := by
  classical
  exact if e : N ≠ 0 ∧ alpha N < beta ∧ GRH N then
    @norm _ _ (@residualOperator (alpha N) e.2.1 N ⟨e.1⟩) else 0

theorem eligibleNorm_spec (N : ℕ) [NeZero N] (ha : alpha N < beta) (g : GRH N) :
    eligibleNorm N = ‖residualOperator ha N‖ := by
  simp [eligibleNorm, NeZero.ne N, ha, g]

theorem eligibleNorm_nonneg (N : ℕ) : 0 ≤ eligibleNorm N := by
  unfold eligibleNorm
  split <;> positivity

/-- With the paper's exact operator and its original quantifiers, some
admissible exclusion strip exists exactly when the normalized norm tends
to zero on GRH-eligible even moduli. -/
theorem some_actual_S_iff :
    (∃ h, HypothesisS h) ↔ ∀ ε : ℝ, 0 < ε →
      EvenEventually (fun N => eligibleNorm N ≤ ε * singularSeries N) := by
  classical
  let U : ℕ → ℝ := fun N => Real.log (N:ℝ)
  obtain ⟨up,ug,uw⟩ := isAdmissible_log
  constructor
  · rintro ⟨h,⟨hp,hi,hw⟩,hs⟩ ε epos
    obtain ⟨K,H⟩ := ((hi (1/ε)).and (hw.and (hs.and evenEventually_large)))
    refine ⟨K,fun N hn he => ?_⟩
    obtain ⟨hg,cap,test,large⟩ := H N hn he
    obtain ⟨n4,logp,ha⟩ := large_parameters large
    have nr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    let : NeZero N := ⟨by omega⟩
    have s := singularSeries_pos N
    have hpos := hp N he n4
    by_cases g : GRH N
    · rw [eligibleNorm_spec N ha g]
      have wp : 0 < zeroFreeWidth N h := by unfold zeroFreeWidth; positivity
      have bd := ((theorem_6_1 N he large g ha).2.1 _ wp (by linarith)).mp (test g inferInstance ha)
      apply (bd.trans (spectralScale_div_sqrt_width_le N h nr s logp hpos cap)).trans
      apply (div_le_iff₀ hpos).mpr
      have p := mul_le_mul_of_nonneg_right ((div_le_iff₀ epos).mp hg) s.le
      linarith only [p, show h N*ε*singularSeries N = ε*singularSeries N*h N by ring]
    · simp [eligibleNorm,g,mul_nonneg epos.le s.le]
  · intro dec
    let h := fun N => if 0 < eligibleNorm N then min (U N) (singularSeries N/(2*eligibleNorm N)) else U N
    have pos (N : ℕ) (he : Even N) (hn : 4 ≤ N) : 0 < h N := by
      have hu : 0 < U N := up N he hn
      dsimp only [h]
      split
      · exact lt_min hu (div_pos (singularSeries_pos N) (by positivity))
      · exact hu
    have cap (N : ℕ) : h N ≤ U N := by
      dsimp only [h]
      split
      · exact min_le_left _ _
      · exact le_rfl
    have gain (N : ℕ) : 2*h N*eligibleNorm N ≤ singularSeries N := by
      dsimp only [h]
      split
      next hn =>
        have bound := (le_div_iff₀ (show 0<2*eligibleNorm N by positivity)).mp
          (min_le_right (U N) (singularSeries N/(2*eligibleNorm N)))
        linarith only [bound, show 2 * min (U N) _ * eligibleNorm N =
          min (U N) (singularSeries N/(2*eligibleNorm N)) * (2*eligibleNorm N) by ring]
      next hn =>
        have z := le_antisymm (le_of_not_gt hn) (eligibleNorm_nonneg N)
        simp [z,(singularSeries_pos N).le]
    have growth : EvenTendstoInfinity h := by
      intro t
      let B := max 1 t
      have bp : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
      obtain ⟨K,H⟩ := (ug B).and (dec (1/(2*B)) (by positivity))
      refine ⟨K, fun N hn he => ?_⟩
      obtain ⟨lim,small⟩ := H N hn he
      apply (le_max_right 1 t).trans
      dsimp only [h]
      split
      next hp =>
        refine le_min lim ((le_div_iff₀ (by positivity)).mpr ?_)
        have q : eligibleNorm N ≤ singularSeries N/(2*B) := by simpa [div_eq_mul_inv,mul_comm] using small
        have r := (le_div_iff₀ (show 0<2*B by positivity)).mp q
        linarith only [r, show eligibleNorm N*(2*B) = B*(2*eligibleNorm N) by ring]
      next => exact lim
    have wcap : EvenEventually (fun N => zeroFreeWidth N h ≤ 1/4) := by
      obtain ⟨K,H⟩ := uw.and evenEventually_large
      refine ⟨K,fun N hn he => ?_⟩
      obtain ⟨small,large⟩ := H N hn he
      obtain ⟨n4,logp,_⟩ := large_parameters large
      apply le_trans _ small
      unfold zeroFreeWidth
      apply div_le_div_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (singularSeries_pos N).le)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pos N he n4).le (cap N) 2) (pow_nonneg logp.le _)
    refine ⟨h,⟨pos,growth,wcap⟩,?_⟩
    obtain ⟨K,H⟩ := wcap.and evenEventually_large
    refine ⟨K,fun N hn he g inst ha => ?_⟩
    obtain ⟨small,large⟩ := H N hn he
    obtain ⟨n4,logp,_⟩ := large_parameters large
    have nr : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
    have sp := singularSeries_pos N
    have hp := pos N he n4
    have wp : 0 < zeroFreeWidth N h := by unfold zeroFreeWidth; positivity
    apply ((theorem_6_1 N he large g ha).2.1 _ wp (by linarith)).mpr
    rw [spectralScale_div_sqrt_width_eq N h nr sp logp hp (by linarith), ← eligibleNorm_spec N ha g]
    have root : 0 < Real.sqrt (1-zeroFreeWidth N h) := Real.sqrt_pos.mpr (by linarith)
    have root_le : Real.sqrt (1-zeroFreeWidth N h) ≤ 1 := (Real.sqrt_le_one).mpr (by linarith)
    apply (le_div_iff₀ (by positivity)).mpr
    have hb := mul_le_mul_of_nonneg_left root_le
      (show 0 ≤ 2*h N*eligibleNorm N by exact mul_nonneg (by linarith) (eligibleNorm_nonneg N))
    nlinarith only [hb,gain N]

#print axioms some_actual_S_iff
end GoldbachSpectral435

