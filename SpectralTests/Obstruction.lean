module
public import SpectralTests.Thresholds
public import SpectralTests.Singular

@[expose] public section
namespace GoldbachSpectral
open Filter
open scoped Quaternion Topology

/-- A cofinal, squared consequence of Y. Liu's Theorem 1.1(ii).
The local GRH condition is inside the existential quantifier of that theorem. -/
def LiuInput (M : ℕ → ℝ) (G : ℕ → Prop) : Prop :=
  ∀ d K : ℕ, ∃ N : ℕ, K ≤ N ∧ Even N ∧ (G N → Real.log N ^ d < (N:ℝ)*(M N)^2)

noncomputable def logWidth (a : ℕ) (N : ℕ) : ℝ := 1/(4*Real.log N^a)

/-- The implication of the pointwise spectral dictionary needed for a disproof. -/
def ZeroFreeImpliesBound (M : ℕ → ℝ) (G : ℕ → Prop) (X : ℕ → ℍ[ℝ] → ℍ[ℝ]) : Prop :=
  ∃ K : ℕ, ∀ N ≥ K, Even N → G N → ∀ η : ℝ, 0 < η → η < 1/2 →
    (∀ q, X N q = 0 → q.re ≤ 1-η) → Sbound (deltaSq N (singular N)) (M N) η

theorem eventually_small_series :
    ∀ᶠ N : ℕ in atTop, 2 ≤ Real.log N ∧ singular N ≤ Real.log N^2 := by
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  filter_upwards [hl.eventually_ge_atTop (4 / Real.log 2 + 4), eventually_ge_atTop 1] with N h hn
  change 4 / Real.log 2 + 4 ≤ Real.log N at h
  have hp : 0 < 4 / Real.log 2 := div_pos (by norm_num) h2
  have hN : 0 < N := by omega
  refine ⟨by linarith, (singular_le N hN).trans ?_⟩
  have halfpos : 0 < 2/Real.log 2 := by positivity
  have twice : 4/Real.log 2 = 2*(2/Real.log 2) := by ring
  have H : 0 ≤ Real.log N * (Real.log N - (2/Real.log 2+1)) :=
    mul_nonneg (by linarith) (by linarith)
  have he : Real.log N * (2 / Real.log 2) = 2 * (Real.log N / Real.log 2) := by ring
  nlinarith

theorem logWidth_fails {a N : ℕ} {m : ℝ}
    (hn : 0 < N) (hl : 2 ≤ Real.log N) (hs : singular N ≤ Real.log N^2)
    (large : Real.log N^(a+6) < (N:ℝ)*m^2) :
    ¬ Sbound (deltaSq N (singular N)) m (logWidth a N) := by
  let L := Real.log N
  have Lpos : 0 < L := by dsimp [L]; linarith
  have P : 1 ≤ L^a := one_le_pow₀ (by linarith : 1 ≤ L)
  have hn' : (0:ℝ) < N := by exact_mod_cast hn
  change L^(a+6) < (N:ℝ)*m^2 at large
  change singular N ≤ L^2 at hs
  intro h
  change 4 * (1/(4*L^a)) * (1-1/(4*L^a))*m^2 ≤ singular N * L^3 / N at h
  have hwidth : 1/(4*L^a) ≤ 1/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : (3/4) * (m^2 / L^a) ≤ singular N * L^3 / N := by
    apply le_trans _ h
    have eqn : 4 * (1/(4*L^a)) * (1-1/(4*L^a))*m^2 =
        (1-1/(4*L^a)) * (m^2/L^a) := by field_simp
    rw [eqn]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hcl : 3*((N:ℝ)*m^2) ≤ 4*singular N*L^(a+3) := by
    rw [pow_add]
    field_simp at hb
    nlinarith [hb]
  have hupper := mul_le_mul_of_nonneg_right hs (show 0 ≤ 4*L^(a+3) by positivity)
  have h6 : L^(a+6) = L^(a+5)*L := by rw [show a+6 = a+5+1 by omega, pow_succ]
  have h5 : L^(a+5) = L^(a+3)*L^2 := by rw [show a+5 = a+3+2 by omega, pow_add]
  have hL : 2 ≤ L := hl
  have lower := mul_le_mul_of_nonneg_left hL (show 0 ≤ L^(a+5) by positivity)
  rw [← h6] at lower
  rw [h5] at lower
  nlinarith [large,hupper,hcl,lower]

/-- There are zeros strictly to the right of every inverse-logarithmic boundary,
at arbitrarily large eligible even moduli. The two analytic inputs are explicit. -/
theorem cofinal_zeros {M : ℕ → ℝ} {G : ℕ → Prop} {X : ℕ → ℍ[ℝ] → ℍ[ℝ]}
    (liu : LiuInput M G) (grh : ∀ N, Even N → G N)
    (dictionary : ZeroFreeImpliesBound M G X) (a K : ℕ) :
    ∃ N ≥ K, Even N ∧ G N ∧ ∃ q : ℍ[ℝ], X N q = 0 ∧ 1-logWidth a N < q.re := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp eventually_small_series
  obtain ⟨F,hF⟩ := dictionary
  obtain ⟨N,hN,even,large⟩ := liu (a+6) (max (max (max K 1) B) F)
  have hK : K ≤ N := by omega
  have h1 : 0 < N := by omega
  obtain ⟨hl,hs⟩ := hB N (by omega)
  have hg := grh N even
  have bad := logWidth_fails h1 hl hs (large hg)
  refine ⟨N,hK,even,hg,?_⟩
  by_contra! none
  have hpow : 1 ≤ Real.log N^a := one_le_pow₀ (by linarith)
  apply bad (hF N (by omega) even hg _ (by unfold logWidth; positivity) _ none)
  unfold logWidth
  apply (div_lt_iff₀ (by positivity)).mpr
  linarith

/-- The actual zero-set formulations with the eventual/local-GRH quantifiers. -/
def HypothesisR (G : ℕ → Prop) (X : ℕ → ℍ[ℝ] → ℍ[ℝ]) : Prop :=
  ∃ K : ℕ, ∀ N ≥ K, Even N → G N → ∀ q, X N q = 0 → q.re = 1/2

def Admissible (h : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, Even n → 4 ≤ n → 0 < h n) ∧
  (∀ b : ℝ, ∃ K : ℕ, ∀ N ≥ K, Even N → b ≤ h N) ∧
  (∃ K : ℕ, ∀ N ≥ K, Even N → width N (singular N) (h N) ≤ 1/4)

def HypothesisS (G : ℕ → Prop) (X : ℕ → ℍ[ℝ] → ℍ[ℝ]) (h : ℕ → ℝ) : Prop :=
  Admissible h ∧ ∃ K : ℕ, ∀ N ≥ K, Even N → G N → ∀ q, X N q = 0 → q.re ≤ 1-width N (singular N) (h N)

theorem reject_R_and_wide_S {M : ℕ → ℝ} {G : ℕ → Prop} {X : ℕ → ℍ[ℝ] → ℍ[ℝ]}
    (liu : LiuInput M G) (grh : ∀ N, Even N → G N) (dictionary : ZeroFreeImpliesBound M G X) :
    ¬ HypothesisR G X ∧ ∀ (h : ℕ → ℝ) (a : ℕ),
      (∃ K : ℕ, ∀ N ≥ K, Even N → G N → logWidth a N ≤ width N (singular N) (h N)) →
        ¬ HypothesisS G X h := by
  constructor
  · rintro ⟨K,H⟩
    obtain ⟨N,hN,he,hg,q,hq,far⟩ := cofinal_zeros liu grh dictionary 0 K
    rw [H N hN he hg q hq] at far
    norm_num [logWidth] at far
  · rintro h a ⟨K,hw⟩ ⟨_,F,H⟩
    obtain ⟨N,hN,he,hg,q,hq,far⟩ := cofinal_zeros liu grh dictionary a (max K F)
    linarith [hw N (by omega) he hg, H N (by omega) he hg q hq]

end GoldbachSpectral

