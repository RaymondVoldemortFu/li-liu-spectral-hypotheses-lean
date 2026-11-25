module
public import SpectralTests.Conclusions
public import SpectralTests.PrimeProgression
public import SpectralTests.BandPrimes
public import SpectralTests.Lattice
public import SpectralTests.BandRows
public import SpectralTests.WindowSize
public import SpectralTests.ProgressionAverage
public import SpectralTests.ReflectedBeta
public import SpectralTests.SlowLimit
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
namespace GoldbachSpectral
open MeasureTheory Set
open scoped Quaternion ComplexConjugate

/-- Correlation, exact diagonal, and continued Beta model, (2.6), (2.11), (2.12).
The second argument is a boundary point; conjugation is performed here. -/
noncomputable def weightedKernel (N : ℕ) [NeZero N] (s z : ℂ) : ℂ := by
  classical
  let g := fun (χ : DirichletCharacter ℂ N) (t : ℂ) =>
    deriv χ.LFunction (1/2+t) / χ.LFunction (1/2+t)
  let P := (2/(N.totient:ℂ)) * ∑ χ : DirichletCharacter ℂ N,
    if χ (-1) = -1 then g χ s * conj (g χ z) else 0
  let w := s+conj z
  let D := ∑' n : ℕ, if 0 < n ∧ n.Coprime N then
    (ArithmeticFunction.vonMangoldt n : ℂ)^2 / (n:ℂ)^(1+w) else 0
  let euler := ∏' p : ℕ, if p.Prime ∧ 2 < p ∧ ¬ p ∣ N then
    1+(p:ℂ)^(-w)/((p:ℂ)-2) else 1
  let X₁ := fun t : ℂ => Complex.Gamma ((3/2-t)/2) / Complex.Gamma ((3/2+t)/2)
  let K := (singular N:ℂ) * ((Real.pi:ℂ)/N)^w * euler * riemannZeta (1-w) * X₁ s * X₁ (conj z)
  exact (P-D-K)/((1+s)*(1+conj z))

abbrev Boundary := Fin 2 × ℝ
noncomputable def arcLength : Measure Boundary := Measure.count.prod volume
noncomputable abbrev BoundarySpace := Lp ℂ 2 arcLength
noncomputable abbrev BoundaryOperator := BoundarySpace →L[ℂ] BoundarySpace

noncomputable def boundaryPoint (N : ℕ) (p : Boundary) : ℂ :=
  ⟨if p.1=0 then 1/Real.log N else 1/8, p.2⟩

/-- Equation (2.17) on the full boundary. Proposition 5.3 of Li–Liu identifies
this with the Hardy operator extended by zero on the orthogonal complement. -/
def Represents (N : ℕ) (T : BoundaryOperator) : Prop :=
  ∀ [NeZero N], ∀ f : BoundarySpace, ∀ᵐ p ∂arcLength, (T f) p =
    ∫ y : Boundary, weightedKernel N (boundaryPoint N p) (boundaryPoint N y) * f y ∂arcLength

theorem realization_unique {N : ℕ} [NeZero N] {T U : BoundaryOperator}
    (hT : Represents N T) (hU : Represents N U) : T = U := by
  ext f : 1
  apply Lp.ext
  filter_upwards [hT f, hU f] with p hp hq using hp.trans hq.symm

/-- Existence/compactness of the boundary realization and the opposite-shift
Hardy entry estimate are the external analytic inputs, together with ShiftBias. -/
structure ArithmeticRealization (T : ℕ → BoundaryOperator) : Prop where
  represents : ∃ K : ℕ, ∀ N ≥ K, Even N → LocalGRH N → Represents N (T N)
  compact : CompactSymmetric T
  entries : HardyEntries T LocalGRH

/-- Actual arithmetic moduli, the unique operator with the explicit integral
kernel above, and a real zero of the product with multiplicity. -/
theorem arithmetic_real_zeros (g : DirichletGRH) (arithmetic : ShiftBias)
    (realization : ∃ T, ArithmeticRealization T) (a K : ℕ) :
    ∃ N ≥ K, Even N ∧ LocalGRH N ∧ ∃ T : BoundaryOperator,
      Represents N T ∧ (∀ U, Represents N U → T = U) ∧
      ∃ r ∈ Ioo (1-1/(4*Real.log N^a)) 1, spectralX T (deltaSq N (singular N)) (r:ℍ[ℝ]) = 0 := by
  obtain ⟨T,ht⟩ := realization
  obtain ⟨F,hF⟩ := ht.represents
  obtain ⟨N,hN,he,hg,r,lo,hi,root⟩ :=
    real_zeros_from_inputs g ht.compact ht.entries arithmetic a (max (max K F) 1)
  let : NeZero N := ⟨by omega⟩
  have hrep := hF N (by omega) he hg
  exact ⟨N,by omega,he,hg,T N,hrep,fun _ hU => realization_unique hrep hU,r,⟨lo,hi⟩,root⟩

def ArithmeticR : Prop :=
  ∃ K : ℕ, ∀ N ≥ K, Even N → LocalGRH N → ∀ T : BoundaryOperator, Represents N T →
    ∀ q : ℍ[ℝ], spectralX T (deltaSq N (singular N)) q = 0 → q.re = 1/2

def ArithmeticS (h : ℕ → ℝ) : Prop :=
  Admissible h ∧ ∃ K : ℕ, ∀ N ≥ K, Even N → LocalGRH N → ∀ T : BoundaryOperator, Represents N T →
    ∀ q : ℍ[ℝ], 1-width N (singular N) (h N) < q.re → spectralX T (deltaSq N (singular N)) q ≠ 0

theorem arithmetic_obstruction (g : DirichletGRH) (arithmetic : ShiftBias)
    (realization : ∃ T, ArithmeticRealization T) :
    ¬ ArithmeticR ∧ ∀ (h : ℕ → ℝ) (a : ℕ),
      (∃ K : ℕ, ∀ N ≥ K, Even N → LocalGRH N → logWidth a N ≤ width N (singular N) (h N)) →
      ¬ ArithmeticS h := by
  constructor
  · rintro ⟨K,H⟩
    obtain ⟨N,hN,he,hg,T,hT,_,r,hr,hx⟩ := arithmetic_real_zeros g arithmetic realization 0 K
    have h := H N hN he hg T hT (r:ℍ[ℝ]) hx
    rw [Quaternion.re_coe] at h
    have lower := hr.1
    norm_num at lower
    linarith
  · rintro h a ⟨K,hwide⟩ ⟨_,F,free⟩
    obtain ⟨N,hN,he,hg,T,hT,_,r,hr,hx⟩ := arithmetic_real_zeros g arithmetic realization a (max K F)
    apply free N (by omega) he hg T hT (r:ℍ[ℝ]) _ hx
    rw [Quaternion.re_coe]
    have lower := hr.1
    have w := hwide N (by omega) he hg
    unfold logWidth at w
    linarith

theorem arithmetic_prescribed (g : DirichletGRH) (arithmetic : ShiftBias)
    (realization : ∃ T, ArithmeticRealization T) (a : ℕ) :
    Admissible (prescribedH a) ∧ ¬ ArithmeticS (prescribedH a) :=
  ⟨admissible_even a, (arithmetic_obstruction g arithmetic realization).2 _ a
    ⟨2, fun N hN _ _ => (prescribed_width a N (by omega)).ge⟩⟩

/-- On this explicit arithmetic route the Maier/Buchstab input is absent.
The same moduli are chosen before local GRH is assumed. -/
theorem arithmetic_one_shift {T : ℕ → BoundaryOperator} (ht : ArithmeticRealization T) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, ∃ N ≥ K, Even N ∧
      (LocalGRH N → Represents N (T N) ∧ c*Real.log N^2 ≤ (N:ℝ)*‖T N‖^2) := by
  obtain ⟨F,hF⟩ := ht.represents
  obtain ⟨c,hc,H⟩ := one_shift_lower (transfer_from_entries ht.entries)
  refine ⟨c,hc,fun K => ?_⟩
  obtain ⟨N,hN,he,lo⟩ := H (max F K)
  exact ⟨N,by omega,he,fun hg => ⟨hF N (by omega) he hg, lo hg⟩⟩

end GoldbachSpectral

