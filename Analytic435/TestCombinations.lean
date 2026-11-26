module
public import RescaleTests
public import TestReality

/-! The real compact Mellin tests are closed under real linear combinations,
and their complexification is dense in the original space. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PhysicalTests

private def summed {f g : ℝ→ℝ} (s : FiniteModelWeight f) (t : FiniteModelWeight g) :
    FiniteModelWeight (f+g) where
  smooth := s.smooth.add t.smooth
  lower := min s.lower t.lower
  upper := max s.upper t.upper
  lower_pos := lt_min s.lower_pos t.lower_pos
  upper_lt_one := max_lt s.upper_lt_one t.upper_lt_one
  lower_le_upper := (min_le_left ..).trans (s.lower_le_upper.trans (le_max_left ..))
  support_subset := by
    intro u nu
    by_cases p : f u=0
    · have h := t.mem_support_interval (u:=u) (by intro z; apply nu; simp [p,z])
      exact ⟨(min_le_right ..).trans h.1,h.2.trans (le_max_right ..)⟩
    · have h := s.mem_support_interval p
      exact ⟨(min_le_left ..).trans h.1,h.2.trans (le_max_left ..)⟩

private def scaled (r : ℝ) {f : ℝ→ℝ} (hf : FiniteModelWeight f) :
    FiniteModelWeight (fun t => r*f t) :=
  ⟨contDiff_const.mul hf.smooth,_,_,hf.lower_pos,hf.upper_lt_one,hf.lower_le_upper,
    fun _ h => hf.mem_support_interval (mul_ne_zero_iff.mp h).2⟩

private theorem scale_vector (N M : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) (mp : 0<M)
    (r : ℝ) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    testVector N M mp (fun t => r*f t) (scaled r hf)=(r:ℂ) • testVector N M mp f hf := by
  let g := fun t => r*f t
  let σ : ℝ := 1/9
  have sp : 0<σ := by norm_num [σ]
  have comp (t : ℝ) : companion g t=r*companion f t := by unfold companion g; ring
  have mell (s : ℂ) : mellinWeight g s=(r:ℂ)*mellinWeight f s := by
    unfold mellinWeight
    simp_rw [comp,Complex.ofReal_mul]
    exact mellin_const_smul (fun t : ℝ => (companion f t:ℂ)) s (r:ℂ)
  apply ext_inner_right ℂ
  intro v
  change paperInner v (testVector N M mp g _) = inner ℂ ((r:ℂ) • testVector N M mp f hf) v
  rw [inner_smul_left,Complex.conj_ofReal]
  change paperInner v (testVector N M mp g _)=(r:ℂ)*paperInner v (testVector N M mp f hf)
  rw [← testVector_rep N M mp g _ σ sp (sample_line big) v,← testVector_rep N M mp f hf σ sp (sample_line big) v]
  unfold finiteFunctionalValue verticalMellin
  change _*(∫ t : ℝ, (M:ℂ)^line σ t*mellinWeight g (line σ t)*(1+line σ t)*fourierLaplace v (line σ t))=_
  have point (s : ℂ) : (M:ℂ)^s*mellinWeight g s*(1+s)*fourierLaplace v s=
      (r:ℂ)*((M:ℂ)^s*mellinWeight f s*(1+s)*fourierLaplace v s) := by rw [mell]; ring
  simp_rw [point]
  rw [integral_const_mul]
  change _*((r:ℂ)*(∫ t : ℝ, _))=(r:ℂ)*(_*(∫ t : ℝ, _))
  rw [mul_left_comm]
  rfl

theorem common_scale (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) {x y : HardySpace (alpha N) beta}
    (hx : x∈tests N) (hy : y∈tests N) :
    ∃ (k : ℕ) (kp : 0<k), AtScale N (k*N) (Nat.mul_pos kp (NeZero.pos N)) x ∧
      AtScale N (k*N) (Nat.mul_pos kp (NeZero.pos N)) y := by
  obtain ⟨i,ip,f,hf,rfl⟩ := hx
  obtain ⟨j,jp,g,hg,rfl⟩ := hy
  refine ⟨max i j,ip.trans_le (le_max_left ..),?_,?_⟩
  · exact atScale_mono N _ _ big _ (Nat.mul_le_mul_right N (le_max_left i j)) ⟨f,hf,rfl⟩
  · exact atScale_mono N _ _ big _ (Nat.mul_le_mul_right N (le_max_right i j)) ⟨g,hg,rfl⟩

theorem add_test (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) {x y : HardySpace (alpha N) beta}
    (hx : x∈tests N) (hy : y∈tests N) : x+y∈tests N := by
  obtain ⟨k,kp,⟨f,hf,rfl⟩,g,hg,rfl⟩ := common_scale N big hx hy
  exact ⟨k,kp,f+g,summed hf hg,(testVector_add N _ _ f g hf hg _ (1/9) (by norm_num) (sample_line big)).symm⟩

theorem smul_test (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) (r : ℝ) {x : HardySpace (alpha N) beta}
    (hx : x∈tests N) : (r:ℂ) • x∈tests N := by
  obtain ⟨k,kp,f,hf,rfl⟩ := hx
  exact ⟨k,kp,_,scaled r hf,(scale_vector N _ big _ r f hf).symm⟩

theorem zero_test (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) :
    (0 : HardySpace (alpha N) beta)∈tests N := by
  let hf : FiniteModelWeight (fun _ => 0) :=
    ⟨contDiff_const,1/3,2/3,by norm_num,by norm_num,by norm_num,by simp⟩
  have x : testVector N (1*N) (Nat.mul_pos zero_lt_one (NeZero.pos N)) _ hf∈tests N :=
    ⟨1,zero_lt_one,_,hf,rfl⟩
  simpa using smul_test N big 0 x

/-- Every vector is a norm limit of x+i y with x and y individual real-weight
tests, which may use a common enlarged sampling scale. -/
theorem dense_complexification (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) :
    Dense {z : HardySpace (alpha N) beta | ∃ x∈tests N, ∃ y∈tests N, z=x+Complex.I • y} := by
  let H := HardySpace (alpha N) beta
  let K : Submodule ℂ H :=
    { carrier := {z | ∃ x∈tests N, ∃ y∈tests N, z=x+Complex.I • y}
      zero_mem' := ⟨0,zero_test N big,0,zero_test N big,by simp⟩
      add_mem' := by
        rintro _ _ ⟨x,hx,y,hy,rfl⟩ ⟨u,hu,v,hv,rfl⟩
        exact ⟨x+u,add_test N big hx hu,y+v,add_test N big hy hv,by rw [smul_add]; abel⟩
      smul_mem' := by
        rintro c _ ⟨x,hx,y,hy,rfl⟩
        refine ⟨(c.re:ℂ) • x+((-c.im:ℝ):ℂ) • y,add_test N big (smul_test N big _ hx) (smul_test N big _ hy),
          (c.im:ℂ) • x+(c.re:ℂ) • y,add_test N big (smul_test N big _ hx) (smul_test N big _ hy),?_⟩
        have a : (c.re:ℂ)+Complex.I*(c.im:ℂ)=c := by simpa only [mul_comm Complex.I] using Complex.re_add_im c
        have b : ((-c.im:ℝ):ℂ)+Complex.I*(c.re:ℂ)=c*Complex.I := by
          apply Complex.ext <;> simp
        rw [smul_add,smul_smul,smul_add,smul_smul,smul_smul]
        calc
          _ = ((c.re:ℂ) • x+(Complex.I*(c.im:ℂ)) • x)+
              (((-c.im:ℝ):ℂ) • y+(Complex.I*(c.re:ℂ)) • y) := by rw [← add_smul,← add_smul,a,b]
          _ = _ := by abel }
  have incl : Submodule.span ℂ (tests N)≤K := by
    apply Submodule.span_le.mpr
    intro x hx
    exact ⟨x,hx,0,zero_test N big,by simp⟩
  exact (dense_tests N big).mono incl

#print axioms dense_complexification
end GoldbachSpectral435.PhysicalTests
