module
public import ConditionalGoldbach.Proofs.FiniteMellinDouble
public import ConditionalGoldbach.Proofs.MellinDiagonal
public import ConditionalGoldbach.Proofs.FiniteModelBasic

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory ConditionalGoldbach Complex
namespace GoldbachSpectral435

def diagCoeff (N i : ℕ) : ℂ := if (i+1).Coprime N then (mangoldt (i+1):ℂ)^2/(i+1:ℕ) else 0

theorem diagonal_test (N M : ℕ) (hm : 0 < M) (φ : ℝ → ℝ) (smooth : FiniteModelWeight φ)
    (σ : ℝ) (hs : 0 < σ) :
    let D := fun s z : ℂ => (M:ℂ)^(s+z)*mellinWeight φ s*mellinWeight φ z*diagonalSeries N (s+z)
    Integrable (fun p : ℝ × ℝ => D (line σ p.1) (line σ p.2)) ∧
      verticalMellin σ (fun s => verticalMellin σ (D s)) =
        ∑' i : ℕ, diagCoeff N i*(companion φ ((i+1:ℕ)/(M:ℝ)):ℂ)^2 := by
  intro D
  let u := fun i : ℕ => (i+1:ℕ)/(M:ℝ)
  have up (i : ℕ) : 0 < u i := by dsimp [u]; positivity
  have su : Summable (fun i : ℕ => ‖diagCoeff N i‖ * Real.rpow (u i) (-σ)^2) := by
    have h := diagonalSeries_summable N (w := (σ:ℂ)+σ) (by simpa using hs)
    apply (((summable_nat_add_iff 1).2 h).mul_left ‖(M:ℂ)^((σ:ℂ)+σ)‖).congr
    intro i
    have ident := congrArg norm (mellin_diagonal_rescale M (i+1) hm (by omega) (σ:ℂ) (σ:ℂ) ((mangoldt (i+1):ℂ)^2))
    simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < (i+1:ℕ)/(M:ℝ)),neg_re,ofReal_re,
      ← Real.rpow_eq_pow] at ident
    simp only [diagCoeff,Nat.succ_pos,true_and]
    split_ifs
    · simpa only [u,pow_two,mul_assoc] using ident.symm
    · simp
  let F := fun (i : ℕ) (s z : ℂ) => diagCoeff N i *
    (mellinWeight φ s*(u i:ℂ)^(-s))*(mellinWeight φ z*(u i:ℂ)^(-z))
  have iden (s z : ℂ) (h : 0 < (s+z).re) : ∑' i : ℕ, F i s z = D s z := by
    have summ : Summable (fun n : ℕ => if 0<n ∧ n.Coprime N then
        (mangoldt n:ℂ)^2/(n:ℂ)^(1+(s+z)) else 0) := by
      apply Summable.of_norm
      simpa only [apply_ite norm,norm_zero] using diagonalSeries_summable N h
    dsimp only [D]
    unfold diagonalSeries
    rw [summ.tsum_eq_zero_add]
    simp only [Nat.not_lt_zero,false_and,ite_false,zero_add,Nat.succ_pos,true_and]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    dsimp only [F,diagCoeff]
    split_ifs
    · have r := mellin_diagonal_rescale M (i+1) hm (by omega) s z ((mangoldt (i+1):ℂ)^2)
      calc
        _ = ((mangoldt (i+1):ℂ)^2/(i+1:ℕ)*(u i:ℂ)^(-s)*(u i:ℂ)^(-z))*(mellinWeight φ s*mellinWeight φ z) := by ring
        _ = _ := by dsimp only [u]; rw [r]; ring
    · ring
  have spec := finite_double_mellin_inversion_series (companion φ)
    ((FiniteModel.companion_contDiff smooth).of_le (by norm_num)) _ _ (FiniteModel.companion_support_subset smooth)
    σ hs u (diagCoeff N) up su
  have hline (t v : ℝ) : 0 < (line σ t+line σ v).re := by simp [line]; linarith
  constructor
  · exact spec.1.congr (Filter.Eventually.of_forall (fun p => iden _ _ (hline p.1 p.2)))
  · rw [spec.2.tsum_eq]
    unfold verticalMellin
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    congr 1
    apply integral_congr_ae
    filter_upwards [] with v
    exact (iden _ _ (hline t v)).symm

#print axioms diagonal_test
end GoldbachSpectral435

