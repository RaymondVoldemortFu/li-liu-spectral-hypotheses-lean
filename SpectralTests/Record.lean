module
public import SpectralTests.Arithmetic
import Mathlib.Tactic.NormNum.Prime

@[expose] public section
namespace GoldbachSpectral

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem no_inner_offset :
    ∀ j : Fin 1281, ¬ GoodPair 742856 (371428-j.val) (371428+j.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checked_window :
    EmptyWindow 742856 (1281/742856) ∧ GoodPair 742856 370147 372709 ∧
      Nat.Prime 370147 ∧ Nat.Prime 372709 := by
  constructor
  · have h := window_of_offsets (k := 371428) (r := 1281) (by decide)
      (fun j hj => no_inner_offset ⟨j,hj⟩)
    norm_num at h ⊢
    exact h
  · exact ⟨by decide +kernel,by norm_num1,by norm_num1⟩

end GoldbachSpectral

