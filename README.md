# The Li–Liu spectral hypotheses in Lean

This repository studies Hypotheses R and S for the residual operator in Jiamin Li and Jianya Liu’s *A Conditional Proof of the Goldbach Conjecture*. The [Chinese manuscript (PDF)](output/pdf/Goldbach-Spectral.pdf) and its [LaTeX source](output/pdf/Goldbach-Spectral.tex) give the mathematical arguments.

The main Lean development imports the operator and the two hypotheses from the [fixed revision of the original formalization](https://github.com/subfish-zhou/conditional-goldbach-lean/tree/c55db645f3b4aed00374fe4aa1fcee2428c88c4b). Under the paper’s eventual local Dirichlet GRH premise, it refutes R and proves failure of S for specified functions. The existence of an admissible function for which S holds remains open in this work.

| File | Result |
| --- | --- |
| [PaperPremise.lean](Analytic435/PaperPremise.lean) | Conclusions with precisely the original eventual GRH quantifier |
| [OriginalStatements.lean](Analytic435/OriginalStatements.lean) | Norm lower bounds and real zeros of the original quaternionic spectral function |
| [ArithmeticWidths.lean](Analytic435/ArithmeticWidths.lean) | A failing width chosen from arithmetic data that decays faster than every inverse power of the logarithm |
| [ActualLimits.lean](Analytic435/ActualLimits.lean) and [PositiveWidth.lean](Analytic435/PositiveWidth.lean) | An exact criterion for some admissible S and a certified zero-free width |

From `Analytic435`, run `lake --wfail build AnalyticAudit` with the pinned Lean 4.35.0 toolchain. The auxiliary arithmetic project at the root uses Lean 4.36.0. The manuscript credits Yilin Liu’s opposite-shift construction and supplies an independent proof of the analytic inputs used here.

Lean, lean4lean, con-leche and nanoda accepted the same export of the spectral results. Its only axioms are `propext`, `Classical.choice` and `Quot.sound`. The spectral theorems explicitly quantify the Dirichlet GRH premise. A separate local replay of the full GRH proof with con-leche in verified mode accepted 1,468,418 declarations and matched all five challenge statements. The primitive-character statement and seven mathematical definitions were compared across the two toolchain versions.

The [verification manifest](verification/results.json) records the proof and manuscript hashes. The [spectral replay log](verification/spectral-audit.log), [external GRH replay](verification/grh-replay.log) and [statement comparison](verification/interface.log) contain the checker output. To reproduce the external check, use the [certificate files](https://math.mit.edu/~drew/grh/) with the [replay script](verification/Replay-GRH.ps1).

