# The Li–Liu spectral hypotheses in Lean

**Leiming Fu** · November 2026

| Original question | Result | Manuscript |
| --- | --- | --- |
| **R**. Must every spectral zero have real part $1/2$ for every sufficiently large eligible even $N$? | **Formally refuted.** Lean proves `¬ ConditionalGoldbach.HypothesisR` with no GRH premise in the final theorem. | [R paper (PDF)](paper/R/refutation-of-R.pdf) · [LaTeX](paper/R/refutation-of-R.tex) · [Proof release](https://github.com/RaymondVoldemortFu/li-liu-spectral-hypotheses-lean/releases/tag/hypothesis-r-v1.0.1) |
| **S**. Does there exist an admissible $h$ for which $X_N$ has the prescribed zero-free region? | **Open.** Certain admissible functions fail. The full existence statement has an exact operator-norm criterion. The choice $h(N)=\log N$ also remains undecided here. | [S research paper (PDF)](paper/S/hypothesis-S.pdf) · [LaTeX](paper/S/hypothesis-S.tex) |

Both questions use Jiamin Li and Jianya Liu’s residual operator on the strip with left boundary $1/\log N$ and right boundary $1/8$. Binary Goldbach remains open in this work. [Original paper](https://mrc.sdu.edu.cn/english/info/1018/1514.htm) · [Original Lean definitions](https://github.com/subfish-zhou/conditional-goldbach-lean/blob/main/formalization/ConditionalGoldbach/Definitions/Hypotheses.lean)

## R — the refutation

If R held, then $N\lVert T_N\rVert^2\leq\mathfrak S(N)(\log N)^3\leq(\log N)^5$ eventually. The opposite-shift construction gives arbitrarily large even $N$ for which $N\lVert T_N\rVert^2>(\log N)^d$ for any fixed $d$. There is a single sequence of genuine real spectral zeros approaching $1$ faster than every fixed inverse power of $\log N$. Yilin Liu previously reported failure under Dirichlet GRH. This formalization derives the required discrepancy by finite inclusion–exclusion. [Arithmetic construction and zeros](Analytic435/OriginalStatements.lean) · [Yilin Liu’s preprint](https://hexagonmath.org/2611.00788v1)

The spectral implication is `GoldbachSpectral435.refute_R`. The joint Lean project supplies the primitive-character Dirichlet GRH theorem and proves `GoldbachSpectral435.Unconditional.not_R`. The final theorem depends on `propext`, `Classical.choice` and `Quot.sound`. [Conditional proof](Analytic435/SpectralRefutation.lean) · [Closed theorem](WithGRH435/UnconditionalAudit.lean#L16) · [Statement and proof audit](verification/hypothesis-R.md) · [Verification records and replay](verification/README.md)

## S — the existence question

Some admissible prescriptions fail, including sparse modifications of $\log N$. Existence of a successful prescription is equivalent to $\lVert T_N\rVert/\mathfrak S(N)\to0$ along the eligible even moduli. The first physical scale alone requires a uniform Hardy–Littlewood asymptotic for ordered Goldbach pairs with a sharp cutoff on the first prime. The global norm limit and a sequence violating it by a fixed positive proportion are both outstanding. [Individual failures](Analytic435/SparsePrescriptions.lean) · [Norm equivalence](Analytic435/ActualLimits.lean) · [Prime-count theorem](Analytic435/GoldbachPrimeCounts.lean) · [Detailed results and Lean sources](docs/hypothesis-S.md)

## Repository guide

| Location | Contents |
| --- | --- |
| [paper/R](paper/R) and [paper/S](paper/S) | Standalone English manuscripts and their LaTeX sources |
| [paper/archive](paper/archive) | Earlier Chinese exposition of the conditional argument |
| [WithGRH435](WithGRH435) | Joint composition with the proved Dirichlet GRH theorem |
| [Analytic435](Analytic435) | Spectral refutation, prescribed widths and results on existence, using the original definitions in Lean 4.35 |
| [SpectralTests](SpectralTests) | Arithmetic lemmas also checked in the root Lean 4.36 project |
| [verification](verification/README.md) | Build commands, proof exports, axiom checks and transcripts |

## Authorship and use of AI

Leiming Fu is the named author of the manuscripts and repository. OpenAI Codex assisted with proof construction, Lean formalization, verification scripts and manuscript drafting. The verification records identify the statements and proofs checked by the kernels. [Citation metadata](CITATION.cff) · [Verification manifest](verification/results.json)

To cite the code, use **Cite this repository** on GitHub. Each paper lists its own title and author and can be cited separately.

