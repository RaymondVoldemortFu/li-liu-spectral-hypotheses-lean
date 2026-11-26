# The Li–Liu spectral hypotheses in Lean

This repository studies the residual operator in Jiamin Li and Jianya Liu’s *A Conditional Proof of the Goldbach Conjecture*. The English paper gives the definitions, proofs and the remaining open questions. [English paper (PDF)](paper/spectral-hypotheses.pdf) · [LaTeX source](paper/spectral-hypotheses.tex) · [Earlier Chinese manuscript (PDF)](paper/spectral-hypotheses-zh.pdf)

Under Dirichlet GRH, Hypothesis R fails. Hypothesis S also fails for some admissible functions that agree with $\log N$ outside an arbitrarily sparse set of even integers. Whether S holds for $h(N)=\log N$, or for any admissible $h$, remains open in this work. The proof uses the operator and hypotheses from the original formalization. [Pinned definitions](https://github.com/subfish-zhou/conditional-goldbach-lean/tree/c55db645f3b4aed00374fe4aa1fcee2428c88c4b)

## Mathematical results

| Question | Result and Lean source |
| --- | --- |
| Can actual zeros approach 1? | One sequence of real zeros approaches 1 faster than every inverse power of the logarithm. [OriginalStatements.lean](Analytic435/OriginalStatements.lean) |
| Can an exceptional set change S? | Any admissible function has a failing modification on a subsequence of arithmetic records. The proof bounds the size of that set. [ArithmeticWidths.lean](Analytic435/ArithmeticWidths.lean) · [SparsePrescriptions.lean](Analytic435/SparsePrescriptions.lean) |
| What would settle existence? | Some admissible function satisfies S exactly when the operator norm divided by the singular series tends to zero on eligible even integers. [ActualLimits.lean](Analytic435/ActualLimits.lean) |
| Can one test the norm through kernel values? | Finite matrices on one fixed sequence give an exact criterion for S, including its boundary. [FiniteSamples.lean](Analytic435/FiniteSamples.lean) |
| How large must a shift window be? | A Chebyshev bound limits the lower estimate from each test. Windows of size $o(N/(\log N)^4)$ give a vanishing estimate at the logarithmic scale. [ShortShiftLimit.lean](Analytic435/ShortShiftLimit.lean) |

The arithmetic construction uses the opposite prime shifts studied by Yilin Liu. The paper derives the analytic inputs and proves the required discrepancy by finite inclusion–exclusion. [Original article](https://mrc.sdu.edu.cn/english/info/1018/1514.htm) · [Yilin Liu’s preprint](https://hexagonmath.org/2611.00788v1)

## Finite prime sums for the existence question

Write $T_N$ for the residual operator and $M_N$ for the Li–Liu model operator. Set $m=\max(1,\lceil100\log\log N\rceil)$ and $X=N^{2m}$. Form $P_N$ from the odd-character Gram sum over prime powers up to $X$. Use the same squared weights for its diagonal $D_N$. For every sufficiently large even $N$ that satisfies the original local GRH condition, the operator norm satisfies

$$
\big\|T_N-(P_N-D_N-M_N)\big\|\le C(\log N)^{-16}.
$$

The constant is independent of $N$. Hypothesis S holds for some admissible $h$ exactly when $\|P_N-D_N-M_N\|/\mathfrak S(N)$ tends to zero on these moduli. Proving this limit or finding an infinite sequence that violates it remains open here. [Finite Gram sum](Analytic435/PerronOperators.lean) · [Diagonal estimate](Analytic435/PerronDiagonal.lean) · [Equivalence with S](Analytic435/PrimeResidual.lean)

For each test vector, the finite arithmetic term is a sum over pairs of prime powers. Equal residue classes contribute with a plus sign. Opposite residue classes contribute with a minus sign. The diagonal cancels. [Signed correlation formula](Analytic435/PrimeCorrelations.lean)

Set $Y=\lceil(\log N)^{100}\rceil$. Keep the primes up to $X$ and the prime powers below $Y^2$. With these indices alone, the signed quadratic form minus the original model still approximates $\langle f,T_N f\rangle$ within $C(\log N)^{-16}$ for every $\|f\|\leq1$. The constant is uniform in the eligible even modulus. For squares, the proof uses the fact that three distinct roots of one square residue modulo $N$ cannot all lie in an interval of length $Y$ when $Y^3<N$. For the remaining powers, the sum of the absolute coefficients converges with an explicit tail bound. [Square-root spacing](Analytic435/SquareResidues.lean) · [Removal of proper prime powers](Analytic435/PowerRemoval.lean)

One can also omit every pair $(n,j)$ with $\sqrt{nj}\leq N/(\log N)^{24}$ at the same error rate, uniformly over the unit ball. The sum of the absolute contributions of these pairs already satisfies the bound. The remaining sum includes pairs on the Goldbach line $n+j=N$ with both primes comparable to $N$. Its discrepancy from the model still has to be estimated. [Prime pairs below the hyperbola](Analytic435/PrimeHyperbola.lean)

## A necessary second term for the odd-character mean square

Fix an even integer $b\ge 2$ and a real number $c>1$. Take $N=b^{k+1}$ and $x=c/\log N$. Let $A_N(x)$ be the average of $|(L'/L)(1/2+x,\chi)|^2$ over the odd characters modulo $N$, with normalization $2/\varphi(N)$. If some admissible $h$ satisfies S and the local GRH condition holds along this sequence, then

$$
\lim_{k\to\infty} x\left(A_N(x)-\frac{1-e^{-2c}}{4x^2}\right)
=-\frac{e^{-2c}}2\left(\log\pi+\sum_{p\mid b}\frac{\log p}{p-1}-\psi(3/4)\right).
$$

Here $\psi=\Gamma'/\Gamma$ and the sum runs over the distinct prime divisors of $b$. The linear correction comes from the derivative of the regular part of the original model. The arithmetic diagonal has a double pole with bounded remainder. A failure of this limit for even one such $b,c$ would rule out every admissible $h$. [Model derivative](Analytic435/ConductorCorrection.lean) · [Arithmetic diagonal](Analytic435/DiagonalPole.lean) · [Mean-square limit](Analytic435/SecondMoment.lean)

## Decay as the left boundary moves

Let $T_{N,a}$ be the original residual operator on the strip with left boundary $a$ and right boundary $1/8$. Write $L=\log N$. For all sufficiently large eligible even $N$ and every $1/L\le a<1/8$, an absolute constant $D$ satisfies

$$
\frac{\|T_{N,a}\|}{\mathfrak S(N)}\le D L^2 e^{-aL}.
$$

In particular, the entire normalized operator tends to zero whenever $aL-2\log L\to+\infty$. At the boundary $a=1/L$ in Hypothesis S, the upper bound is $D L^2/e$. Decay at this boundary remains open. [Operator bound and limit](Analytic435/StripDecay.lean)

For a test vector supported at Fourier times $t>-\log Y$, the original arithmetic form is exactly a finite signed sum over $n,j<Y$. This holds for every positive integer $Y$ at each eligible modulus. When $2Y\le N$, odd-character orthogonality makes the sum zero. Restriction to the strip with left boundary $a$ bounds the contribution from the complementary times. The model has its own factor $N^{-2a}$. [Fourier support](Analytic435/PhysicalSupport.lean) · [Exact arithmetic form](Analytic435/LocalPrimeForm.lean) · [Model estimate](Analytic435/ModelDecay.lean)

## Build the proofs

Each project pins its Lean toolchain and Git dependencies. The main spectral project uses Lean 4.35.0. From the repository root, build it with Lake.

```sh
cd Analytic435
lake --wfail build AnalyticAudit
```

In the same directory, run `lake --wfail build ExistenceAudit` for the finite approximation and conductor moments. The root project checks the supporting arithmetic in Lean 4.36.0. From the repository root, run `lake --wfail build Audit`. Both builds treat warnings as errors. The audits inspect the dependencies of the named theorems.

## Replay the proof exports

Use Python 3.11 or later and ripgrep. Make the Lean 4.36 checker executables available on `PATH`, or pass their directory with `--checker-bin`. The executables are `leanchecker`, `lean4lean`, `con-leche` and `nanoda_bin`. With Elan on `PATH`, run the commands from the repository root.

```sh
python verification/replay.py spectral
python verification/replay.py existence
python verification/replay.py arithmetic
```

If you use a standalone Lean distribution, pass its Lake executable with `--lake`. The script builds the selected project, exports its listed theorems and runs all four checkers on the same file. It also reads the axiom declarations from the export. The only axioms are `propext`, `Classical.choice` and `Quot.sound`. [Verification manifest](verification/results.json) · [Spectral replay](verification/spectral-audit.log) · [Existence research replay](verification/existence-audit.log) · [Arithmetic replay](verification/arithmetic-audit.log)

The spectral proof states its GRH premise explicitly. A separate replay of the published Dirichlet GRH certificate used con-leche in verified mode. It accepted 1,468,418 declarations and matched all five challenge statements. We compared the primitive-character GRH statement and seven definitions across the two Lean versions. [GRH replay](verification/grh-replay.log) · [Statement comparison](verification/interface.log) · [Published certificates](https://math.mit.edu/~drew/grh/)

To repeat the GRH replay, put the two compressed certificates in one directory. Run `verification/Replay-GRH.ps1 -CertificateDirectory <directory>` with PowerShell, zstd, Python, ripgrep and the checker revision listed in the manifest. To repeat the statement comparison, run the following command with the expanded challenge file.

```sh
python verification/compare-interface.py challenge.ndjson Analytic435/.lake/build/AnalyticAudit.ndjson
```

## Compile the manuscripts

Each LaTeX source compiles on its own. From `paper`, run `pdflatex spectral-hypotheses.tex` twice for the English paper. For the earlier Chinese paper, run `xelatex spectral-hypotheses-zh.tex` twice with the ctex and Fandol packages.

