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

## The first Goldbach line on the original strip

For two complex unit vectors supported at Fourier times $t>-\log N$, the full arithmetic operator after diagonal subtraction has a single sum. If $c_x(n)=-\Lambda(n)n^{-1/2}\langle x,d_n\rangle$, where $d_n$ is the monomial Hardy vector, then

$$
\langle x,(P_N^{\mathrm{arith}}-D_N^{\mathrm{arith}})y\rangle
=-\sum_{\substack{n<N\\(n,N)=1}}c_x(n)\overline{c_y(N-n)}.
$$

Here the two operators are the original infinite arithmetic Gram operator and diagonal. The formula applies to every pair of vectors with the stated support. It gives exact cancellation when their respective physical cutoffs $Y,Z$ satisfy $Y+Z\le N$. [Reflection formula](Analytic435/Reflection.lean)

For arbitrary positive integer cutoffs $Y,Z$, set $W=\max(Y,Z)$. At the original boundary $a=1/\log N$, the absolute mixed arithmetic entry is bounded by

$$
162(\log W)^2(1+\log(W+1))^2\frac{\sqrt{YZ}}{N}.
$$

In particular it is at most $10368/(\log N)^2$ throughout $W\le N^2$ and $\sqrt{YZ}\le N/(\log N)^6$. The unit vectors, the modulus and the two window sizes may vary together. When both physical cutoffs are comparable to $N$, estimating the discrepancy between the reflected prime sum and the continuous model remains necessary. [Critical-window bounds](Analytic435/PhysicalHyperbola.lean)

## Finite formulas on a dense family of tests

Fix an eligible modulus $N$. Take any positive integer $k$, put $M=kN$, and let $f$ be a real $C^6$ function compactly supported in $(0,1)$. Put $w(n)=\Lambda(n)f(n/M)/\sqrt M$. Write $e_N(j,n)$ for the signed unit-residue indicator after diagonal subtraction and $J_f(y)=2\int_0^\infty f(u)f(u+y)\,du-\int_0^\infty f(u)f(y-u)\,du$. The original Riesz vector $x_f$ satisfies the exact identity

$$
\langle x_f,T_Nx_f\rangle=
\sum_{n,j<M}w(n)w(j)e_N(j,n)
-\sum_{\ell=1}^{2k}\mathfrak S(\ell N)J_f(\ell/k).
$$

Both sums are finite. The model formula follows from Mellin inversion of the continued density after dilation. At $k=1$ the difference is $\mathfrak S(N)\int_0^1 f(u)f(1-u)\,du$ minus the reflected Mangoldt sum. [Dilation and inversion](Analytic435/Dilation.lean) · [Exact finite discrepancy](Analytic435/FiniteDiscrepancy.lean) · [First-scale identity](Analytic435/ReflectionModel.lean)

Denote the displayed difference by $D_N(k,f)$. Let $E_N(k,f)$ be the squared norm of the test vector. Some admissible $h$ satisfies Hypothesis S if and only if, for every $\varepsilon>0$, every sufficiently large eligible even $N$ satisfies

$$
|D_N(k,f)|\leq \varepsilon\,\mathfrak S(N) E_N(k,f)
\qquad\text{for every integer }k\geq 1\text{ and every real compact }C^6\text{ weight }f.
$$

At each such modulus, the least constant multiplying $E_N(k,f)$ is exactly $\|T_N\|$. One can put two tests on a common scale and take their real linear combinations there. The real and imaginary parts of a complex test contribute additively to its squared norm and to its residual quadratic form. These complex tests are dense in the original Hardy space. The uniform arithmetic estimate above remains open. [Density](Analytic435/PhysicalDensity.lean) · [Real and imaginary parts](Analytic435/TestCombinations.lean) · [Exact norm and existence criterion](Analytic435/PhysicalCriterion.lean)

At the first scale, write $F(u)=f(u)f(1-u)$. Let $H_N(t)$ be the sum of $\Lambda(n)\Lambda(N-n)/N$ over units $n<N$ with $n/N<t$, minus $t\mathfrak S(N)$. Then $D_N(1,f)=\int_0^1 H_N(t)F'(t)\,dt$. If $|H_N(j/m)|\le D$ at every mesh point, the entry is bounded by $(D+\mathfrak S(N)/m)\int_0^1|F'|$. The estimate applies simultaneously to all the test weights. [Cumulative count and mesh bound](Analytic435/GoldbachPrimitive.lean)

There is also an unconditional mean bound for the absolute prime masses at the two ends of this line. Put $v(n)=\Lambda(n)/\sqrt n$ for $n>0$ and $v(0)=0$. Summing $v(n)v(j)$ over $n+j=N$, $n\le Y$, $j\le Z$, and over any finite set of distinct moduli costs at most $16(4+\log 4)^2\sqrt{YZ}$. At each eligible modulus, nine times its individual mass bounds the mixed arithmetic entry for any two unit vectors with these respective physical cutoffs, provided $Y,Z\le N$. [Mean bound](Analytic435/MeanReflection.lean)

For weights supported on $u\ge 1/N$, the same mesh gives a bound in the Hilbert norm itself,

$$
|D_N(1,f)|\le 16\pi\bigl(D+\mathfrak S(N)/m\bigr) E_N(1,f).
$$

The constant is uniform as the support approaches either endpoint. Integration by parts gives $\int_0^1(f(u)/(1-u))^2\,du\le4\int_0^1 u^2 f'(u)^2\,du$. Applying this inequality to the reflected product bounds its total variation by four times $\int_0^1(f(u)/2-u f'(u))^2\,du$. [Reflection inequality](Analytic435/ReflectionVariation.lean) · [Norm bound](Analytic435/ReflectionEnergy.lean)

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

