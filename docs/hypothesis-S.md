# Results on Hypothesis S

The question is whether there exists an admissible function $h$ satisfying Li and Liu’s Hypothesis S. It remains open. The following results give equivalent criteria and necessary conditions. [Research paper](../paper/S/hypothesis-S.pdf) · [List of checked theorems](../verification/existence-targets.txt)

## Finite prime sums for the existence question

Write $T_N$ for the residual operator and $M_N$ for the Li–Liu model operator. Set $m=\max(1,\lceil100\log\log N\rceil)$ and $X=N^{2m}$. Form $P_N$ from the odd-character Gram sum over prime powers up to $X$. Use the same squared weights for its diagonal $D_N$. For every sufficiently large even $N$ that satisfies the original local GRH condition, the operator norm satisfies

$$
\big\|T_N-(P_N-D_N-M_N)\big\|\le C(\log N)^{-16}.
$$

The constant is independent of $N$. Hypothesis S holds for some admissible $h$ exactly when $\|P_N-D_N-M_N\|/\mathfrak S(N)$ tends to zero on these moduli. Proving this limit or finding an infinite sequence that violates it remains open here. [Finite Gram sum](../Analytic435/PerronOperators.lean) · [Diagonal estimate](../Analytic435/PerronDiagonal.lean) · [Equivalence with S](../Analytic435/PrimeResidual.lean)

For each test vector, the finite arithmetic term is a sum over pairs of prime powers. Equal residue classes contribute with a plus sign. Opposite residue classes contribute with a minus sign. The diagonal cancels. [Signed correlation formula](../Analytic435/PrimeCorrelations.lean)

Set $Y=\lceil(\log N)^{100}\rceil$. Keep the primes up to $X$ and the prime powers below $Y^2$. With these indices alone, the signed quadratic form minus the original model still approximates $\langle f,T_N f\rangle$ within $C(\log N)^{-16}$ for every $\|f\|\leq1$. The constant is uniform in the eligible even modulus. For squares, the proof uses the fact that three distinct roots of one square residue modulo $N$ cannot all lie in an interval of length $Y$ when $Y^3<N$. For the remaining powers, the sum of the absolute coefficients converges with an explicit tail bound. [Square-root spacing](../Analytic435/SquareResidues.lean) · [Removal of proper prime powers](../Analytic435/PowerRemoval.lean)

One can also omit every pair $(n,j)$ with $\sqrt{nj}\leq N/(\log N)^{24}$ at the same error rate, uniformly over the unit ball. The sum of the absolute contributions of these pairs already satisfies the bound. The remaining sum includes pairs on the Goldbach line $n+j=N$ with both primes comparable to $N$. Its discrepancy from the model still has to be estimated. [Prime pairs below the hyperbola](../Analytic435/PrimeHyperbola.lean)

## A necessary second term for the odd-character mean square

Fix an even integer $b\ge 2$ and a real number $c>1$. Take $N=b^{k+1}$ and $x=c/\log N$. Let $A_N(x)$ be the average of $|(L'/L)(1/2+x,\chi)|^2$ over the odd characters modulo $N$, with normalization $2/\varphi(N)$. If some admissible $h$ satisfies S and the local GRH condition holds along this sequence, then

$$
\lim_{k\to\infty} x\left(A_N(x)-\frac{1-e^{-2c}}{4x^2}\right)
=-\frac{e^{-2c}}2\left(\log\pi+\sum_{p\mid b}\frac{\log p}{p-1}-\psi(3/4)\right).
$$

Here $\psi=\Gamma'/\Gamma$ and the sum runs over the distinct prime divisors of $b$. The linear correction comes from the derivative of the regular part of the original model. The arithmetic diagonal has a double pole with bounded remainder. A failure of this limit for even one such $b,c$ would rule out every admissible $h$. [Model derivative](../Analytic435/ConductorCorrection.lean) · [Arithmetic diagonal](../Analytic435/DiagonalPole.lean) · [Mean-square limit](../Analytic435/SecondMoment.lean)

## Decay as the left boundary moves

Let $T_{N,a}$ be the original residual operator on the strip with left boundary $a$ and right boundary $1/8$. Write $L=\log N$. For all sufficiently large eligible even $N$ and every $1/L\le a<1/8$, an absolute constant $D$ satisfies

$$
\frac{\|T_{N,a}\|}{\mathfrak S(N)}\le D L^2 e^{-aL}.
$$

In particular, the entire normalized operator tends to zero whenever $aL-2\log L\to+\infty$. At the boundary $a=1/L$ in Hypothesis S, the upper bound is $D L^2/e$. Decay at this boundary remains open. [Operator bound and limit](../Analytic435/StripDecay.lean)

For a test vector supported at Fourier times $t>-\log Y$, the original arithmetic form is exactly a finite signed sum over $n,j<Y$. This holds for every positive integer $Y$ at each eligible modulus. When $2Y\le N$, odd-character orthogonality makes the sum zero. Restriction to the strip with left boundary $a$ bounds the contribution from the complementary times. The model has its own factor $N^{-2a}$. [Fourier support](../Analytic435/PhysicalSupport.lean) · [Exact arithmetic form](../Analytic435/LocalPrimeForm.lean) · [Model estimate](../Analytic435/ModelDecay.lean)

## The first Goldbach line on the original strip

For two complex unit vectors supported at Fourier times $t>-\log N$, the full arithmetic operator after diagonal subtraction has a single sum. If $c_x(n)=-\Lambda(n)n^{-1/2}\langle x,d_n\rangle$, where $d_n$ is the monomial Hardy vector, then

$$
\langle x,(P_N^{\mathrm{arith}}-D_N^{\mathrm{arith}})y\rangle
=-\sum_{\substack{n<N\\(n,N)=1}}c_x(n)\overline{c_y(N-n)}.
$$

Here the two operators are the original infinite arithmetic Gram operator and diagonal. The formula applies to every pair of vectors with the stated support. It gives exact cancellation when their respective physical cutoffs $Y,Z$ satisfy $Y+Z\le N$. [Reflection formula](../Analytic435/Reflection.lean)

For arbitrary positive integer cutoffs $Y,Z$, set $W=\max(Y,Z)$. At the original boundary $a=1/\log N$, the absolute mixed arithmetic entry is bounded by

$$
162(\log W)^2(1+\log(W+1))^2\frac{\sqrt{YZ}}{N}.
$$

In particular it is at most $10368/(\log N)^2$ throughout $W\le N^2$ and $\sqrt{YZ}\le N/(\log N)^6$. The unit vectors, the modulus and the two window sizes may vary together. When both physical cutoffs are comparable to $N$, estimating the discrepancy between the reflected prime sum and the continuous model remains necessary. [Critical-window bounds](../Analytic435/PhysicalHyperbola.lean)

## Finite formulas on a dense family of tests

Fix an eligible modulus $N$. Take any positive integer $k$, put $M=kN$, and let $f$ be a real $C^6$ function compactly supported in $(0,1)$. Put $w(n)=\Lambda(n)f(n/M)/\sqrt M$. Write $e_N(j,n)$ for the signed unit-residue indicator after diagonal subtraction and $J_f(y)=2\int_0^\infty f(u)f(u+y)\,du-\int_0^\infty f(u)f(y-u)\,du$. The original Riesz vector $x_f$ satisfies the exact identity

$$
\langle x_f,T_Nx_f\rangle=
\sum_{n,j<M}w(n)w(j)e_N(j,n)
-\sum_{\ell=1}^{2k}\mathfrak S(\ell N)J_f(\ell/k).
$$

Both sums are finite. The model formula follows from Mellin inversion of the continued density after dilation. At $k=1$ the difference is $\mathfrak S(N)\int_0^1 f(u)f(1-u)\,du$ minus the reflected Mangoldt sum. [Dilation and inversion](../Analytic435/Dilation.lean) · [Exact finite discrepancy](../Analytic435/FiniteDiscrepancy.lean) · [First-scale identity](../Analytic435/ReflectionModel.lean)

Denote the displayed difference by $D_N(k,f)$. Let $E_N(k,f)$ be the squared norm of the test vector. Some admissible $h$ satisfies Hypothesis S if and only if, for every $\varepsilon>0$, every sufficiently large eligible even $N$ satisfies

$$
|D_N(k,f)|\leq \varepsilon\,\mathfrak S(N) E_N(k,f)
\qquad\text{for every integer }k\geq 1\text{ and every real compact }C^6\text{ weight }f.
$$

At each such modulus, the least constant multiplying $E_N(k,f)$ is exactly $\|T_N\|$. One can put two tests on a common scale and take their real linear combinations there. The real and imaginary parts of a complex test contribute additively to its squared norm and to its residual quadratic form. These complex tests are dense in the original Hardy space. The uniform arithmetic estimate above remains open. [Density](../Analytic435/PhysicalDensity.lean) · [Real and imaginary parts](../Analytic435/TestCombinations.lean) · [Exact norm and existence criterion](../Analytic435/PhysicalCriterion.lean)

At the first scale, write $F(u)=f(u)f(1-u)$. Let $H_N(t)$ be the sum of $\Lambda(n)\Lambda(N-n)/N$ over units $n<N$ with $n/N<t$, minus $t\mathfrak S(N)$. Then $D_N(1,f)=\int_0^1 H_N(t)F'(t)\,dt$. If $|H_N(j/m)|\le D$ at every mesh point, the entry is bounded by $(D+\mathfrak S(N)/m)\int_0^1|F'|$. The estimate applies simultaneously to all the test weights. [Cumulative count and mesh bound](../Analytic435/GoldbachPrimitive.lean)

There is also an unconditional mean bound for the absolute prime masses at the two ends of this line. Put $v(n)=\Lambda(n)/\sqrt n$ for $n>0$ and $v(0)=0$. Summing $v(n)v(j)$ over $n+j=N$, $n\le Y$, $j\le Z$, and over any finite set of distinct moduli costs at most $16(4+\log 4)^2\sqrt{YZ}$. At each eligible modulus, nine times its individual mass bounds the mixed arithmetic entry for any two unit vectors with these respective physical cutoffs, provided $Y,Z\le N$. [Mean bound](../Analytic435/MeanReflection.lean)

For weights supported on $u\ge 1/N$, the same mesh gives a bound in the Hilbert norm itself,

$$
|D_N(1,f)|\le 16\pi\bigl(D+\mathfrak S(N)/m\bigr) E_N(1,f).
$$

The constant is uniform as the support approaches either endpoint. Integration by parts gives $\int_0^1(f(u)/(1-u))^2\,du\le4\int_0^1 u^2 f'(u)^2\,du$. Applying this inequality to the reflected product bounds its total variation by four times $\int_0^1(f(u)/2-u f'(u))^2\,du$. [Reflection inequality](../Analytic435/ReflectionVariation.lean) · [Norm bound](../Analytic435/ReflectionEnergy.lean)

For arbitrary first-scale weights, including support below $1/N$, put $d_N=\sup_{0\le t\le1}|H_N(t)|$. The full range of such tests satisfies

$$
|D_N(1,f)|\le 576\pi\left(d_N+\frac{\mathfrak S(N)}{N}\right)E_N(1,f).
$$

Subtracting $tH_N(1)$ from the cumulative error makes it vanish at both endpoints. Below the first sample and above the last nonzero sample its value is explicit. The weight $1-e^{-Nu}$ incorporates those endpoint contributions into the Hardy norm. Thus $d_N=o(\mathfrak S(N))$ would suffice at the first scale even for weights that vary with $N$. The existence criterion also requires all larger scales. [Endpoint estimate](../Analytic435/PrimitiveEndpoints.lean) · [Weighted inequality](../Analytic435/WeightedReflection.lean) · [Uniform first-scale theorem](../Analytic435/FirstBlockBound.lean)

## A rectangular kernel at every scale

For $M=kN$, insert the identity $f(u)=-\int_u^1 (f(s)/\sqrt{s})'\sqrt{u}\,ds$ in both factors of the prime sum and each convolution. This gives a real kernel $C_{N,k}(s,t)$ on the unit square. The arithmetic term counts pairs with $n<Ms$ and $j<Mt$, with the original residue sign and the additional factor $\sqrt{nj}/M$. The model term integrates the same square-root weights over the three lines $v=u+\ell/k$, $u=v+\ell/k$ and $v=\ell/k-u$, with signs $+,+,-$.

Let $a=1/\log N$, $\beta=1/8$, and put $b(u)^2=u^3(Mu)^{2\beta}/(1+(Mu)^{2(\beta-a)})$ on $0<u\le1$. For every finite dilation $k\ge1$, the kernel $K_{N,k}(s,t)=C_{N,k}(s,t)/(b(s)b(t))$ is square-integrable on the full unit square. Each affine line is separated from the origin, and its contribution to $|C_{N,k}(s,t)|$ is bounded by a constant times $(st)^{3/2}$. After division by the energy factors, the square has an integrable majorant proportional to $(st)^{-1/4}$. The constant may depend on $N,k$. [Boundary estimates](../Analytic435/ThresholdEdges.lean) · [Finite kernel](../Analytic435/KernelEnvelope.lean) · [Square integrability](../Analytic435/KernelIntegrability.lean)

Every real compact test satisfies

$$
|D_N(k,f)|\le 2\pi\|K_{N,k}\|_{L^2((0,1)^2)}E_N(k,f).
$$

Consequently, a bound $\sup_{k\ge1}\|K_{N,k}\|_2=o(\mathfrak S(N))$ on eligible moduli would imply the existence assertion. The theorem proves the implication. Establishing decay requires cancellation between the prime counts and the line integrals. [Integral representation](../Analytic435/CumulativeKernel.lean) · [Prime and model kernels](../Analytic435/ThresholdDiscrepancy.lean) · [Norm estimate](../Analytic435/KernelBound.lean)

## One prescribed scale per modulus

Put $L=\log N$ and $k_N=\lceil\exp(8L\log L)/N\rceil$. If every real compact test at this one scale satisfies $|D_N(k_N,f)|\le B E_N(k_N,f)$ for some $B\ge0$, then

$$
\|T_N\|\le B+\frac{C}{(\log N)^2}
$$

with an absolute constant $C$ independent of $N$ and $B$. Consequently, the uniform little-$o$ estimate on real tests at $k_N$ alone is equivalent to the full existence assertion. At each modulus the arithmetic and continuous terms at that scale involve only finitely many prime pairs and shifts. The remaining estimate must hold for every sufficiently large eligible even integer.

The proof identifies the closure needed at one scale. For a smooth test $\phi$ supported on a compact subinterval of a right half-line, the equation $g+g'=\phi-e^{-d}\phi(\,\cdot-d)$ has a smooth compact solution on the same half-line for every $d\ge0$. This separates all integrable densities there. The resulting bound extends from real tests at $M=k_NN$ to complex Hardy vectors supported above $-\log M$ with the same constant. On the complement, the squared output energy is at most $C' L^{-4}$ times the squared input norm. Self-adjointness gives the stated error for the full operator. [Half-line separation](../Analytic435/HalfLineTests.lean) · [Density at one scale](../Analytic435/SingleScaleDensity.lean) · [Complex blocks](../Analytic435/SingleScaleBound.lean) · [Norm estimate and equivalence](../Analytic435/SingleScaleCriterion.lean)

## An unconditional bound on mass in short intervals

There is an absolute constant $C$ such that, for every even $N\ge 2^{64}$ and all integers $A,Y\ge0$ with $A+Y\le N+1$,

$$
\sum_{A\le n<A+Y}\Lambda(n)\Lambda(N-n)
\le C\bigl(Y\mathfrak S(N)+\sqrt N(\log N)^2\bigr).
$$

The estimate applies to every translate of the interval. At a prime $p$, the sieve removes the residues $0$ and $N$, counting them once if they coincide. The Chinese remainder theorem gives every complete squarefree period. Each incomplete period has count error at most its length. In the Selberg sieve, at least half the Euler-product mass is retained on divisors up to $z^8$. This follows by bounding the logarithmic first moment, using $\sum_{p\le z}(\log p)/p\le 2\log z$. Choosing $z=\lfloor N^{1/64}\rfloor$ bounds the sieve remainder by a constant times $\sqrt N$. The estimate for $\psi-\theta$ controls the proper prime powers. [Selberg denominator](../Analytic435/SieveDenominator.lean) · [Residue counts](../Analytic435/SieveResidues.lean) · [Euler product](../Analytic435/SieveEuler.lean) · [Interval sieve](../Analytic435/GoldbachUpper.lean) · [Weighted count](../Analytic435/WindowTightness.lean)

For the original first-line counting measure, put $F_N(t)=t+H_N(t)/\mathfrak S(N)$. For $0\le s\le t\le1$ one has $0\le F_N(t)-F_N(s)\le C(t-s+1/N+(\log N)^2/\sqrt N)$. In particular, any sequence of intervals of vanishing relative length has vanishing normalized mass as the even moduli grow. The estimate gives upper bounds on concentration. Identifying the limiting mass on each interval still requires a prime-pair asymptotic. [Original counting measure](../Analytic435/GoldbachIntervals.lean)

## Sharp Goldbach counts and the first scale

Along every sequence of eligible even moduli tending to infinity, the normalized first-scale bound for all real test functions tends to zero if and only if

$$
\sup_{0\le t\le1} |F_N(t)-t|\longrightarrow 0.
$$

In particular the existence of any admissible $h$ satisfying S implies this uniform asymptotic for the actual von Mangoldt pair counts. To prove the forward implication, polarization and reflection symmetry recover each smooth interior weight from the original quadratic forms. The translated sieve estimate controls the ends of each interval as the test approaches its indicator. Positivity of the counting measure extends convergence on a finite mesh to every threshold. The reverse implication uses the first-scale operator estimate above. [Energy and exact entries](../Analytic435/FirstLineLimits.lean) · [Polarization](../Analytic435/GoldbachSmoothTests.lean) · [Interval tests](../Analytic435/GoldbachWindowTests.lean) · [Equivalence](../Analytic435/SharpGoldbachLimits.lean)

For ordinary primes let $P_N(t)$ count the ordered pairs $p+q=N$ with $p<tN$. Uniformly in $t$ and every sufficiently large even $N$, the translated sieve and finite Abel summation give
$$
\left|F_N(t)-\frac{(\log N)^2 P_N(t)}{N\mathfrak S(N)}\right|
\le C\left(\frac1{\log N}+\frac{(\log N)^2}{\sqrt N}\right).
$$
In fact the proof bounds the sum of the absolute differences of all the atomic masses, including the possible prime pair $p=q=N/2$. Consequently the first-scale spectral criterion is equivalent to the uniform sharp asymptotic for ordinary ordered prime representations. [Logarithmic weight loss](../Analytic435/PrimePairLogLoss.lean) · [Total variation estimate](../Analytic435/PrimePairVariation.lean) · [Prime counts and the original operator](../Analytic435/GoldbachPrimeCounts.lean)

## The signed frequency tail and rational arcs

On the first scale, the sharp prime-count asymptotic is equivalent to decay of the signed Fourier tail for each pair of smooth tests. The rational-arc approximation evaluates the principal coefficient as $\mu(q)/\varphi(q)$ for every reduced denominator, using local GRH at $4q$. Truncating the Ramanujan series at a fixed power of $\lfloor\log N/64\rfloor$ approximates the original singular series within any prescribed relative error uniformly over the full range of even shifts. Controlling the signed prime-pair discrepancy at each required even shift remains open. [Tail criterion](../Analytic435/GoldbachLineTail.lean) · [Rational arcs](../Analytic435/ArchimedeanPrimeArcs.lean) · [Ramanujan series](../Analytic435/RamanujanCoefficients.lean)
