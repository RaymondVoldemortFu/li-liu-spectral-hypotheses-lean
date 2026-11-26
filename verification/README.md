# Verifying the spectral results

| Result | Formal statement or export | Recorded evidence |
| --- | --- | --- |
| Refutation of R | `GoldbachSpectral435.Unconditional.not_R : ¬ ConditionalGoldbach.HypothesisR` | [Joint kernel check and axiom audit](unconditional-audit.log) |
| Spectral implication under Dirichlet GRH | `GoldbachSpectral435.refute_R` and the [spectral targets](spectral-targets.txt) | [Four-checker replay](spectral-audit.log) |
| Published Dirichlet GRH certificate | `LFunction_eq_zero_re_of_isPrimitive` | [Verified-mode challenge comparison](grh-replay.log) · [Interface comparison](interface.log) |
| S research | [Exact criteria, individual obstructions and estimates](existence-targets.txt) | [Replay log](existence-audit.log). The full existence question remains open. |
| Arithmetic lemmas | [Arithmetic targets](arithmetic-targets.txt) | [Four-checker replay](arithmetic-audit.log) |

The closed R theorem first specializes primitive Dirichlet GRH to each conductor dividing the modulus. It then applies the spectral refutation. The source of both steps is [UnconditionalAudit.lean](../WithGRH435/UnconditionalAudit.lean). For separately published GRH certificates, the challenge comparison also checks the primitive-character statement and the interface report compares seven definitions across libraries. [MIT verification files](https://math.mit.edu/~drew/grh/) · [Manifest and hashes](results.json)

## Build and replay

From the repository root, run the commands below individually. Use Python 3.11 or later, ripgrep, the pinned Lean toolchains, and the Lean 4.36 checker executables `leanchecker`, `lean4lean`, `con-leche` and `nanoda_bin`. With Elan available, the script selects Lake in the project directory. For standalone installations, use `--lake` and `--checker-bin` to specify the project Lake executable and checker directory.

```sh
python verification/replay.py unconditional
python verification/replay.py spectral
python verification/replay.py existence
python verification/replay.py arithmetic
```

The joint replay builds the pinned GRH and spectral dependencies. They both define a global name `nabla` with different meanings. The build helper checks the SHA-256 of the pinned Wiener source and renames its finite-difference declaration and its occurrences in a temporary copy. It then builds the joint theorem with warnings treated as errors and exports the listed roots. The combined export includes the proof terms of the GRH theorem. [Build helper](join-grh.py) · [Joint targets](unconditional-targets.txt)

For a native build of the spectral implication or S research, change to `Analytic435` and run `lake --wfail build AnalyticAudit` or `lake --wfail build ExistenceAudit`. Build the arithmetic support at the repository root with `lake --wfail build Audit`. The export checker accepts only propositional extensionality, classical choice and quotient soundness.

## Reproduce the separate GRH challenge check

Download the two compressed certificate files listed in the manifest. With PowerShell, zstd and the pinned con-leche executable available, run `verification/Replay-GRH.ps1 -CertificateDirectory <directory>`. To compare the cross-version statement trees, use the decompressed challenge and the spectral export.

```sh
python verification/compare-interface.py challenge.ndjson Analytic435/.lake/build/AnalyticAudit.ndjson
```

## Compile the manuscripts

Run pdfLaTeX twice on `refutation-of-R.tex` in [paper/R](../paper/R) or on `hypothesis-S.tex` in [paper/S](../paper/S). Each source includes its own bibliography. The [Chinese exposition](../paper/archive/spectral-hypotheses-zh.tex) uses XeLaTeX, ctex and the Fandol fonts.
