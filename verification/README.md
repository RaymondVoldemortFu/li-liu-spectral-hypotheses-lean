# Verifying the spectral results

| Result | Formal statement or export | Recorded evidence |
| --- | --- | --- |
| Refutation of R | `GoldbachSpectral435.Unconditional.not_R : ¬ ConditionalGoldbach.HypothesisR` | [Joint kernel check and axiom audit](unconditional-audit.log) · [Independent con-leche replay](unconditional-con-leche.log) |
| Spectral implication under Dirichlet GRH | `GoldbachSpectral435.refute_R` and the [spectral targets](spectral-targets.txt) | [Four-checker replay](spectral-audit.log) |
| Published Dirichlet GRH certificate | `LFunction_eq_zero_re_of_isPrimitive` | [Verified-mode challenge comparison](grh-replay.log) · [Interface comparison](interface.log) |
| S research | [Exact criteria, individual obstructions and estimates](existence-targets.txt) | [Replay log](existence-audit.log). The full existence question remains open. |
| Arithmetic lemmas | [Arithmetic targets](arithmetic-targets.txt) | [Four-checker replay](arithmetic-audit.log) |

The closed R theorem first specializes primitive Dirichlet GRH to each conductor dividing the modulus. It then applies the spectral refutation. The source of both steps is [UnconditionalAudit.lean](../WithGRH435/UnconditionalAudit.lean). For separately published GRH certificates, the challenge comparison also checks the primitive-character statement and the interface report compares seven definitions across libraries. [MIT verification files](https://math.mit.edu/~drew/grh/) · [Manifest and hashes](results.json)

## Build and replay

From the repository root, run the commands below individually. Use Python 3.11 or later, ripgrep and the pinned Lean toolchains. The first command uses the Lean 4.36 `leanchecker` executable. The other three also use `lean4lean`, `con-leche` and `nanoda_bin`. With Elan available, the script selects Lake in the project directory. For standalone installations, use `--lake` and `--checker-bin` to specify the project Lake executable and checker directory.

```sh
python verification/replay.py unconditional --lean-only
python verification/replay.py spectral
python verification/replay.py existence
python verification/replay.py arithmetic
```

The first command reproduces the recorded Lean kernel check of the 5.27 GB joint export and audits every axiom declaration. Omitting `--lean-only` requests all four checkers. The recorded four-checker results cover the separate spectral, existence-research and arithmetic exports.

To reproduce the independent joint check, run `lake build con-leche` in the [pinned con-leche checkout](https://github.com/leanprover/con-leche/tree/5dc36dc15b7bee891a02406b78a8ac816a47baad). Put that executable on PATH. From the proof repository root, run the following command after the Lean replay has finished. In verified mode, this build accepted all 209,642 declarations on four worker threads. [Transcript](unconditional-con-leche.log)

```sh
con-leche --verified --jobs=4 --progress=10% WithGRH435/.lake/build/UnconditionalAudit.ndjson
```

Nanoda also accepted the joint export with four threads and the three-axiom allowlist. From the repository root, run `nanoda_bin verification/unconditional-nanoda.json` for its independent check. For a joint replay with all four checkers, `--con-leche PATH` selects the pinned con-leche executable. The replay script runs the checkers sequentially and uses four con-leche workers for the joint proof.

The joint build also checks all three conclusions of the R manuscript against explicit statements of the operator and partial products. The audit records the original PDF pages, proof-body dependencies and axiom checks. [R manuscript audit](hypothesis-R.md)

The R manuscript also has a dedicated export with five roots. It includes the complete proofs of the norm growth, the refutation and the common zero sequence. Verified-mode con-leche accepted all 207,991 declarations. To rebuild it and repeat the independent check, run the following commands with the same pinned con-leche executable. [Manuscript export transcript](r-paper-export.log) · [Roots](r-paper-targets.txt)

```sh
python verification/replay.py r-paper --lean-only
con-leche --verified --jobs=4 --progress=10% WithGRH435/.lake/build/RPaperAudit.ndjson
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
