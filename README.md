# Tight Bounds for Tusnády's Problem in the Plane — Lean verification

[![Verify Lean proof](https://github.com/wzskytop/tusnady-lean-arxiv/actions/workflows/verify.yml/badge.svg)](https://github.com/wzskytop/tusnady-lean-arxiv/actions/workflows/verify.yml)

This submission snapshot binds the **r65 manuscript** to a Lean 4 proof of its **main lower-bound theorem**, following the manuscript's continuous oscillation, symmetric-jump, and digit-filtration route. It does not claim line-by-line verification of the entire paper.

- [Paper PDF](verification/tusnady-plane-stoc27-vC-r65.pdf) and [LaTeX source](verification/tusnady-plane-stoc27-vC-r65.tex)
- [Main theorem](R56Audit/Parameters.lean), [deterministic lower bound](R56Audit/Parameters.lean), and [independent explicit statement checks](scripts/SubmissionStatements.lean)
- [Paper-to-code correspondence](PROOF_MAP.md), [scope audit](AUDIT_R65.md), and [supplement provenance](audit-claude/PROVENANCE.json)
- [Manuscript SHA256 hashes](verification/manuscript-r65.json)

## What is verified

`R56Audit.theorem_1_1_unfolded` states directly in terms of iid Lebesgue-uniform points in the unit square and continuous anchored-rectangle sums: for every A > 0 there is c_A > 0, independent of n, such that for every n ≥ 1 the lower bound c_A (log₂ n)^(3/2) holds simultaneously for every coloring, with probability at least 1 − exp(−An). Colorings may depend on the sampled points. `R56Audit.corollary_1_2_lower` supplies the deterministic consequence. Neither theorem assumes unproved probabilistic estimates.

The primary proof uses the full continuous-height oscillation potential, symmetric jumps for every integer base b ≥ 3, conditional digits, successive conditioning, and Markov's inequality. Proposition 2.7 has the paper's constants 64, 48, and 2048 without an even-base restriction. The general symmetric-variable moment bound (Fact 2.2) and conditional bounded-differences statement (Fact A.1) are included.

The historical namespace `R56Audit` is retained to minimize source changes: 31 of the 33 supplied files are byte-for-byte unchanged; the legacy comparisons in `ArchiveRoute.lean` and `GoodTransitionsArchive.lean` only adapt three `R56` references to `R65` (and one comment). This repository binds and verifies those sources against **r65**. `Oscillation.paper_lower_bound` is an older, separately checked comparison proof; it is not the primary manuscript-route theorem. The primary theorem's transitive proof dependencies are checked to exclude that older route.

The cited matching upper bound, the complete two-sided Θ statement, historical claims, bibliography, figures, and explanatory discussion are outside the formalization. See the correspondence table for exact scope and measure-theoretic conventions.

## Reproduce

Install [Lean via elan](https://lean-lang.org/install/). Lean 4.34.1 and all dependency commits are pinned. From a fresh checkout:

```sh
lake exe cache get
python3 scripts/verify.py --replay
```

Do not update `lake-manifest.json` for this snapshot. The verifier rejects revision mismatches or dirty dependency sources. Plain `lake build` builds both libraries; it is not a substitute for the full verification command.

Full verification covers all **91 local modules** (including two declaration-free umbrella modules), 89 per-module kernel replays, all 907 supplement constants, 353 source-derived statement/definition examples, 52 rejected mutations and three accepted controls, five independent semantic checks, and an unrestricted traversal of the two primary conclusions. The supplement is recompiled with strict lint checks and no messages. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted. Legacy proof modules and their eight completion checks remain verified too; their existing style/deprecation warnings are recorded.

GitHub Actions runs the same verifier on a fresh Ubuntu runner, without restoring this project's build cache. Each run records its Git commit, manuscript and source hashes, dependency revisions, audit output, and every replay result. A new `verification/current-run.json` is written only after successful verification. Download that run's evidence and checked ZIP from Actions; do not treat an older receipt as evidence for changed sources.

After successful full replay, create the checked package with:

```sh
python3 scripts/package.py ../tusnady-r65-lean-verified.zip
```

For the supplement's checks alone, use `bash audit-claude/check.sh`. This does not replace the full verifier's manuscript binding or legacy kernel replay.

## Citation, provenance, and license

This is source snapshot version `r65-submission-v2`; cite the exact Git commit. A version string does not imply that a GitHub release or tag exists. The manuscript files are preserved as supplied, including their intended repository URL. The current staging repository is `wzskytop/tusnady-lean-arxiv`; the permanent manuscript URL is `wzskytop/tusnady-lean`.

The original formalization was developed with GPT assistance. The added manuscript-route library and audit were supplied as a Claude audit package; this integration and independent statement/dependency checks were performed with Codex. The manuscript's existing AI-methodology wording is preserved and should be reviewed before submission to reflect this added contribution.

Code, scripts, and repository documentation are [MIT licensed](LICENSE). The [manuscript licensing scope](MANUSCRIPT_LICENSE.md) is separate. Citation metadata is in [CITATION.cff](CITATION.cff).
