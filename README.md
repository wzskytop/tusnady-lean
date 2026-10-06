# Tight Bounds for Tusnády's Problem in the Plane — Lean verification

[![Verify Lean proof](https://github.com/wzskytop/tusnady-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/wzskytop/tusnady-lean/actions/workflows/verify.yml)

This submission snapshot binds the **r65 manuscript** to a Lean 4 proof of its **main lower-bound theorem**. The sources are directly browsable and build from the repository root. The formal proof uses the all-good-transitions union route. This is not a claim of line-by-line verification of the entire paper.

- [Paper PDF](verification/tusnady-plane-stoc27-vC-r65.pdf) and [LaTeX source](verification/tusnady-plane-stoc27-vC-r65.tex)
- [Main theorem](Oscillation/Main.lean), [r65 interfaces](Oscillation/R65.lean), and [explicit statement checks](scripts/Completion.lean)
- [Paper-to-code correspondence](PROOF_MAP.md) and [scope audit](AUDIT_R65.md)
- [Manuscript SHA256 hashes](verification/manuscript-r65.json)
- [Automated verification runs](https://github.com/wzskytop/tusnady-lean/actions/workflows/verify.yml)

## What is verified

`Oscillation.paper_lower_bound` proves: for every A > 0 there is c_A > 0, independent of n, such that for every n ≥ 1, iid uniform points in the unit square satisfy the anchored-rectangle lower bound c_A (log₂ n)^(3/2) simultaneously for every coloring, with probability at least 1 − exp(−An). Colorings may depend on the sampled points. `Oscillation.planar_tusnady_lower_bound` gives the deterministic lower-bound consequence. No unproved probabilistic estimates are premises of these theorems.

The simultaneous probability interface has the exact r65 constants 48, 64, and 2048 for even b ≥ 4. The good-transition probability interfaces cover every integer b ≥ 3. The final existential theorem chooses a sufficiently large power-of-two base.

The local gain is proved using an even-base representative/Rademacher argument. The internal potential uses finite vertical probes and is connected to genuine continuous anchored-rectangle counts; it is not identified with the paper's continuous-height potential. General symmetric-variable statements and every step of the paper's arbitrary-base local proof are not fully covered. The cited matching upper bound and therefore the complete two-sided Θ statement are outside this formalization. See the correspondence table for precise hypotheses.

## Reproduce

Install [Lean via elan](https://lean-lang.org/install/). The repository pins Lean 4.34.1 and all dependency commits in `lake-manifest.json`. From a fresh checkout:

```sh
lake exe cache get
python3 scripts/verify.py --replay
```

The first command downloads the pinned dependencies and their Mathlib cache. Do not update the manifest to newer dependency versions for this snapshot. The verifier rejects dependency revision mismatches or dirty dependency source checkouts.

Verification builds all local modules, checks eight explicit statement interfaces, traverses the final theorem's actual proof dependencies, audits every imported local theorem's axioms, and replays each non-umbrella module with Lean's kernel. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted. Placeholder proofs, custom axioms, and native computation bypasses are prohibited in the proof sources. Existing nonblocking style/deprecation warnings are recorded.

GitHub Actions performs the same checks on a fresh Ubuntu runner without restoring this project's build cache. Each run records its exact Git commit, manuscript hashes, source hashes, build output, axiom reports, and individual replay results. Its evidence and checked ZIP are downloadable from that run. `verification/current-run.json` is generated only after successful verification; it is not a preexisting certificate to trust instead of rebuilding.

To create a byte-checked package after successful replay:

```sh
python3 scripts/package.py ../tusnady-r65-lean-verified.zip
```

## Citation and version

Use the submission release `r65-submission-v1` and record its full commit SHA. The manuscript files are preserved as supplied, including the existing repository URL. The earlier private development history is not required to reproduce this snapshot. Retained proof modules with older names are dependencies or audited supporting results; the dependency checker requires the all-transition union route and excludes the r17 sequential-crowding reduction from the main proof.

Code, scripts, and repository documentation are [MIT licensed](LICENSE). The [manuscript licensing scope](MANUSCRIPT_LICENSE.md) is separate. Citation metadata is in [CITATION.cff](CITATION.cff).
