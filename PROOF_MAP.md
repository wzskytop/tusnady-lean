# r65 correspondence

The primary manuscript route is in namespace `R56Audit`. Its historical name is retained to minimize changes to the supplied proof sources (see the recorded legacy-reference adaptation). The r65 PDF and TeX are bound by `verification/manuscript-r65.json`.

| Manuscript item | Lean declaration | Coverage |
|---|---|---|
| Theorem 1.1 | `R56Audit.theorem_1_1_unfolded` | Every A>0, every n≥1, one c_A>0; iid uniform points; continuous anchored rectangles; all sample-dependent colorings; failure ≤ exp(-An) |
| Corollary 1.2, lower bound | `R56Audit.corollary_1_2_lower` | Deterministic lower bound; the cited upper bound is not formalized |
| Lemma 2.1 | `R56Audit.vertical_comparison` | Vertical oscillation comparison |
| Fact 2.2 | `R56Audit.fact_2_2_general` | Independent symmetric real random variables, common second moment, integrable fourth powers and fourth-moment bound |
| Lemma 2.3 | `R56Audit.local_gain` | Midpoint/symmetric-jump local gain for arbitrary integer bases b≥3 |
| Lemma 2.4 | `R56Audit.lemma_2_4_digits` | Conditional drift for the full continuous-height potential, almost surely |
| Lemma 2.5(i) | `R56Audit.lemma_2_5_i` | Nonheavy mass bound |
| Lemma 2.5(ii) | `R56Audit.lemma_2_5_ii`, `R56Audit.lemma_2_5_ii_all` | Single/all-transition occupancy bounds for integer b≥3; no independence between transitions required |
| Lemma 2.6 | `R56Audit.lemma_2_6_digits` | Centered fluctuation bound with the digit filtration |
| Proposition 2.7 | `R56Audit.proposition_2_7` | All integer b≥3, h≥1, b^(h−1)≤n; exact constants 64, 48, 2048 |
| Parameters / all n | `R56Audit.theorem_1_1` and `Parameters.lean` | Choice of base and scale; completion of all n≥1 |
| Fact A.1 | `R56Audit.fact_A_1` | Conditional bounded differences for arbitrary measurable spaces, independent inputs, measurable integrable function, coordinate bound c>0 |
| Successive conditioning | `R56Audit.integral_prod_le_of_condExp_le`, `R56Audit.roadmap_digits` | Product bound and Markov route used by the final proof |

## Definitions and bridges

- `F` is the actual anchored-rectangle color sum. `Zpot` takes suprema minus infima over entire half-open vertical intervals; it is not a finite-probe substitute. `scripts/SubmissionStatements.lean` independently unfolds this definition.
- The full potential is identified with the step representation `Zstep` on nonnegative coordinates by proved lemmas. Null grid-boundary events are handled almost surely.
- `digitSigma` describes the digits in the paper. The equivalent interval-index implementation `stageSigma` is connected by `condExp_digitSigma`; the final route requires this bridge.
- The unfolded main theorem uses ordinary product Lebesgue measure restricted to the unit square and actual rectangle sums. It has no project-defined predicate or unproved probability hypothesis hiding in its statement.
- Fourth-power integrability in Fact 2.2 expresses the finite-moment convention explicitly. Lean's integral on a nonintegrable function cannot be used as a substitute for a finite fourth moment.
- Fact A.1 uses a common measurable codomain for the independent coordinates and assumes integrability of the function, as required by the conditional-expectation formulation.

## Verification and remaining scope

The source-derived gates check 266 theorem statements and 80 definition examples covering 83 names, plus seven other examples. Independent gates additionally unfold the main theorem and potential and check Proposition 2.7 and both general probability tools. Mutation checks reject 52 deliberately altered statements/definitions and accept three controls.

`scripts/SubmissionClosure.lean` traverses all proof constants without stopping at module boundaries. Both primary conclusions must use the local gain, general moment and bounded-difference facts, digit bridge, drift, occupancy, fluctuation, and simultaneous proposition. They must not reach the old `Oscillation.Direct`, `Oscillation.R56`, or `Oscillation.R65` routes, `Oscillation.paper_lower_bound`, or `Oscillation.gridPotential`.

The old finite-probe/even-base proof remains under `Oscillation` as a comparison. Its legacy completion and route checks remain enabled, but it is not the evidence for the new manuscript-route claim. Eight older foundational modules supply proved distribution, averaging, interval-index, digit-law, and null-event facts.

This correspondence is at the level of mathematical statements and proof architecture. For example, the fourth-moment calculation uses induction, and bounded differences uses iterated product integration. It is not a certification of every sentence in the PDF. The upper bound, Section 3 discussion, citations, priority claims, figures, and AI-methodology narrative are not proved by Lean.
