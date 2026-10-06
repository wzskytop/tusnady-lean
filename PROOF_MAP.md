# r65 correspondence

| Manuscript item | Lean declaration or file | Coverage |
|---|---|---|
| Theorem 1.1 | `Main.paper_lower_bound` → `R65.paper_lower_bound` → `Direct.paper_lower_bound` | All A>0, all n≥1, one c_A>0, simultaneous sample-dependent colorings, failure at most exp(-An); no unproved probabilistic premises |
| Corollary 1.2, lower-bound direction | `Main.planar_tusnady_lower_bound` | Deterministic Ω(log^(3/2)n); the cited upper bound is not formalized |
| Lemma 2.1, vertical comparison | `midpoint_range_comparison` in `R17LocalFacts.lean` | Algebraic comparison of finite block extrema; independent checked fact, not in the main proof's local-gain route |
| Fact 2.2, symmetric sums | `abs_mean_of_fourth_three` in `R17LocalFacts.lean`, `Rademacher.lean` | Finite-law moment consequence and the signs needed by the actual local proof; not the full arbitrary real-random-variable statement |
| Lemma 2.3, local gain | `AveragedComparison.lean`, `AveragedLocal.lean`, `DriftAssembly.lean` | Existing average-before-maximum/representative proof for even bases; same 1/4 constant, not a literal translation of the midpoint/symmetric-jump proof |
| Lemma 2.4, conditional gain | `stage_finite_drift`, `stage_exp_gain` | Actual finite-probe process and independent conditional digits; summation of local gain |
| Lemma 2.5(i), nonheavy mass | `paperGoodTransition_mass` | Good transitions give the mass bound; `allGood_subset_good` weakens it to the aggregate threshold needed by the compensated-loss proof |
| Lemma 2.5(ii), single transition | `R65.bad_transition_bound` | Exact (48/b)^(n/2), every integer b≥3; nontrivial cases use the union over heavy-region choices |
| Lemma 2.5(ii), all transitions | `R65.all_good_compl_bound`, `allGood_compl_bound` | Exact h*(48/b)^(n/2), b≥3; no independence between transitions assumed |
| Lemma 2.6, fluctuations | `CenteredFluctuations.stage_centered_lower_tail` | Actual centered sum of the finite-probe process conditional on fixed vertical labels; independently checked |
| Main route's fluctuation estimate | `DirectAccumulation.point_exp_loss`, `DirectScale.loss_tail` | Unconditional compensated-loss route on actual point samples, not an identification of its process with the PDF's continuous-height Z |
| Proposition 2.7, equation (14) | `R65.simultaneous_bound` → `Direct.proposition_2_7` | Exact threshold and both failure terms; interface requires even b≥4, h≥1, n≥1, M≤n |
| Parameters, all n | `DirectParameters.paper_lower_bound`, `direct_rates`, `failure_sum`, `absorb_all_stages` | Chooses a sufficiently large power-of-two base, maximal scale hM/b^5≤n, and covers M>n via imbalance ≥1 |
| Fact A.1 | `finAvg_exp_boundedDifferences` and conditional finite-law machinery | The finite independent-digit case used by the proof; not an assertion of the fully general appendix interface |

## Definitions and quantifiers

- `unifPts n` is the actual iid uniform law on the unit square. The final statement uses genuine continuous anchored rectangles and a finite set of n distinct points.
- The internal potential uses finite vertical grid probes. Boundary conventions agree almost surely under continuous sampling. No equality with the continuous-height potential is claimed.
- `allGood` is the intersection of all per-transition occupancy events. The geometric failure is counted once; only the fluctuation event is union-bounded over colorings.
- The final explicit completion gate expands the probability event and quantifies over every coloring of the sampled point set. It proves a strict inequality, which implies the manuscript's non-strict lower bound.
- The conservative power-of-two base is sufficient for the existence theorem. It does not prove Proposition 2.7 for all odd bases or reproduce the broadest local interfaces in the manuscript.

## Dependency requirements

`scripts/DirectDependencies.lean` traverses actual proof terms, not just imports. The main theorem must use `bucket_bad_transition_bound`, `paper_bad_transition_bound`, `allGood_compl_bound`, `allGood_subset_good`, `union_simultaneous_bound`, `failure_sum`, `absorb_all_stages`, `averaged_child_difference_gain`, and the compensated fluctuation bound. It must not use the r17 sequential-crowding reduction, the earlier half-of-stages Markov route, or the old global Laplace route. Retained historical modules are compiled and audited, but their presence is not evidence that their route is used.
