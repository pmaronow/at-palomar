# Coverage of arXiv:2604.11921v2

The Comparator configuration selects Theorem 1.1 and Proposition 1.2. The remaining numbered results and supporting lemmas are included in the full development.

All fifteen numbered results have closed Lean proofs about the actual SK model, weak Parisi PDE solution, and constructed Brownian state. The main theorem is also proved along the paper's actual PDE and variational argument.

`Paper/NumberedResults.lean` gives an unparameterized, universally quantified `Statement_* : Prop` for every numbered result. Each completed statement has a closed `result_* : Statement_*`. `Paper/NumberedResultsAudit.lean` type-checks those pairings and rejects every transitive axiom except `propext`, `Classical.choice`, and `Quot.sound`.

Local verification under Lean 4.35.0-rc2 and the pinned Mathlib checked 2,309 public project declarations, including 1,931 public theorems, and every numbered proof against its exact target. All 665 Lean files compiled: 198 project files, 465 vendored files, and the Challenge/Solution pair. `results.json` records the local verification scope and commands. The verification tools regenerate reports in `work/`, and GitHub CI repeats the checks for the pushed source. Lake dependency jobs are not a declaration count.

## Numbered statements

| Paper result | Status | Actual checked conclusion |
|---|---|---|
| Theorem 1.1 | Proved | The expected finite SK free energy converges to the concrete Gaussian RS formula throughout the closed AT region, including equality. |
| Proposition 1.2 | Proved | The exact Gaussian AT boundary is the positive, strictly increasing C∞ graph on β>1, together with (1,0), with the stated right endpoint limit. |
| Proposition 2.1 | Proved | Original admissible weak-class existence and uniqueness, all positive spatial orders jointly continuous and bounded, all spatial orders with bounded measurable weak time derivatives, and sharp gradient/Hessian bounds. |
| Theorem 2.2 | Proved | The physical finite SK limit is the infimum over all probability measures on [0,1] of the actual weak-PDE functional. |
| Proposition 2.3 | Proved | Minimizers of the actual PDE functional are exactly the measures whose actual topological support lies in the argmin of their selected state-based G. Actual first variation, mixing convexity, HJB envelope, and optimal-gradient martingale are discharged. |
| Proposition 3.1 | Proved | The general PDE selector at δq is the explicit soft/hard potential, including gradient/Hessian and interface values; its actual selected strong state satisfies both drift equations and has the stated Gaussian law at q. |
| Proposition 4.1 | Proved | The actual selected PDE-gradient second moment satisfies the exact quantitative left bound (1−α)(q−t), including the equality AT boundary. |
| Proposition 5.1 | Proved | Actual magnetization changes are limits in probability of genuine Brownian left sums with coefficient β(1−m²); actual second moments have the stated derivative, initial fixed-point value, and literal one-sided endpoint derivatives. |
| Proposition 5.2 | Proved | The actual selected second moment is at most t in the small-complement regime; no AT premise is required. |
| Proposition 5.3 | Proved | The actual positive-field fixed point and large-complement regime imply h<β²q; no AT premise is required. |
| Proposition 5.4 | Proved | The actual selected process has the explicit normalized cosh-Gaussian conditional transition law for every bounded measurable observable, including elapsed time zero. The chosen Markov kernel has the pointwise formula at every starting x. |
| Proposition 5.5 | Proved | The actual selected second moment is at most t under the small-field hypothesis and is strictly below t after q. |
| Proposition 5.6 | Proved | The actual selected moment has the full post-q bound under the physical AT hypotheses, with both regimes discharged. |
| Proposition 6.1 | Proved | The genuine selected observable Gδq has its global minimum at q. Its minimum is also proved strict away from q. |
| Remark 6.2 | Proved | The actual Dirac q is a minimizer and every actual PDE-functional minimizer equals it, from the strict actual Gδq minimum and the proved mixing first variation. No general strict-convexity premise is needed. |

The one-to-one names are `Paper.Numbered.Statement_1_1` and `Paper.Numbered.result_1_1`, with the same convention for all fifteen numbers. The machine-readable map, source lines, supporting displays, precise scope, and remaining work are in `results.json`.

## Mathematical scope and representations

The finite Hamiltonian uses one independent standard normal coupling for each unordered pair i<j, the normalization β/√N, and the paper's magnetic field sign. The audited physical bridges prove that the imported finite-step Parisi theory describes this model, including the Gaussian common-noise correction and energy/field sign changes.

The Parisi functional uses the constructed arbitrary-measure weak potential. Its infimum ranges over actual Borel probability measures on [0,1]. Genuine finite atomic probability laws approximate every measure with an L¹ CDF mesh bound; finite Cole–Hopf recursions, global mild uniqueness and convergence, exact correction integrals, and the finite-step Talagrand theorem establish the PDE-form formula. Defining the desired infimum to equal a backend value would not suffice; their equality is a theorem here.

Weak potentials are continuous on the closed strip and have a bounded measurable distributional spatial gradient in the stated admissible class. Literal potential uniqueness is on this strip, while measurable gradient representatives are unique almost everywhere. Time derivatives are weak derivatives: atomic CDFs can jump, so the project does not assert false global classical time differentiability. The stated C∞ regularity is spatial and jointly continuous for every positive spatial order.

The general strong state is a genuine causal Picard construction driven by the canonical continuous Brownian process in its natural filtration. This is a concrete realization. No formal transport to a completed right-continuous augmented filtration is asserted. Its analytic and stochastic prerequisites are derived from the actual PDE solution. At δq it is identified path by path with the explicit Dirac process. All numbered moment and G statements use this actual general selector, rather than an abstract family with assumed laws or moment identities.

Conditioning on Xq=x is represented by an explicit normalized Markov kernel and its conditional-expectation identity. This gives a chosen version at every x without treating a zero-probability singleton as an event on which one can divide. Variance zero is handled through the identity heat operator, not a nonexistent Gaussian density.

## Supporting displays and background

`results.json` preserves the full original supporting inventory and adds the general PDE, actual SDE, measure approximation, physical Parisi bridge, bounded-measurable heat regularization, and general functional convexity. Gaussian integration by parts, Poincaré, conditional Gaussian composition, tanh/sech calculus, the symmetrized-weight double integral and its absolute integrability, exponential fourth-moment decay, fixed-point existence and uniqueness, and every appendix curve derivative/inverse/endpoint step have concrete proofs.

The literal before-q conditional-expectation representation, conditional Gaussian Poincaré inequality, total conditional-variance decomposition, actual post-q moment integral identity, and exact integrated exponential moment envelope are separately proved and audited. The general actual optimal-gradient process is also a genuine Mathlib martingale. For every physical starting time and spatial point, the actual PDE potential is the supremum of explicitly integrated fresh-Brownian control objectives, attained by its genuine restarted feedback, including the terminal starting time. The actual Dirac potential has classical C¹ time and C² spatial regularity off q, with physical within-strip derivatives at the endpoints. All 58 substantive supporting inventory entries have concrete proofs.

The introduction's historical literature-survey claims about zero-field RS/RSB phases, replica symmetry breaking when α>1, earlier sufficient RS regions, and mixed-p-spin counterexamples are retained as cited background. They are not claimed as proved results of this development. The paper's fifteen numbered statements and substantive displayed proof ingredients have separate coverage entries, so completion of a numbered target cannot silently erase an unproved supporting assertion.

The vendored theorem sources, exact revisions, compatibility edits, standard-axiom audits, and removed off-path unfinished declarations are recorded in the provenance files. Imported names alone do not establish trust: the physical target statements and their full transitive proof closures are checked by Lean's kernel.
