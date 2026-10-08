# Spin glass foundations dependency slice

This package contains the source dependency closure for the exact-covariance SK
Parisi formula and the quantitative strict Almeida–Thouless theorem. Sources,
exact Git commits, licenses, original hashes and adaptation hashes are recorded
in `PROVENANCE.json`. Both upstream repositories use Apache-2.0; their licenses
are included separately. File/module namespaces are retained to preserve theorem
statements. Source files modified locally carry an adaptation notice.

The public Parisi theorem is `SpinGlass.Targets.parisi_formula`. Its conclusion
is actual convergence of quenched finite SK free entropy to the infimum of the
finite-step Parisi functional, for every positive beta and every real field.
The arbitrary probability-measure weak PDE and its variational support criterion
are not asserted by this theorem. The discrete/general-measure value bridge is
an additional mathematical task for the paper.

The strict-AT theorem is `SpinGlass.AT.quantitative_strictAT_on_compact` or its
concrete wrapper `quantitative_strictAT`. It constructs the uniform bounds from
compactness, positive beta and field, and the actual strict AT inequality. In
particular, the replica symmetric pressure minus finite SK free entropy lies
between zero and a constant divided by system size. The main theorem is not a
conditional restatement of this conclusion. Gaussian disorder assumptions are
actual distribution/independence conditions and must be instantiated for the
paper's finite product Gaussian model.

The canonical fixed point is the infimum of the interval-valued fixed points.
Its uniqueness for positive field is a proved imported result; arbitrary q must
be identified with it through `SpinGlass.AT.eq_rsQ_of_isRSFixedPoint`.

Upstream SK covariance is N beta² R²/2, including a diagonal common Gaussian
shift relative to the paper's unordered i<j convention. Exact equality of
expected free entropy requires a Gaussian model/covariance comparison or
explicit symmetrization and removal of the mean-zero diagonal shift. The
paper's physical model is defined separately and cannot be silently redefined
as the imported model.

Three unfinished legacy declarations in `Targets.Milestones` have been removed
because no imported theorem uses them. Native decision tactics on finite cavity
combinatorics have been replaced with kernel `decide`. The critical axiom audit
in `SpinGlassFoundations/Audit.lean` permits only `propext`, `Classical.choice`
and `Quot.sound`; it rejects placeholder axioms, native decision oracles and
custom assumptions in every dependency of the main imported theorems.

Validation status is recorded in `PROVENANCE.json` and the project build log;
existence of an upstream repository alone is not treated as a successful build.
