# Replica symmetry up to the de Almeida–Thouless line

Lean 4 formalization of Patrick Lopatto's [Replica symmetry up to the de Almeida–Thouless line in the Sherrington–Kirkpatrick model](https://arxiv.org/abs/2604.11921v2).

P. M. Aronow and Patrick Lopatto are jointly responsible for the formalization; Lopatto is responsible for the paper. Sol 6.1 autoformalized the original development. Codex prepared the Palomar interface and compiler compatibility changes. Authorship, automation, review, sources, and mathematical scope are recorded in `formalization.yaml`.

## Results

`Challenge.lean` independently states two results using Mathlib's concrete Gaussian expectations and the finite SK Hamiltonian. `Solution.lean` supplies their proofs, and `comparator.json` selects:

- `PalomarAT.replicaSymmetry` (Theorem 1.1): for beta > 0, h > 0, every overlap fixed point q in [0,1] with AT parameter at most one, the expected finite SK free energy converges to the replica-symmetric Gaussian formula. Equality at the AT line is included.
- `PalomarAT.smoothATBoundary` (Proposition 1.2): the positive-field AT boundary is a positive, strictly increasing smooth graph on beta > 1, tending to zero as beta approaches 1 from the right, together with (1,0).

The main Solution proof uses the vendored quantitative strict-AT theorem, a proved physical-model bridge, and boundary approximation. The repository also contains a separate proof through the paper's Parisi PDE and variational argument. `Paper/NumberedResults.lean`, `COVERAGE.md`, and `results.json` describe fifteen numbered statements and their supporting development. The Comparator configuration selects the two headline results.

## Verification

The project pins Lean 4.35.0-rc2 and Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`, including the dependency manifest. Install the pinned toolchain with elan and, on Linux, install `bwrap`. Run from the repository root:

```sh
python3 -m pip install PyYAML==6.0.3
lake exe cache get
python3 tools/submission_check.py
lake build Paper Challenge Solution
python3 tools/audit.py --report work/final-audit-report.json
bash tools/verify_comparator.sh
```

The two intentional theorem `sorry` holes in `Challenge.lean` state the claims to be proved. The Solution proofs have no proof holes. `audit.py` checks every public project declaration's transitive axioms, scans project and vendored sources, and typechecks each numbered proof against its exact target. It permits only `propext`, `Classical.choice`, and `Quot.sound`.

`verify_comparator.sh` compares Challenge and Solution using Lean, NanoDa, and con-ron. Local build, audit, and Comparator checks passed for these Lean sources. `results.json` records their scope and reproduction commands. The [GitHub workflow](https://github.com/pmaronow/at-palomar/actions/workflows/palomar.yml) repeats these checks. Palomar performs its own mechanical and editorial review. No human mathematical peer review is asserted.

## Mathematical scope and provenance

The finite Hamiltonian has independent standard normal couplings for unordered pairs i<j, normalization beta/sqrt(n), and the paper's uniform-field sign. Expectations are Gaussian integrals, and the free-energy claim concerns the finite expected log partition function and its limit.

The AT graph is smooth on beta > 1 and has the stated right limit at beta = 1. General process results use a canonical Brownian realization and its natural filtration. No formal transport to a completed right-continuous augmented filtration is asserted. HJB controls are bounded continuous adapted controls with magnitude at most one. Time derivatives for arbitrary Parisi measures are weak; classical Dirac time regularity excludes the interface q. The introduction's zero-field phase and above-AT replica-symmetry-breaking claims are cited background. `COVERAGE.md` gives the full scope of the supporting development.

`vendor/` contains proof foundations for the Parisi formula, strict-AT theorem, Brownian construction, stochastic calculus, and Cole–Hopf calculus. Their provenance files record exact upstream revisions and adaptations. `compatibility/` records the subsequent module-system and compiler changes.

## License

Original Lean code and original project documentation are MIT licensed. Vendored sources retain their own Apache-2.0 licenses and notices. The cited manuscript has its own distribution terms and is outside the software license.
