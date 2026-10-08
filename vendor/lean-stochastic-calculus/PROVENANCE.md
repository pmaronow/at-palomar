# StochasticCalculus provenance

Upstream: https://github.com/savarin/lean-stochastic-calculus
Commit: `bde839683ba3cf1bf149355a40e9de9522babe92`
Author: Ezzeri Esa. License: Apache 2.0 (see LICENSE).

Only the 57-module dependency closure of `StochasticCalculus.GirsanovTheorem`
is included. Upstream BlackScholesChallenge, which intentionally contains a
proof placeholder, is excluded.

Upstream uses Lean/mathlib v4.35.0-rc3. This copy compiles with the enclosing
project's Lean/mathlib v4.34.1 pin. The initial compatibility edit removes
`Lean.Elab.Recall` imports and redundant `recall` signature checks (a newer
elaborator feature). That initial edit leaves mathematical definitions and proof bodies unchanged.

A further generic-sample-space port is recorded completely in generality.patch.
Seventeen Ito-related source files remove inherited normed/Gaussian sample-space
assumptions and instead require an arbitrary measurable probability space.
The scalar expectation map used by ItoConstruction is recreated by the same
lpPairing/constant-one formula, without Gaussian restrictions. All proof bodies
remain checked; the entire 57-module closure compiles, and the widened Ito
martingale/continuous-modification/quadratic-variation APIs have been inspected.
This permits genuine use on the canonical Brownian projective-limit space.

Verified by actual compilation and `#print axioms` for the natural Ito
integral, the general Ito formula, the predictable Girsanov theorem, and the
Girsanov probability normalization. Their dependencies contain only
`propext`, `Classical.choice`, and `Quot.sound`.

Input-contract audit: local martingales are genuinely defined through
Mathlib localizing sequences of martingales, quadratic variations through
limits in probability of uniform partition sums, and Girsanov assumes
Novikov, predictability, and proved cross-variation data. These hypotheses
do not assert the transformed Brownian conclusion. Their concrete
instantiation for the paper remains separate formalization work.
