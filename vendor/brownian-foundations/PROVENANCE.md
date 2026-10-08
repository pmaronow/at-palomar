# Canonical Brownian foundations provenance

BrownianMotion upstream: https://github.com/RemyDegenne/brownian-motion
Commit: `0d5b6eb928e616d3b1f774ad7d233c167d9f42c9`
KolmogorovExtension4 upstream: https://github.com/RemyDegenne/kolmogorov_extension4
Commit: `7d76e184c3d2138a2741baf923b57e9a01b9cf25`
Both licensed Apache 2.0; preserve the accompanying license files.

Only the clean 30-module dependency closure of
`BrownianMotion.Gaussian.BrownianMotion` is included. Unrelated upstream
stochastic integral and iterated logarithm files with proof placeholders
are excluded. This closure has been compiled on Lean/mathlib v4.34.1.

Compatibility changes are recorded completely in compatibility.patch:
remove two declarations already present in current mathlib; make chaining
supremum index bounds explicit; update subtype and measurability inference;
make the current HasGaussianLaw constructor fields explicit; add an explicit
Polish-space import. The chaining scale-change proof is rewritten as the
same triangle inequality plus the three explicit supremum bounds.

The actual Brownian measure is constructed through Kolmogorov extension
from the Gaussian projective family. Its coordinate process is modified
using the proved Kolmogorov–Chentsov theorem to obtain continuous paths.
Thus IsBrownianReal is established for a concrete measure and process, not
assumed as a field in a model structure.

Kernel axiom audit of isBrownianReal_brownian, gaussianLimit projective
limit, continuous_brownian and continuous-map measurability reports only
propext, Classical.choice and Quot.sound.
