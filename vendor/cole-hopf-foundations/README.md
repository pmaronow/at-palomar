# Cole–Hopf and Gaussian heat foundations

This source-only dependency closure comes from or4nge19/SpinGlass, commit
dc1d3820af6e443c09bd1177ec3e409cf0640d5c. Original Apache-2.0 licenses and
copyright notices are retained. Per-file source/adaptation hashes are in
PROVENANCE.json. Fifteen upstream modules and one local kernel audit are used.

The source declarations are nested in ColeHopfFoundation to avoid collisions
with independently sourced RSAT Gaussian lemmas. Inner namespaces and theorem
statements are retained. Root-scoped notation and original mathlib namespace
opens are explicit. Compatibility changes use the current probability-map
instance and allow modern conversion elaboration to close redundant goals.

Lean4.34.1/mathlibd13f23b7 compiled the actual Gaussian heat equation,
spatial derivatives, one-level Cole–Hopf PDE, Lipschitz preservation and
sup-norm contraction. Common.ColeHopfAudit rejects any transitive axiom beyond
propext, Classical.choice and Quot.sound. The audit passed with those three
standard axioms. This is actual single-level PDE calculus; arbitrary-measure
weak Parisi PDE existence and uniqueness remain separate results.
