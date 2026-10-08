# Lean 4.35.0-rc2 compatibility changes

The vendored libraries retain their own upstream provenance and adaptation records. These two patches document subsequent changes to the original development for the pinned compiler and Mathlib release:

- `module-system.patch` adds module headers, public imports, exposed public sections, and helper visibility needed by signatures, definitions, and imported automation. It preserves mathematical statements, definition values, and proof bodies.
- `compiler-port.patch`, applied after the module patch, contains four elaboration and proof compatibility repairs: an explicit integrability composition in `DiracSoftMoment`; direct use of `Real.artanh_pos` in `KSInequality`; the existing pressure-trace identity and `linarith` in `SmartPath.Interpolation`; and public List sorting recurrences in `ParisiCascadeSorting`.

The compiler repairs preserve theorem statements and hypotheses and introduce no axioms or proof holes. All 665 Lean files compiled under the pinned toolchain, and the selected proofs passed the standard-axiom audit and Comparator with Lean, NanoDa, and con-ron. Verification methods and commands are documented in the repository README and `results.json`.
