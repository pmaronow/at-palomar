module

public import Common.Mathlib.Probability.Distributions.Gaussian.ColeHopf

@[expose] public section

/-! Transitive kernel audit for the actual Gaussian heat and Cole–Hopf PDE theorems. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ColeHopfFoundation.ProbabilityTheory.hasDerivAt_coleHopf_var',
    ``ColeHopfFoundation.ProbabilityTheory.hasDerivAt_coleHopf,
    ``ColeHopfFoundation.ProbabilityTheory.abs_coleHopf_sub_le_of_lipschitz,
    ``ColeHopfFoundation.ProbabilityTheory.abs_coleHopf_sub_le_of_sup,
    ``ColeHopfFoundation.ProbabilityTheory.hasDerivWithinAt_integral_comp_add_gaussianReal_var_zero] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms ColeHopfFoundation.ProbabilityTheory.hasDerivAt_coleHopf_var'
#print axioms ColeHopfFoundation.ProbabilityTheory.hasDerivAt_coleHopf
#print axioms ColeHopfFoundation.ProbabilityTheory.abs_coleHopf_sub_le_of_lipschitz
