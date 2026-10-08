module

public import Paper.ParisiPDEFormula

@[expose] public section

/-!
Theorem 2.2 kernel audit. Compilation fails if any audited statement depends
transitively on an axiom other than Lean's standard extensionality, choice,
and quotient axioms. This checks the physical model theorem together with
the actual finite-law and arbitrary-measure PDE identification bridges.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``Paper.physicalParisiFormula,
    ``Paper.parisiPDEValue_eq_finiteStep,
    ``Paper.parisiPDEFunctional_scheme,
    ``Paper.tendsto_parisiFiniteFunctional_grid,
    ``Paper.parisiSchemeGradient_mild,
    ``Paper.parisiFiniteGradient_mild,
    ``Paper.parisiCDF_grid_norm_integral_le] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms Paper.physicalParisiFormula
#print axioms Paper.parisiPDEValue_eq_finiteStep
#print axioms Paper.parisiPDEFunctional_scheme
#print axioms Paper.tendsto_parisiFiniteFunctional_grid

