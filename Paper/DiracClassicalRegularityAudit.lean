module

public import Paper.DiracClassicalRegularity

@[expose] public section

/-! Reject nonstandard axioms in the literal off-interface classical regularity. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``Paper.hasDerivAt_parisiPotential_dirac_time_soft,
    ``Paper.hasDerivAt_parisiPotential_dirac_time_hard,
    ``Paper.hasDerivWithinAt_parisiPotential_dirac_time_soft,
    ``Paper.hasDerivWithinAt_parisiPotential_dirac_time_hard,
    ``Paper.parisiDirac_classical_regular] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms Paper.parisiDirac_classical_regular
